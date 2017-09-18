//! Shader Interface

use {std, spv, spvdefs};
use container_ext::*;
use module_loader::*;
use collector::*;
use spvdefs::Id;
use spvdefs::Decoration as DecorationIndex;
use std::collections::BTreeMap;
use std::borrow::*;

#[derive(Clone, Debug)]
enum Descriptor<'n>
{
    Empty, UniformBuffer(&'n spv::Typedef<'n>), SampledImage(&'n spv::Typedef<'n>)
}
impl<'n> HasPlaceholder for Descriptor<'n> { fn placeholder() -> Self { Descriptor::Empty } }
struct DescriptorSet<'n>(BTreeMap<u32, AutosizeVec<Descriptor<'n>>>);
struct DescriptorSetSlots<'n>(BTreeMap<u32, DescriptorSet<'n>>);
impl<'n> DescriptorSetSlots<'n>
{
    fn new() -> Self { DescriptorSetSlots(BTreeMap::new()) }
    fn binding(&self, binding: u32) -> Option<&DescriptorSet<'n>> { self.0.get(&binding) }
    fn binding_entry(&mut self, binding: u32) -> &mut DescriptorSet<'n>
    {
        self.0.entry(binding).or_insert_with(DescriptorSet::new)
    }
    fn iter(&self) -> std::collections::btree_map::Iter<u32, DescriptorSet<'n>> { self.0.iter() }
}
impl<'n> DescriptorSet<'n>
{
    fn new() -> Self { DescriptorSet(BTreeMap::new()) }
    fn set_index(&self, index: u32) -> Option<&[Descriptor<'n>]> { self.0.get(&index).map(|x| &x[..]) }
    fn set_entry(&mut self, index: u32) -> &mut AutosizeVec<Descriptor<'n>>
    {
        self.0.entry(index).or_insert_with(AutosizeVec::new)
    }
    fn iter(&self) -> std::collections::btree_map::Iter<u32, AutosizeVec<Descriptor<'n>>> { self.0.iter() }
}
#[derive(Clone, Debug)]
struct SpirvVariableRef<'n> { path: Vec<Cow<'n, str>>, _type: &'n spv::Typedef<'n> }
impl<'n> std::fmt::Display for SpirvVariableRef<'n>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        write!(fmt, "{}: {:?}", self.path.join("::"), self._type)
    }
}
#[derive(Debug)]
struct SpirvConstantVariable<'n> { name: Cow<'n, str>, _type: &'n spv::Typedef<'n>, value: Box<ConstantValue> }
impl<'n> std::fmt::Display for SpirvConstantVariable<'n>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        write!(fmt, "{}: {:?} = {:?}", self.name, self._type, self.value)
    }
}

pub struct ShaderInterface<'m>
{
    exec_model: spvdefs::ExecutionModel, inputs: BTreeMap<Id, Vec<SpirvVariableRef<'m>>>, builtins: BTreeMap<spvdefs::BuiltIn, Vec<SpirvVariableRef<'m>>>,
    outputs: BTreeMap<Id, Vec<SpirvVariableRef<'m>>>, descriptors: DescriptorSetSlots<'m>,
    input_attachments: BTreeMap<u32, Vec<SpirvVariableRef<'m>>>,
    spec_constants: BTreeMap<u32, SpirvConstantVariable<'m>>
}

impl<'m> ShaderInterface<'m>
{
    pub fn make(module: &'m SpirvModule, collected: &'m CollectedData<'m>, er: &mut ErrorReporter) -> Result<Self, SpirvReadError>
    {
        // Getting all input/output/descripted variables or pointers
        let mut exec_model = SetOnce::new();
        let (mut inputs, mut outputs, mut descriptors, mut input_attachments) = (Vec::new(), Vec::new(), DescriptorSetSlots::new(), BTreeMap::new());
        for op in module.operations.iter()
        {
            struct DecoratedVariableRef<'s>
            {
                name: Vec<Cow<'s, str>>, _type: &'s spv::Typedef<'s>, decorations: Option<Cow<'s, DecorationList>>
            }
            fn enumerate_structure_elements<'n>(id: Id, parent_name: &'n str, member: &'n [spv::StructureElement<'n>],
                decorations: &'n DecorationMaps, sink: &mut Vec<DecoratedVariableRef<'n>>)
            {
                let base_decos = decorations.toplevel.get(&id);
                let vars = member.iter().enumerate().map(|(n, e)|
                {
                    let ref member_decos = decorations.member.get(&id).unwrap()[n];
                    let decos = match base_decos
                    {
                        Some(bd) => { let mut decos = bd.clone(); for (&id, d) in member_decos.iter() { decos.register(id, d.clone()); } Cow::Owned(decos) },
                        _ => Cow::Borrowed(member_decos)
                    };
                    DecoratedVariableRef
                    {
                        name: vec![Cow::Borrowed(parent_name), e.name.as_ref().map(|x| Cow::Borrowed(x as &str)).unwrap_or(Cow::Borrowed("<anon>"))],
                        _type: &e._type, decorations: Some(decos)
                    }
                });
                for v in vars { sink.push(v); }
            }
            match op
            {
                &Operation::EntryPoint { model, .. } => exec_model.set(model),
                &Operation::Variable { storage, result_type, result: id, .. } => match storage
                {
                    spvdefs::StorageClass::Input => inputs.push(DecoratedVariableRef
                    {
                        name: vec![module.names.toplevel.get(&id).map(|x| Cow::from(x as &str)).unwrap_or(Cow::Borrowed("<anon>"))],
                        _type: collected.types.get(result_type).unwrap(),
                        decorations: module.decorations.toplevel.get(&id).map(Cow::Borrowed)
                    }),
                    spvdefs::StorageClass::Output => outputs.push(DecoratedVariableRef
                    {
                        name: vec![module.names.toplevel.get(&id).map(|x| Cow::from(x as &str)).unwrap_or(Cow::Borrowed("<anon>"))],
                        _type: collected.types.get(result_type).unwrap(),
                        decorations: module.decorations.toplevel.get(&id).map(Cow::Borrowed)
                    }),
                    spvdefs::StorageClass::Uniform | spvdefs::StorageClass::UniformConstant => if let Some(decos) = module.decorations.toplevel.get(&id)
                    {
                        let t = collected.types.get(result_type).unwrap();
                        match t.dereference()
                        {
                            ia @ &spv::Typedef { def: spv::Type::Image { dim: spvdefs::Dim::SubpassData, .. }, .. } =>
                            {
                                if let Some(&Decoration::InputAttachmentIndex(iax)) = decos.get(DecorationIndex::InputAttachmentIndex)
                                {
                                    input_attachments.entry(iax).or_insert_with(Vec::new).push(SpirvVariableRef
                                    {
                                        path: vec![Cow::Borrowed(module.names.toplevel.get(&id).unwrap())],
                                        _type: ia
                                    });
                                }
                                else { er.report("Required `input_attachment_index` decoration for SubpassData"); }
                            },
                            td => if let Some(&Decoration::Binding(binding)) = decos.get(DecorationIndex::Binding)
                            {
                                if let Some(&Decoration::DescriptorSet(set)) = decos.get(DecorationIndex::DescriptorSet)
                                {
                                    let array_index = if let Some(&Decoration::Index(x)) = decos.get(DecorationIndex::Index) { x } else { 0 } as usize;
                                    let desc = match td
                                    {
                                        &spv::Typedef { def: spv::Type::Structure(_), .. } => Descriptor::UniformBuffer(td),
                                        &spv::Typedef { def: spv::Type::SampledImage(ref si), .. } => Descriptor::SampledImage(si),
                                        _ => Descriptor::UniformBuffer(td)
                                    };
                                    descriptors.binding_entry(binding).set_entry(set).set(array_index, desc);
                                }
                                else { er.report("Required `set` decoration for Uniform"); }
                            }
                            else { er.report("Required `binding` decoration for Uniform"); }
                        }
                    }
                    else
                    {
                        println!("Warn: Undecorated Uniform/UniformConstant Variable: {}", id);   
                    },
                    _ => (/* otherwise */)
                },
                &Operation::TypePointer { storage: spvdefs::StorageClass::Output, _type, .. } =>
                    if let Some(&spv::Typedef { name: Some(ref parent_name), def: spv::Type::Structure(ref m) }) = collected.types.get(_type)
                    {
                        enumerate_structure_elements(_type, parent_name, m, &module.decorations, &mut outputs);
                    },
                &Operation::TypePointer { storage: spvdefs::StorageClass::Input, _type, .. } =>
                    if let Some(&spv::Typedef { name: Some(ref parent_name), def: spv::Type::Structure(ref m) }) = collected.types.get(_type)
                    {
                        enumerate_structure_elements(_type, parent_name, m, &module.decorations, &mut inputs);
                    },
                _ => ()
            }
        }
        let (mut inlocs, mut outlocs, mut builtins) = (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
        for n in inputs.into_iter()
        {
            if let Some(decos) = n.decorations
            {
                if let Some(&Decoration::Location(location)) = decos.get(DecorationIndex::Location)
                {
                    inlocs.entry(location).or_insert_with(Vec::new).push(SpirvVariableRef
                    {
                        path: n.name, _type: n._type.dereference()
                    });
                }
                else if let Some(&Decoration::BuiltIn(bi)) = decos.get(DecorationIndex::BuiltIn)
                {
                    builtins.entry(bi).or_insert_with(Vec::new).push(SpirvVariableRef
                    {
                        path: n.name, _type: n._type.dereference()
                    });
                }
            }
        }
        for n in outputs.into_iter()
        {
            if let Some(decos) = n.decorations
            {
                if let Some(&Decoration::Location(location)) = decos.get(DecorationIndex::Location)
                {
                    outlocs.entry(location).or_insert_with(Vec::new).push(SpirvVariableRef
                    {
                        path: n.name, _type: n._type.dereference()
                    });
                }
                else if let Some(&Decoration::BuiltIn(bi)) = decos.get(DecorationIndex::BuiltIn)
                {
                    builtins.entry(bi).or_insert_with(Vec::new).push(SpirvVariableRef
                    {
                        path: n.name, _type: n._type.dereference()
                    });
                }
            }
        }
        let mut spec_constants = BTreeMap::new();
        for (id, c) in collected.constants.specialized.iter()
        {
            if let Some(decos) = module.decorations.toplevel.get(&id)
            {
                if let Some(&Decoration::SpecId(sid)) = decos.get(DecorationIndex::SpecId)
                {
                    if spec_constants.contains_key(&sid)
                    {
                        println!("Warn: Duplicated specialization constant id {}", sid);
                    }
                    else
                    {
                        let name = module.names.toplevel.get(id).map(|x| Cow::from(x as &str)).unwrap_or(Cow::Borrowed("<anon>"));
                        let _type = collected.types.get(collected.assigned[*id as usize].unwrap().result_type().expect("Could not find a result type"))
                            .expect("Could not find a type");
                        spec_constants.insert(sid, SpirvConstantVariable { name, _type, value: c.clone_inner() });
                    }
                }
                else { println!("Warn: OpSpecConstant** #{} is not decorated by SpecId", id); }
            }
            else { println!("Warn: OpSpecConstant** #{} is not decorated by SpecId", id); }
        }

        Ok(ShaderInterface
        {
            exec_model: exec_model.unwrap(), inputs: inlocs, builtins, outputs: outlocs, descriptors, input_attachments, spec_constants
        })
    }
    pub fn dump(&self)
    {
        println!("## ShaderInterface");
        println!("- Execution Model: {:?}", self.exec_model);
        println!("- Inputs: ");
        for (l, v) in self.inputs.iter().filter(|&(_, v)| !v.is_empty())
        {
            println!("-- Location {}: {:?}", l, v.iter().map(ToString::to_string).collect::<Vec<_>>());
        }
        println!("- Outputs: ");
        for (l, v) in self.outputs.iter().filter(|&(_, v)| !v.is_empty())
        {
            println!("-- Location {}: {:?}", l, v.iter().map(ToString::to_string).collect::<Vec<_>>());
        }
        println!("- Built-Ins: ");
        for (l, v) in self.builtins.iter().filter(|&(_, v)| !v.is_empty())
        {
            println!("-- {:?}: {:?}", l, v.iter().map(ToString::to_string).collect::<Vec<_>>());
        }
        println!("- Descriptors: ");
        for (b, ds) in self.descriptors.iter()
        {
            println!("-- Descriptor Bound #{}", b);
            for (s, da) in ds.iter()
            {
                println!("-- set {}: {:?}", s, da);
            }
        }
        println!("- Input Attachments: ");
        for (x, ia) in self.input_attachments.iter()
        {
            println!("-- #{}: {:?}", x, ia.iter().map(ToString::to_string).collect::<Vec<_>>());
        }
        println!("- Specialized Constants: ");
        for (x, c) in self.spec_constants.iter()
        {
            println!("-- #{}: {}", x, c);
        }
    }
}
