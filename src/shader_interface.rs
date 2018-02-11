//! Shader Interface

use {std, spv, spvdefs};
use container_ext::*;
use module_loader::*;
use collector::*;
use spvdefs::Id;
use std::collections::BTreeMap;
use std::borrow::*;

#[derive(Clone, Debug)]
pub enum Descriptor<'n>
{
    Empty, UniformBuffer(&'n spv::Typedef<'n>), SampledImage(&'n spv::Typedef<'n>)
}
impl<'n> Descriptor<'n>
{
    pub fn uniform_buffer(&self) -> Option<&'n spv::Typedef<'n>>
    {
        if let &Descriptor::UniformBuffer(b) = self { Some(b) } else { None }
    }
}
impl<'n> HasPlaceholder for Descriptor<'n> { fn placeholder() -> Self { Descriptor::Empty } }
pub struct DescriptorSet<'n>(BTreeMap<u32, AutosizeVec<Descriptor<'n>>>);
pub struct DescriptorSetSlots<'n>(BTreeMap<u32, DescriptorSet<'n>>);
impl<'n> DescriptorSetSlots<'n>
{
    fn new() -> Self { DescriptorSetSlots(BTreeMap::new()) }
    pub fn binding(&self, binding: u32) -> Option<&DescriptorSet<'n>> { self.0.get(&binding) }
    fn binding_entry(&mut self, binding: u32) -> &mut DescriptorSet<'n>
    {
        self.0.entry(binding).or_insert_with(DescriptorSet::new)
    }
    fn iter(&self) -> std::collections::btree_map::Iter<u32, DescriptorSet<'n>> { self.0.iter() }
}
impl<'n> DescriptorSet<'n>
{
    fn new() -> Self { DescriptorSet(BTreeMap::new()) }
    pub fn set_index(&self, index: u32) -> Option<&[Descriptor<'n>]> { self.0.get(&index).map(|x| &x[..]) }
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
struct SpirvConstantVariable<'n> { name: &'n str, ty: &'n spv::Typedef<'n>, value: Box<ConstantValue> }
impl<'n> std::fmt::Display for SpirvConstantVariable<'n>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        write!(fmt, "{}: {:?} = {:?}", self.name, self.ty, self.value)
    }
}

pub struct ShaderInterface<'m>
{
    exec_model: spvdefs::ExecutionModel, inputs: BTreeMap<Id, SpirvVariableRef<'m>>, builtins: BTreeMap<spvdefs::BuiltIn, Vec<SpirvVariableRef<'m>>>,
    outputs: BTreeMap<Id, SpirvVariableRef<'m>>, pub descriptors: DescriptorSetSlots<'m>,
    input_attachments: BTreeMap<u32, Vec<SpirvVariableRef<'m>>>,
    spec_constants: BTreeMap<u32, SpirvConstantVariable<'m>>
}

impl<'m> ShaderInterface<'m>
{
    pub fn make(module: &'m SpirvModule, collected: &'m CollectedData<'m>, er: &mut ErrorReporter) -> Result<Self, SpirvReadError>
    {
        struct DecoratedVariableRef<'s>
        {
            name: Vec<Cow<'s, str>>, _type: &'s spv::Typedef<'s>, decorations: Option<Cow<'s, DecorationList>>
        }
        impl<'s> DecoratedVariableRef<'s>
        {
            fn toplevel_from_id(module: &'s SpirvModule, collected: &'s CollectedData<'s>, id: Id, tyid: Id) -> Self
            {
                DecoratedVariableRef
                {
                    name: vec![module.names.lookup_in_toplevel(id).unwrap_or("<anon>").into()],
                    _type: collected.types.get(tyid).unwrap(),
                    decorations: module.decorations.lookup_in_toplevel(id).map(Cow::Borrowed)
                }
            }
        }

        // Getting all input/output/descripted variables or pointers
        let mut exec_model = SetOnce::new();
        let (mut inputs, mut outputs, mut descriptors, mut input_attachments) = (Vec::new(), Vec::new(), DescriptorSetSlots::new(), BTreeMap::new());
        for op in module.operations.iter()
        {
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
                    spvdefs::StorageClass::Input => inputs.push(DecoratedVariableRef::toplevel_from_id(module, collected, id, result_type)),
                    spvdefs::StorageClass::Output => outputs.push(DecoratedVariableRef::toplevel_from_id(module, collected, id, result_type)),
                    spvdefs::StorageClass::Uniform | spvdefs::StorageClass::UniformConstant => if let Some(decos) = module.decorations.lookup_in_toplevel(id)
                    {
                        let t = collected.types.get(result_type).unwrap();
                        match t.dereference()
                        {
                            ia @ &spv::Typedef { def: spv::Type::Image { dim: spvdefs::Dim::SubpassData, .. }, .. } => match decos.input_attachment_index()
                            {
                                Some(iax) => input_attachments.entry(iax).or_insert_with(Vec::new).push(SpirvVariableRef
                                    {
                                        path: vec![Cow::Borrowed(module.names.toplevel.get(&id).unwrap())], _type: ia
                                    }),
                                _ => er.report("Required `input_attachment_index` decoration for SubpassData".to_owned())
                            },
                            td => match (decos.descriptor_bound_index(), decos.descriptor_set_index())
                            {
                                (Some(b), Some(s)) =>
                                {
                                    let array_index = decos.array_index().unwrap_or(0);
                                    let desc = match td
                                    {
                                        &spv::Typedef { def: spv::Type::SampledImage(ref si), .. } => Descriptor::SampledImage(si),
                                        _ => Descriptor::UniformBuffer(td)
                                    };
                                    descriptors.binding_entry(b).set_entry(s).set(array_index as _, desc);
                                },
                                (None, Some(_)) => er.report("Required `binding` decoration for Uniform".to_owned()),
                                (Some(_), None) => er.report("Required `set` decoration for Uniform".to_owned()),
                                (None, None) => er.report("Required `binding` and `set` decorations for Uniform".to_owned())
                            }
                        }
                    }
                    else { println!("Warn: Undecorated Uniform/UniformConstant Variable: {}", id); },
                    _ => (/* otherwise */)
                },
                &Operation::TypePointer { storage: spvdefs::StorageClass::Output, _type, .. } =>
                    if let Some(&spv::Typedef { name: Some(ref parent_name), def: spv::Type::Structure(ref m) }) = collected.types.get(_type)
                    {
                        enumerate_structure_elements(_type, parent_name, &m.members, &module.decorations, &mut outputs);
                    },
                &Operation::TypePointer { storage: spvdefs::StorageClass::Input, _type, .. } =>
                    if let Some(&spv::Typedef { name: Some(ref parent_name), def: spv::Type::Structure(ref m) }) = collected.types.get(_type)
                    {
                        enumerate_structure_elements(_type, parent_name, &m.members, &module.decorations, &mut inputs);
                    },
                _ => ()
            }
        }
        let (mut inlocs, mut outlocs, mut builtins) = (BTreeMap::<u32, SpirvVariableRef>::new(), BTreeMap::<u32, SpirvVariableRef>::new(), BTreeMap::new());
        for (decos, name, ty) in inputs.into_iter().filter_map(|DecoratedVariableRef { decorations, name, _type }| decorations.map(|d| (d, name, _type)))
        {
            if let Some(loc) = decos.location()
            {
                use std::collections::btree_map::Entry;
                match inlocs.entry(loc)
                {
                    Entry::Occupied(e) => er.report(format!("Input #{} has been found twice (previous declaration was for {:?})", loc, e.get().path)),
                    Entry::Vacant(v) => { v.insert(SpirvVariableRef { path: name, _type: ty.dereference() }); }
                }
            }
            else if let Some(bty) = decos.builtin() { builtins.entry(bty).or_insert_with(Vec::new).push(SpirvVariableRef { path: name, _type: ty.dereference() }) }
            else { println!("Warning: An input variable found that has no location"); }
        }
        for (decos, name, ty) in outputs.into_iter().filter_map(|DecoratedVariableRef { decorations, name, _type }| decorations.map(|d| (d, name, _type)))
        {
            if let Some(loc) = decos.location()
            {
                use std::collections::btree_map::Entry;
                match outlocs.entry(loc)
                {
                    Entry::Occupied(e) => er.report(format!("Output #{} has been found twice (previous declaration was for {:?})", loc, e.get().path)),
                    Entry::Vacant(v) => { v.insert(SpirvVariableRef { path: name, _type: ty.dereference() }); }
                }
            }
            else if let Some(bty) = decos.builtin()
            {
                builtins.entry(bty).or_insert_with(Vec::new).push(SpirvVariableRef { path: name, _type: ty.dereference() });
            }
            else { println!("Warning: An output variable found that has no location"); }
        }
        let mut spec_constants = BTreeMap::new();
        for (&id, c) in collected.constants.specialized.iter()
        {
            let sid = if let Some(s) = module.decorations.lookup_in_toplevel(id).and_then(DecorationList::spec_id) { s }
                else { println!("Warning: OpSpecConstant** #{} is not decorated by SpecId", id); continue; };
            if spec_constants.contains_key(&sid) { println!("Warning: Duplicated specialization constant id {}", sid); continue; }

            let name = module.names.lookup_in_toplevel(id).unwrap_or("<anon>");
            let ty = collected.types.get(collected.assigned.at(id).expect("Referring illegal id").result_type().expect("Could not find a result type")).expect("Could not find a type");
            spec_constants.insert(sid, SpirvConstantVariable { name, ty, value: c.clone_inner() });
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
        for (l, v) in self.inputs.iter() { println!("-- #{}: {}", l, v); }
        println!("- Outputs: ");
        for (l, v) in self.outputs.iter() { println!("-- #{}: {}", l, v); }
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

#[derive(Debug, Clone)]
pub struct PlacedStructureMember<'s: 't, 't>
{
    pub name: &'s str, pub offset: usize, pub ty: &'t spv::Typedef<'s>
}
impl<'m> ShaderInterface<'m>
{
    pub fn structure_layout_for<'t>(&self, structure: &'t spv::TyStructure<'m>, decorations: &DecorationMaps) -> Vec<PlacedStructureMember<'m, 't>>
    {
        structure.members.iter().enumerate().map(|(i, m)|
        {
            let offset = if let Some(decos) = decorations.lookup_member(structure.id, i)
            {
                if let Some(o) = decos.offset() { o as _ }
                else { println!("Warning: Undecorated member by Offset"); 0 }
            } else { println!("Warning: No decorations for member"); 0 };
            PlacedStructureMember { name: m.name.unwrap(), ty: &m._type, offset }
        }).collect()
    }
}
