use std::io::prelude::*;
use std::io::BufReader;
use std::collections::*;
use std::borrow::*;

mod spvdefs;
use spvdefs as spv;
use spvdefs::Id;
mod module_loader;
use module_loader::*;

fn main()
{
    match std::env::args().nth(1)
    {
        Some(n) =>
        {
            let module = std::fs::File::open(n).map(BufReader::new).map_err(From::from).and_then(SpirvModule::load).unwrap();
            module.dump();
            let sinterface = ShaderInterface::make(module).unwrap();
            sinterface.dump();
        },
        None => show_help()
    }
}
fn show_help()
{
    println!("usage>app [inputFilePath]");
}

#[derive(Clone, Debug)]
struct SpirvStructureElement<'n> { name: Option<Cow<'n, str>>, _type: SpirvTypedef<'n> }
#[derive(Clone)]
enum SpirvType<'n>
{
    Void, Bool, Int(u8, bool), Float(u8), Vector(u32, Box<SpirvTypedef<'n>>), Matrix(u32, Box<SpirvTypedef<'n>>),
    Array(u32, Box<SpirvTypedef<'n>>), DynamicArray(Box<SpirvTypedef<'n>>), Pointer(spv::StorageClass, Box<SpirvTypedef<'n>>),
    Structure(Vec<SpirvStructureElement<'n>>),
    Image
    {
        sampled_type: Box<SpirvTypedef<'n>>, dim: spv::Dim, depth: u32, arrayed: u32, ms: u32, sampled: u32, format: spv::ImageFormat,
        qualifier: Option<spv::AccessQualifier>
    }, Sampler, SampledImage(Box<SpirvTypedef<'n>>), Function(Box<SpirvTypedef<'n>>, Vec<SpirvTypedef<'n>>)
}
#[derive(Clone)] struct SpirvTypedef<'n> { name: Option<Cow<'n, str>>, def: SpirvType<'n> }
type SpirvTypedefMap<'n> = BTreeMap<Id, SpirvTypedef<'n>>;
#[derive(Clone, Debug)]
enum Descriptor<'n>
{
    Empty, UniformBuffer(SpirvTypedef<'n>), SampledImage(SpirvTypedef<'n>)
}
struct DescriptorSet<'n>(BTreeMap<u32, Vec<Descriptor<'n>>>);
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
    fn set_entry(&mut self, index: u32) -> &mut Vec<Descriptor<'n>>
    {
        self.0.entry(index).or_insert_with(Vec::new)
    }
    fn iter(&self) -> std::collections::btree_map::Iter<u32, Vec<Descriptor<'n>>> { self.0.iter() }
}
impl<'n> std::fmt::Debug for SpirvType<'n>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        match self
        {
            &SpirvType::Void => write!(fmt, "void"),
            &SpirvType::Bool => write!(fmt, "bool"),
            &SpirvType::Int(bits, true) => write!(fmt, "signed {}bit int", bits),
            &SpirvType::Int(bits, false) => write!(fmt, "unsigned {}bit int", bits),
            &SpirvType::Float(bits) => write!(fmt, "{}bit float", bits),
            &SpirvType::Vector(n, ref e) => write!(fmt, "vec{} of {:?}", n, e),
            &SpirvType::Matrix(n, ref e) => write!(fmt, "mat{} of {:?}", n, e),
            &SpirvType::Array(n, ref e) => write!(fmt, "array of {:?} with {} element(s)", e, n),
            &SpirvType::DynamicArray(ref e) => write!(fmt, "array of {:?}", e),
            &SpirvType::Pointer(ref s, ref p) => write!(fmt, "pointer to {:?} of {:?}", s, p),
            &SpirvType::Structure(ref m) => write!(fmt, "struct {:?}", m),
            &SpirvType::Image { ref sampled_type, .. } => write!(fmt, "Image sampled with type {:?}", sampled_type),
            &SpirvType::Sampler => write!(fmt, "sampler"),
            &SpirvType::SampledImage(ref i) => write!(fmt, "sampled image of {:?}", i),
            &SpirvType::Function(ref r, ref p) => write!(fmt, "({:?}) => {:?}", p, r)
        }
    }
}
impl<'n> std::fmt::Debug for SpirvTypedef<'n>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        match self
        {
            &SpirvTypedef { ref name, def: SpirvType::Structure(ref m) } => write!(fmt, "struct {:?} {:?}", name, m),
            &SpirvTypedef { ref def, .. } => def.fmt(fmt)
        }
    }
}
impl<'n> SpirvTypedef<'n>
{
    fn concrete(&self) -> SpirvTypedef<'static>
    {
        SpirvTypedef { name: self.name.clone().map(|x| Cow::Owned(x.into_owned())), def: self.def.concrete() }
    }
    fn dereference(&self) -> &SpirvTypedef<'n>
    {
        match self
        {
            &SpirvTypedef { def: SpirvType::Pointer(_, ref p), .. } => p,
            s => s
        }
    }
}
impl<'n> SpirvType<'n>
{
    fn concrete(&self) -> SpirvType<'static>
    {
        match self
        {
            &SpirvType::Void => SpirvType::Void, &SpirvType::Bool => SpirvType::Bool,
            &SpirvType::Int(bits, sign) => SpirvType::Int(bits, sign),
            &SpirvType::Float(bits) => SpirvType::Float(bits),
            &SpirvType::Vector(n, ref e) => SpirvType::Vector(n, Box::new(e.concrete())),
            &SpirvType::Matrix(n, ref c) => SpirvType::Matrix(n, Box::new(c.concrete())),
            &SpirvType::Array(n, ref e) => SpirvType::Array(n, Box::new(e.concrete())),
            &SpirvType::DynamicArray(ref e) => SpirvType::DynamicArray(Box::new(e.concrete())),
            &SpirvType::Structure(ref m) => SpirvType::Structure(m.iter().map(SpirvStructureElement::concrete).collect()),
            &SpirvType::Pointer(s, ref p) => SpirvType::Pointer(s.clone(), Box::new(p.concrete())),
            &SpirvType::Image { ref sampled_type, ref dim, depth, arrayed, ms, sampled, ref format, ref qualifier } => SpirvType::Image
            {
                sampled_type: Box::new(sampled_type.concrete()), dim: dim.clone(), depth: depth, arrayed: arrayed, ms: ms,
                sampled: sampled, format: format.clone(), qualifier: qualifier.clone()
            },
            &SpirvType::Sampler => SpirvType::Sampler,
            &SpirvType::SampledImage(ref i) => SpirvType::SampledImage(Box::new(i.concrete())),
            &SpirvType::Function(ref r, ref p) => SpirvType::Function(Box::new(r.concrete()), p.iter().map(SpirvTypedef::concrete).collect())
        }
    }
}
impl<'n> SpirvStructureElement<'n>
{
    fn concrete(&self) -> SpirvStructureElement<'static>
    {
        SpirvStructureElement { name: self.name.clone().map(|x| Cow::Owned(x.into_owned())), _type: self._type.concrete() }
    }
}
#[derive(Clone, Debug)]
struct SpirvVariableRef { path: Vec<String>, _type: SpirvTypedef<'static> }
impl std::fmt::Display for SpirvVariableRef
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        write!(fmt, "{}: {:?}", self.path.join("::"), self._type)
    }
}

struct ShaderInterface
{
    exec_model: spv::ExecutionModel, inputs: BTreeMap<Id, Vec<SpirvVariableRef>>, builtins: BTreeMap<spv::BuiltIn, Vec<SpirvVariableRef>>,
    outputs: BTreeMap<Id, Vec<SpirvVariableRef>>, descriptors: DescriptorSetSlots<'static>,
    input_attachments: BTreeMap<u32, Vec<SpirvVariableRef>>
}

struct ErrorReporter { has_error: bool }
impl ErrorReporter
{
    fn new() -> Self { ErrorReporter { has_error: false } }
    fn report(&mut self, msg: String)
    {
        writeln!(std::io::stderr(), "*Error* {}", msg).unwrap();
        self.has_error = true;
    }
}

struct AssignedOperations<'m>(Vec<Option<&'m Operation>>);
impl<'m> AssignedOperations<'m>
{
    fn collect(module: &'m SpirvModule) -> Self
    {
        let mut sink = vec![None; module.id_range.len()];
        for o in module.operations.iter()
        {
            if let Some(id) = o.result_id()
            {
                sink[id as usize] = Some(o);
            }
        }
        AssignedOperations(sink)
    }
}
impl<'m> std::ops::Deref for AssignedOperations<'m> { type Target = [Option<&'m Operation>]; fn deref(&self) -> &Self::Target { &self.0[..] } }

struct TypeAggregator<'n>(SpirvTypedefMap<'n>);
impl<'n> TypeAggregator<'n>
{
    // Public APIs //
    fn resolve_all(ops: &AssignedOperations, names: &'n NameMaps, err: &mut ErrorReporter) -> Self
    {
        let mut t = SpirvTypedefMap::new();
        for (n, op) in ops.iter().enumerate().filter(|&(_, op)| op.map(Operation::is_type_op).unwrap_or(false))
        {
            if t.contains_key(&(n as Id))
            {
                err.report(format!("Type Definition for ID {} has been found once more.", n));
            }
            else
            {
                let r = Self::try_resolve(&mut t, ops, names, n as Id, &op.unwrap());
                t.insert(n as Id, r);
            }
        }
        TypeAggregator(t)
    }
    fn get(&self, id: Id) -> Option<&SpirvTypedef<'n>> { self.0.get(&id) }

    // Private APIs //
    fn lookup<'s>(sink: &'s mut SpirvTypedefMap<'n>, ops: &AssignedOperations, names: &'n NameMaps, id: Id) -> &'s SpirvTypedef<'n>
    {
        if !sink.contains_key(&id)
        {
            let resolved = Self::try_resolve(sink, ops, names, id, ops[id as usize].as_ref().unwrap());
            sink.insert(id, resolved);
        }
        sink.get(&id).as_ref().unwrap()
    }
    fn try_resolve(sink: &mut SpirvTypedefMap<'n>, ops: &AssignedOperations, names: &'n NameMaps, id: Id, op: &Operation) -> SpirvTypedef<'n>
    {
        let t = match op
        {
            &Operation::TypeVoid { .. } => SpirvType::Void,
            &Operation::TypeBool { .. } => SpirvType::Bool,
            &Operation::TypeInt { width, signedness, .. } => SpirvType::Int(width as u8, signedness),
            &Operation::TypeFloat { width, .. } => SpirvType::Float(width as u8),
            &Operation::TypeVector { component_type, component_count, .. }
                => SpirvType::Vector(component_count, Box::new(Self::lookup(sink, ops, names, component_type).clone())),
            &Operation::TypeMatrix { column_type, column_count, .. }
                => SpirvType::Matrix(column_count, Box::new(Self::lookup(sink, ops, names, column_type).clone())),
            &Operation::TypeArray { element_type, length, .. } => SpirvType::Array(length, Box::new(Self::lookup(sink, ops, names, element_type).clone())),
            &Operation::TypeRuntimeArray { element_type, .. } => SpirvType::DynamicArray(Box::new(Self::lookup(sink, ops, names, element_type).clone())),
            &Operation::TypePointer { ref storage, _type, .. }
                => SpirvType::Pointer(storage.clone(), Box::new(Self::lookup(sink, ops, names, _type).clone())),
            &Operation::TypeStruct { ref member_types, .. } => SpirvType::Structure(member_types.iter().enumerate().map(|(n, &x)| SpirvStructureElement
            {
                name: names.member.get(&id).and_then(|mb| mb.get(n)).map(|x| Cow::Borrowed(x as &str)),
                _type: Self::lookup(sink, ops, names, x).clone()
            }).collect()),
            &Operation::TypeImage { sampled_type, ref dim, depth, arrayed, ms, sampled, ref format, ref qualifier, .. } => SpirvType::Image
            {
                sampled_type: Box::new(Self::lookup(sink, ops, names, sampled_type).clone()),
                dim: dim.clone(), depth: depth, arrayed: arrayed, ms: ms, sampled: sampled, format: format.clone(), qualifier: qualifier.clone()
            },
            &Operation::TypeSampler { .. } => SpirvType::Sampler,
            &Operation::TypeSampledImage { image_type, .. } => SpirvType::SampledImage(Box::new(Self::lookup(sink, ops, names, image_type).clone())),
            &Operation::TypeFunction { return_type, ref parameters, .. } => SpirvType::Function(
                Box::new(Self::lookup(sink, ops, names, return_type).clone()),
                parameters.iter().map(|&x| Self::lookup(sink, ops, names, x).clone()).collect()),
            _ => unreachable!("Unresolvable as a type: {:?}", op)
        };

        SpirvTypedef { name: names.toplevel.get(&id).map(|x| Cow::Borrowed(x as &str)), def: t }
    }
}

impl ShaderInterface
{
    fn make(module: SpirvModule) -> Result<Self, SpirvReadError>
    {
        let mut er = ErrorReporter::new();
        let ops = AssignedOperations::collect(&module);
        let type_aggregator = TypeAggregator::resolve_all(&ops, &module.names, &mut er);
        if er.has_error { return Err(SpirvReadError::SomeErrorOccured) }

        // Getting all input/output/descripted variables or pointers
        let mut exec_model = SetOnce::new();
        let (mut inputs, mut outputs, mut descriptors, mut input_attachments) = (Vec::new(), Vec::new(), DescriptorSetSlots::new(), BTreeMap::new());
        for op in module.operations.iter()
        {
            struct DecoratedVariableRef<'s>
            {
                name: Vec<Cow<'static, str>>, _type: &'s SpirvTypedef<'s>, decorations: Option<Cow<'s, DecorationList>>
            }
            fn enumerate_structure_elements<'n>(id: Id, parent_name: &'n str, member: &'n [SpirvStructureElement<'n>],
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
                        name: vec![Cow::Owned(parent_name.to_owned()), e.name.as_ref().map(|x| Cow::Owned(x.clone().into_owned())).unwrap_or(Cow::Borrowed("<anon>"))],
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
                    spv::StorageClass::Input => inputs.push(DecoratedVariableRef
                    {
                        name: vec![module.names.toplevel.get(&id).cloned().map(Cow::from).unwrap_or(Cow::Borrowed("<anon>"))],
                        _type: type_aggregator.get(result_type).as_ref().unwrap(),
                        decorations: module.decorations.toplevel.get(&id).map(Cow::Borrowed)
                    }),
                    spv::StorageClass::Output => outputs.push(DecoratedVariableRef
                    {
                        name: vec![module.names.toplevel.get(&id).cloned().map(Cow::from).unwrap_or(Cow::Borrowed("<anon>"))],
                        _type: type_aggregator.get(result_type).as_ref().unwrap(),
                        decorations: module.decorations.toplevel.get(&id).map(Cow::Borrowed)
                    }),
                    spv::StorageClass::Uniform | spv::StorageClass::UniformConstant => if let Some(decos) = module.decorations.toplevel.get(&id)
                    {
                        let t = type_aggregator.get(result_type).unwrap();
                        match t.dereference()
                        {
                            ia @ &SpirvTypedef { def: SpirvType::Image { dim: spv::Dim::SubpassData, .. }, .. } =>
                            {
                                if let Some(&Decoration::InputAttachmentIndex(iax)) = decos.get(spv::Decoration::InputAttachmentIndex)
                                {
                                    input_attachments.entry(iax).or_insert_with(Vec::new).push(SpirvVariableRef
                                    {
                                        path: vec![module.names.toplevel.get(&id).unwrap().to_owned()],
                                        _type: ia.concrete()
                                    });
                                }
                                else { er.report("Required `input_attachment_index` decoration for SubpassData".to_owned()); }
                            },
                            td => if let Some(&Decoration::Binding(binding)) = decos.get(spv::Decoration::Binding)
                            {
                                if let Some(&Decoration::DescriptorSet(set)) = decos.get(spv::Decoration::DescriptorSet)
                                {
                                    let array_index = if let Some(&Decoration::Index(x)) = decos.get(spv::Decoration::Index) { x } else { 0 } as usize;
                                    let mut descriptors = descriptors.binding_entry(binding).set_entry(set);
                                    if descriptors.len() <= array_index
                                    {
                                        descriptors.resize(array_index, Descriptor::Empty);
                                        let desc = match td
                                        {
                                            &SpirvTypedef { def: SpirvType::Structure(_), .. } => Descriptor::UniformBuffer(td.concrete()),
                                            &SpirvTypedef { def: SpirvType::SampledImage(ref si), .. } => Descriptor::SampledImage(si.concrete()),
                                            _ => Descriptor::UniformBuffer(td.concrete())
                                        };
                                        descriptors.push(desc);
                                    }
                                }
                                else { er.report("Required `set` decoration for Uniform".to_owned()); }
                            }
                            else { er.report("Required `binding` decoration for Uniform".to_owned()); }
                        }
                    },
                    _ => (/* otherwise */)
                },
                &Operation::TypePointer { storage: spv::StorageClass::Output, _type, .. } =>
                    if let Some(&SpirvTypedef { name: Some(ref parent_name), def: SpirvType::Structure(ref m) }) = type_aggregator.get(_type)
                    {
                        enumerate_structure_elements(_type, parent_name, m, &decorations, &mut outputs);
                    },
                &Operation::TypePointer { storage: spv::StorageClass::Input, _type, .. } =>
                    if let Some(&SpirvTypedef { name: Some(ref parent_name), def: SpirvType::Structure(ref m) }) = type_aggregator.get(_type)
                    {
                        enumerate_structure_elements(_type, parent_name, m, &decorations, &mut inputs);
                    },
                _ => ()
            }
        }
        let (mut inlocs, mut outlocs, mut builtins) = (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
        for n in inputs.into_iter()
        {
            if let Some(decos) = n.decorations
            {
                if let Some(&Decoration::Location(location)) = decos.get(spv::Decoration::Location)
                {
                    inlocs.entry(location).or_insert_with(Vec::new).push(SpirvVariableRef
                    {
                        path: n.name.into_iter().map(|x| x.into_owned()).collect(), _type: n._type.dereference().concrete()
                    });
                }
                else if let Some(&Decoration::BuiltIn(bi)) = decos.get(spv::Decoration::BuiltIn)
                {
                    builtins.entry(bi).or_insert_with(Vec::new).push(SpirvVariableRef
                    {
                        path: n.name.into_iter().map(|x| x.into_owned()).collect(), _type: n._type.dereference().concrete()
                    });
                }
            }
        }
        for n in outputs.into_iter()
        {
            if let Some(decos) = n.decorations
            {
                if let Some(&Decoration::Location(location)) = decos.get(spv::Decoration::Location)
                {
                    outlocs.entry(location).or_insert_with(Vec::new).push(SpirvVariableRef
                    {
                        path: n.name.into_iter().map(|x| x.into_owned()).collect(), _type: n._type.dereference().concrete()
                    });
                }
                else if let Some(&Decoration::BuiltIn(bi)) = decos.get(spv::Decoration::BuiltIn)
                {
                    builtins.entry(bi).or_insert_with(Vec::new).push(SpirvVariableRef
                    {
                        path: n.name.into_iter().map(|x| x.into_owned()).collect(), _type: n._type.dereference().concrete()
                    });
                }
            }
        }

        Ok(ShaderInterface
        {
            exec_model: exec_model, inputs: inlocs, builtins: builtins, outputs: outlocs, descriptors: descriptors, input_attachments: input_attachments
        })
    }
    fn dump(&self)
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
    }
}
