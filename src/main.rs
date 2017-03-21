use std::io::prelude::*;
use std::io::BufReader;
use std::collections::*;
use std::borrow::*;

mod spvdefs;
use spvdefs as spv;

fn main()
{
    match std::env::args().nth(1)
    {
        Some(n) => std::fs::File::open(n).map(BufReader::new).map_err(From::from).and_then(parse_spirv).unwrap().dump(),
        None => show_help()
    }
}
fn show_help()
{
    println!("usage>app [inputFilePath]");
}

pub struct WordStream<Source: Read + Seek>
{
    src: Source, require_conversion: bool
}
impl<Source: Read + Seek> WordStream<Source>
{
    fn read(&mut self) -> std::io::Result<u32>
    {
        let mut word: u32 = 0;
        self.src.read_exact(unsafe { std::mem::transmute::<_, &mut [u8; 4]>(&mut word) })
            .map(|_| if self.require_conversion { word.swap_bytes() } else { word })
    }
    fn reserved(&mut self) -> std::io::Result<()>
    {
        self.src.seek(std::io::SeekFrom::Current(4)).map(|_| ())
    }
}
#[derive(Debug)]
pub enum SpirvReadError
{
    InvalidMagic, MultipleLocationNotAllowed(Vec<String>), MultipleBuiltInsNotAllowed(Vec<String>), MultipleEntryPointNotAllowed,
    SomeErrorOccured
}
impl std::fmt::Display for SpirvReadError
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result { std::fmt::Debug::fmt(self, fmt) }
}
impl std::error::Error for SpirvReadError
{
    fn description(&self) -> &str
    {
        match self
        {
            &SpirvReadError::InvalidMagic => "Invalid Magic Number",
            &SpirvReadError::MultipleLocationNotAllowed(_) => "Multiple Location for single variable are not allowed",
            &SpirvReadError::MultipleBuiltInsNotAllowed(_) => "Multiple BulitIns for single variable are not allowed",
            &SpirvReadError::MultipleEntryPointNotAllowed => "Multiple Entry Points are not allowed in single module",
            &SpirvReadError::SomeErrorOccured => "Some errors occured in process, check stderr"
        }
    }
    fn cause(&self) -> Option<&std::error::Error> { None }
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
type NameMap = BTreeMap<Id, String>;
type MemberNameMap = BTreeMap<Id, Vec<String>>;
struct NameMaps { names: NameMap, member_names: MemberNameMap }
#[derive(Clone)]
struct DecorationList(BTreeMap<spv::Decoration, Decoration>);
impl DecorationList
{
    fn new() -> Self { DecorationList(BTreeMap::new()) }
    fn register(&mut self, id: spv::Decoration, dec: Decoration)
    {
        if self.0.contains_key(&id) { println!("Warn: Duplicating Decoration {:?}", dec); }
        else { self.0.insert(id, dec); }
    }
    fn iter(&self) -> std::collections::btree_map::Iter<spv::Decoration, Decoration> { self.0.iter() }
    fn get(&self, id: spv::Decoration) -> Option<&Decoration> { self.0.get(&id) }
}
type DecorationMap = BTreeMap<Id, DecorationList>;
type MemberDecorationMap = BTreeMap<Id, Vec<DecorationList>>;
struct DecorationMaps { toplevel: DecorationMap, member: MemberDecorationMap }
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
    fn concrete(self) -> SpirvTypedef<'static>
    {
        SpirvTypedef { name: self.name.map(|x| Cow::Owned(x.into_owned())), def: self.def.concrete() }
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
    fn concrete(self) -> SpirvType<'static>
    {
        match self
        {
            SpirvType::Void => SpirvType::Void, SpirvType::Bool => SpirvType::Bool,
            SpirvType::Int(bits, sign) => SpirvType::Int(bits, sign),
            SpirvType::Float(bits) => SpirvType::Float(bits),
            SpirvType::Vector(n, e) => SpirvType::Vector(n, Box::new(e.concrete())),
            SpirvType::Matrix(n, c) => SpirvType::Matrix(n, Box::new(c.concrete())),
            SpirvType::Array(n, e) => SpirvType::Array(n, Box::new(e.concrete())),
            SpirvType::DynamicArray(e) => SpirvType::DynamicArray(Box::new(e.concrete())),
            SpirvType::Structure(m) => SpirvType::Structure(m.into_iter().map(SpirvStructureElement::concrete).collect()),
            SpirvType::Pointer(s, p) => SpirvType::Pointer(s.clone(), Box::new(p.concrete())),
            SpirvType::Image { sampled_type, dim, depth, arrayed, ms, sampled, format, qualifier } => SpirvType::Image
            {
                sampled_type: Box::new(sampled_type.concrete()), dim: dim.clone(), depth: depth, arrayed: arrayed, ms: ms,
                sampled: sampled, format: format.clone(), qualifier: qualifier.clone()
            },
            SpirvType::Sampler => SpirvType::Sampler,
            SpirvType::SampledImage(i) => SpirvType::SampledImage(Box::new(i.concrete())),
            SpirvType::Function(r, p) => SpirvType::Function(Box::new(r.concrete()), p.into_iter().map(SpirvTypedef::concrete).collect())
        }
    }
}
impl<'n> SpirvStructureElement<'n>
{
    fn concrete(self) -> SpirvStructureElement<'static>
    {
        SpirvStructureElement { name: self.name.map(|x| Cow::Owned(x.into_owned())), _type: self._type.concrete() }
    }
}
struct DecoratedVariableRef<'s> { name: Vec<Cow<'s, str>>, _type: &'s SpirvTypedef<'s>, decorations: Cow<'s, [Decoration]> }
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

struct TypeAggregator<'n>(SpirvTypedefMap<'n>);
impl<'n> TypeAggregator<'n>
{
    // Public APIs //
    fn resolve_all(ops: &Vec<Operation>, names: &'n NameMaps, err: &mut ErrorReporter) -> Self
    {
        let mut t = SpirvTypedefMap::new();
        for (n, op) in ops.iter().enumerate().filter(|&(_, op)| op.is_type_op())
        {
            if t.contains_key(&(n as Id))
            {
                err.report(format!("Type Definition for ID {} has been found once more.", n));
            }
            else
            {
                let r = Self::try_resolve(&mut t, ops, names, n as Id, op);
                t.insert(n as Id, r);
            }
        }
        TypeAggregator(t)
    }
    fn get(&self, id: Id) -> Option<&SpirvTypedef<'n>> { self.0.get(&id) }

    // Private APIs //
    fn lookup<'s>(sink: &'s mut SpirvTypedefMap<'n>, ops: &Vec<Operation>, names: &'n NameMaps, id: Id) -> &'s SpirvTypedef<'n>
    {
        if !sink.contains_key(&id)
        {
            let resolved = Self::try_resolve(sink, ops, names, id, &ops[id as usize]);
            sink.insert(id, resolved);
        }
        sink.get(&id).as_ref().unwrap()
    }
    fn try_resolve(sink: &mut SpirvTypedefMap<'n>, ops: &Vec<Operation>, names: &'n NameMaps, id: Id, op: &Operation) -> SpirvTypedef<'n>
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
                name: names.member_names.get(&id).and_then(|mb| mb.get(n)).map(|x| Cow::Borrowed(x as &str)),
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

        SpirvTypedef { name: names.names.get(&id).map(|x| Cow::Borrowed(x as &str)), def: t }
    }
}

fn parse_spirv<F: Read + Seek>(mut fp: F) -> Result<ShaderInterface, Box<std::error::Error>>
{
    let mut magic: u32 = 0;
    try!(fp.read_exact(unsafe { std::mem::transmute::<_, &mut [u8; 4]>(&mut magic) }));
    let mut stream = try!(if magic == 0x07230203
    {
        Ok(WordStream { src: fp, require_conversion: false })
    }
    else if magic == 0x03022307
    {
        Ok(WordStream { src: fp, require_conversion: true })
    }
    else { Err(SpirvReadError::InvalidMagic) });
    
    let (v_major, v_minor) = try!(stream.read().map(deconstruct_version));
    let genmagic = try!(stream.read());
    let bound = try!(stream.read());
    try!(stream.reserved());

    println!("SPIR-V Module Header: ");
    println!("-- Endian Mismatching: {}", stream.require_conversion);
    println!("-- Version: {}.{}", v_major, v_minor);
    println!("-- Generator Magic: {:08x}", genmagic);
    println!("-- ID Bound: {}", bound);

    // Parse Module, collect decorations and names
    let mut exec_model = None;
    let mut operation_slots = vec![Operation::Nop; bound as usize];
    let mut decorations = DecorationMaps { toplevel: DecorationMap::new(), member: MemberDecorationMap::new() };
    let mut names = NameMaps { names: NameMap::new(), member_names: MemberNameMap::new() };
    loop
    {
        match parse_op(&mut stream)
        {
            OperandParsingResult::Term => break,
            OperandParsingResult::Error(e) => return Err(e),
            OperandParsingResult::Continue(op) =>
            {
                println!("Operand => {:?}", op);
                match op
                {
                    Operation::TypeVoid { result } | Operation::TypeBool { result } | Operation::TypeInt { result, .. } | Operation::TypeFloat { result, .. }
                    | Operation::TypeVector { result, .. } | Operation::TypeMatrix { result, .. } | Operation::TypeImage { result, .. }
                    | Operation::TypeSampler { result, .. } | Operation::TypeSampledImage { result, .. } | Operation::TypeArray { result, .. }
                    | Operation::TypeRuntimeArray { result, .. } | Operation::TypeStruct { result, .. } | Operation::TypeOpaque { result, .. }
                    | Operation::TypePointer { result, .. } | Operation::TypeFunction { result, .. } | Operation::TypeEvent { result }
                    | Operation::TypeDeviceEvent { result } | Operation::TypeReserveId { result } | Operation::TypeQueue { result }
                    | Operation::TypePipe { result } | Operation::Variable { result, .. } => operation_slots[result as usize] = op,
                    Operation::Decorate { target, decoid, decoration } => decorations.toplevel.entry(target).or_insert_with(DecorationList::new)
                        .register(decoid, decoration),
                    Operation::MemberDecorate { structure_type, member, decoid, decoration } =>
                    {
                        let mut sink = decorations.member.entry(structure_type).or_insert_with(Vec::new);
                        if sink.len() <= member as usize { sink.resize(member as usize + 1, DecorationList::new()); }
                        sink[member as usize].register(decoid, decoration);
                    },
                    Operation::Name { target, name } => { names.names.entry(target).or_insert(name); },
                    Operation::MemberName { _type, member, name } =>
                    {
                        let sink = names.member_names.entry(_type).or_insert(Vec::new());
                        if sink.len() <= member as usize { sink.resize(member as usize, String::default()); sink.push(name) } else { sink[member as usize] = name; }
                    },
                    Operation::EntryPoint { model, .. }
                        => if exec_model.is_none() { exec_model = Some(model); } else { return Err(Box::new(SpirvReadError::MultipleEntryPointNotAllowed)) },
                    _ => ()
                }
            }
        }
    }

    ShaderInterface::make(exec_model.unwrap(), operation_slots, decorations, names).map_err(From::from)
}
impl ShaderInterface
{
    fn make(exec_model: spv::ExecutionModel, operations: Vec<Operation>, decorations: DecorationMaps, names: NameMaps)
        -> Result<Self, SpirvReadError>
    {
        let mut er = ErrorReporter::new();
        let type_aggregator = TypeAggregator::resolve_all(&operations, &names, &mut er);
        if er.has_error { return Err(SpirvReadError::SomeErrorOccured) }

        // Getting all input/output/descripted variables or pointers
        let (mut inputs, mut outputs, mut descriptors, mut input_attachments) = (Vec::new(), Vec::new(), DescriptorSetSlots::new(), BTreeMap::new());
        for (n, op) in operations.iter().enumerate()
        {
            let id = n as Id;
            let name = names.names.get(&id);
            match name
            {
                Some(ref nm) => println!("#{}({}) => {:?}", n, nm, op),
                None => println!("#{} => {:?}", n, op)
            }
            
            struct DecoratedVariableRef<'s>
            {
                name: Vec<Cow<'s, str>>, _type: &'s SpirvTypedef<'s>, decorations: Option<Cow<'s, DecorationList>>
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
                        name: vec![Cow::Borrowed(parent_name), e.name.as_ref().map(|x| Cow::from(x.borrow())).unwrap_or("<anon>".into())],
                        _type: &e._type, decorations: Some(decos)
                    }
                });
                for v in vars { sink.push(v); }
            }
            match op
            {
                &Operation::Variable { storage, result_type, .. } => match storage
                {
                    spv::StorageClass::Input => inputs.push(DecoratedVariableRef
                    {
                        name: vec![Cow::Borrowed(names.names.get(&id).unwrap() as &str)],
                        _type: type_aggregator.get(result_type).as_ref().unwrap(),
                        decorations: decorations.toplevel.get(&id).map(Cow::Borrowed)
                    }),
                    spv::StorageClass::Output => outputs.push(DecoratedVariableRef
                    {
                        name: vec![Cow::Borrowed(names.names.get(&id).unwrap() as &str)],
                        _type: type_aggregator.get(result_type).as_ref().unwrap(),
                        decorations: decorations.toplevel.get(&id).map(Cow::Borrowed)
                    }),
                    spv::StorageClass::Uniform | spv::StorageClass::UniformConstant => if let Some(decos) = decorations.toplevel.get(&id)
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
                                        path: vec![names.names.get(&id).unwrap().to_owned()],
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
enum OperandParsingResult
{
    Term, Continue(Operation), Error(Box<std::error::Error>)
}
macro_rules! try_op
{
    ($e: expr) => { match $e { Ok(x) => x, Err(e) => return OperandParsingResult::Error(e.into()) } }
}
fn parse_op<F: Read + Seek>(stream: &mut WordStream<F>) -> OperandParsingResult
{
    let op = match stream.read()
    {
        Ok(b) => Operand::from(b),
        Err(ref e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return OperandParsingResult::Term,
        Err(e) => return OperandParsingResult::Error(e.into())
    };
    let mut opargs = vec![0u32; op.word_count as usize - 1];
    for n in 0 .. op.word_count - 1
    {
        opargs[n as usize] = try_op!(stream.read());
    }

    OperandParsingResult::Continue(Operation::from_parts(op.opcode, opargs))
}
fn deconstruct_version(v: u32) -> (u8, u8)
{
    (((v & 0x00ff0000) >> 16) as u8, ((v & 0x0000ff00) >> 8) as u8)
}
struct Operand { word_count: u16, opcode: spv::Opcode }
impl std::convert::From<u32> for Operand
{
    fn from(v: u32) -> Self
    {
        Operand { word_count: (v >> 16) as u16, opcode: unsafe { std::mem::transmute(v as u16) } }
    }
}
type Id = u32;
#[derive(Debug, Clone)]
enum Operation
{
    Nop, Undef { result: Id, result_type: Id },
    SourceContinued { continued_source: String },
    Source { language: spv::SourceLanguage, version: u32, file_id: Option<Id>, source: Option<String> },
    SourceExtension { extension: String },
    Name { target: Id, name: String },
    MemberName { _type: Id, member: u32, name: String },
    String { result: Id, string: String },
    Line { file_id: Id, line: u32, column: u32 }, NoLine,
    Decorate { target: Id, decoid: spv::Decoration, decoration: Decoration },
    MemberDecorate { structure_type: Id, member: u32, decoid: spv::Decoration, decoration: Decoration },
    EntryPoint { model: spv::ExecutionModel, entry_point: Id, name: String, interfaces: Vec<Id> },
    ExecutionMode { entry_point: Id, mode: ExecutionMode },
    Capability { capability: spv::Capability },
    Variable { result: Id, result_type: Id, storage: spv::StorageClass, initializer: Option<Id> },
    TypeVoid { result: Id }, TypeBool { result: Id }, TypeInt { result: Id, width: u32, signedness: bool },
    TypeFloat { result: Id, width: u32 }, TypeVector { result: Id, component_type: Id, component_count: u32 },
    TypeMatrix { result: Id, column_type: Id, column_count: u32 },
    TypeImage
    {
        result: Id, sampled_type: Id, dim: spv::Dim, depth: u32, arrayed: u32, ms: u32, sampled: u32, format: spv::ImageFormat,
        qualifier: Option<spv::AccessQualifier>
    },
    TypeSampler { result: Id }, TypeSampledImage { result: Id, image_type: Id }, TypeArray { result: Id, element_type: Id, length: Id },
    TypeRuntimeArray { result: Id, element_type: Id }, TypeStruct { result: Id, member_types: Vec<Id> },
    TypeOpaque { result: Id, typename: String }, TypePointer { result: Id, storage: spv::StorageClass, _type: Id },
    TypeFunction { result: Id, return_type: Id, parameters: Vec<Id> }, TypeEvent { result: Id }, TypeDeviceEvent { result: Id },
    TypeReserveId { result: Id }, TypeQueue { result: Id }, TypePipe { result: Id }, TypeForwardPointer { pointer_type: Id, storage: spv::StorageClass },
    ConstantTrue { result: Id, result_type: Id },
    ConstantFalse { result: Id, result_type: Id },
    Constant { result: Id, result_type: Id, literals: Vec<u32> },
    ConstantComposite { result: Id, result_type: Id, constituents: Vec<Id> },
    ConstantSampler { result: Id, result_type: Id, addressing_mode: spv::SamplerAddressingMode, param: u32, filter_mode: spv::SamplerFilterMode },
    ConstantNull { result: Id, result_type: Id },
    SpecConstantTrue { result: Id, result_type: Id },
    SpecConstantFalse { result: Id, result_type: Id },
    SpecConstant { result: Id, result_type: Id, literals: Vec<u32> },
    SpecConstantComposite { result: Id, result_type: Id, constituents: Vec<Id> },
    SpecConstantOp { result: Id, result_type: Id, op: Box<Operation> },
    Unknown { code: spv::Opcode, args: Vec<u32> }
}
impl Operation
{
    fn from_parts(code: spv::Opcode, mut args: Vec<u32>) -> Self
    {
        use spvdefs::Opcode;

        match code
        {
            Opcode::Nop => Operation::Nop,
            Opcode::Undef => Operation::Undef { result_type: args[0], result: args[1] },
            Opcode::SourceContinued => Operation::SourceContinued { continued_source: spv::parse_string(&mut args) },
            Opcode::Source =>
            {
                let lang = args.remove(0);
                let ver = args.remove(0);
                let file_ref = if !args.is_empty() { Some(args.remove(0)) } else { None };
                let source_str = if !args.is_empty() { Some(spv::parse_string(&mut args)) } else { None };
                Operation::Source { language: unsafe { std::mem::transmute(lang) }, version: ver, file_id: file_ref, source: source_str }
            },
            Opcode::SourceExtension => Operation::SourceExtension { extension: spv::parse_string(&mut args) },
            Opcode::Name => Operation::Name { target: args.remove(0), name: spv::parse_string(&mut args) },
            Opcode::MemberName => Operation::MemberName { _type: args.remove(0), member: args.remove(0), name: spv::parse_string(&mut args) },
            Opcode::String => Operation::String { result: args.remove(0), string: spv::parse_string(&mut args) },
            Opcode::Line => Operation::Line { file_id: args[0], line: args[1], column: args[2] },
            Opcode::NoLine => Operation::NoLine,
            Opcode::Decorate =>
            {
                let t = args.remove(0);
                let (id, o) = Decoration::parse(&mut args);
                Operation::Decorate { target: t, decoid: id, decoration: o }
            },
            Opcode::MemberDecorate =>
            {
                let (st, mem) = (args[0], args[1]); args.drain(..2);
                let (id, o) = Decoration::parse(&mut args);
                Operation::MemberDecorate { structure_type: st, member: mem, decoid: id, decoration: o }
            },
            Opcode::EntryPoint => Operation::EntryPoint
            {
                model: unsafe { std::mem::transmute(args.remove(0)) }, entry_point: args.remove(0), name: spv::parse_string(&mut args), interfaces: args
            },
            Opcode::ExecutionMode => Operation::ExecutionMode { entry_point: args.remove(0), mode: ExecutionMode::parse(&mut args) },
            Opcode::Capability => Operation::Capability { capability: unsafe { std::mem::transmute(args.remove(0)) } },
            Opcode::Variable => Operation::Variable
            {
                result_type: args.remove(0), result: args.remove(0), storage: unsafe { std::mem::transmute(args.remove(0)) },
                initializer: if !args.is_empty() { Some(args.remove(0)) } else { None }
            },
            Opcode::TypeVoid => Operation::TypeVoid { result: args.remove(0) },
            Opcode::TypeBool => Operation::TypeBool { result: args.remove(0) },
            Opcode::TypeInt => Operation::TypeInt { result: args.remove(0), width: args.remove(0), signedness: args.remove(0) != 0 },
            Opcode::TypeFloat => Operation::TypeFloat { result: args.remove(0), width: args.remove(0) },
            Opcode::TypeVector => Operation::TypeVector { result: args.remove(0), component_type: args.remove(0), component_count: args.remove(0) },
            Opcode::TypeMatrix => Operation::TypeMatrix { result: args.remove(0), column_type: args.remove(0), column_count: args.remove(0) },
            Opcode::TypeImage => Operation::TypeImage
            {
                result: args.remove(0), sampled_type: args.remove(0), dim: unsafe { std::mem::transmute(args.remove(0)) },
                depth: args.remove(0), arrayed: args.remove(0), ms: args.remove(0), sampled: args.remove(0),
                format: unsafe { std::mem::transmute(args.remove(0)) },
                qualifier: if !args.is_empty() { Some(unsafe { std::mem::transmute(args.remove(0)) }) } else { None }
            },
            Opcode::TypeSampler => Operation::TypeSampler { result: args.remove(0) },
            Opcode::TypeSampledImage => Operation::TypeSampledImage { result: args.remove(0), image_type: args.remove(0) },
            Opcode::TypeArray => Operation::TypeArray { result: args.remove(0), element_type: args.remove(0), length: args.remove(0) },
            Opcode::TypeRuntimeArray => Operation::TypeRuntimeArray { result: args.remove(0), element_type: args.remove(0) },
            Opcode::TypeStruct => Operation::TypeStruct { result: args.remove(0), member_types: args },
            Opcode::TypeOpaque => Operation::TypeOpaque { result: args.remove(0), typename: spv::parse_string(&mut args) },
            Opcode::TypePointer => Operation::TypePointer
            {
                result: args.remove(0), storage: unsafe { std::mem::transmute(args.remove(0)) }, _type: args.remove(0)
            },
            Opcode::TypeFunction => Operation::TypeFunction { result: args.remove(0), return_type: args.remove(0), parameters: args },
            Opcode::TypeEvent => Operation::TypeEvent { result: args.remove(0) },
            Opcode::TypeDeviceEvent => Operation::TypeDeviceEvent { result: args.remove(0) },
            Opcode::TypeReserveId => Operation::TypeReserveId { result: args.remove(0) },
            Opcode::TypeQueue => Operation::TypeQueue { result: args.remove(0) },
            Opcode::TypePipe => Operation::TypePipe { result: args.remove(0) },
            Opcode::TypeForwardPointer => Operation::TypeForwardPointer
            {
                pointer_type: args.remove(0), storage: unsafe { std::mem::transmute(args.remove(0)) }
            },
            Opcode::ConstantTrue => Operation::ConstantTrue { result_type: args.remove(0), result: args.remove(0) },
            Opcode::ConstantFalse => Operation::ConstantFalse { result_type: args.remove(0), result: args.remove(0) },
            Opcode::Constant => Operation::Constant { result_type: args.remove(0), result: args.remove(0), literals: args },
            Opcode::ConstantComposite => Operation::ConstantComposite { result_type: args.remove(0), result: args.remove(0), constituents: args },
            Opcode::ConstantSampler => Operation::ConstantSampler
            {
                result_type: args.remove(0), result: args.remove(0),
                addressing_mode: unsafe { std::mem::transmute(args.remove(0)) }, param: args.remove(0),
                filter_mode: unsafe { std::mem::transmute(args.remove(0)) }
            },
            Opcode::ConstantNull => Operation::ConstantNull { result_type: args.remove(0), result: args.remove(0) },
            Opcode::SpecConstantTrue => Operation::SpecConstantTrue { result_type: args.remove(0), result: args.remove(0) },
            Opcode::SpecConstantFalse => Operation::SpecConstantFalse { result_type: args.remove(0), result: args.remove(0) },
            Opcode::SpecConstant => Operation::SpecConstant { result_type: args.remove(0), result: args.remove(0), literals: args },
            Opcode::SpecConstantComposite => Operation::SpecConstantComposite { result_type: args.remove(0), result: args.remove(0), constituents: args },
            Opcode::SpecConstantOp => Operation::SpecConstantOp
            {
                result_type: args.remove(0), result: args.remove(0), op: Box::new(Operation::from_parts(unsafe { std::mem::transmute(args.remove(0) as u16) }, args))
            },
            _ => Operation::Unknown { code: code, args: args }
        }
    }
    fn is_type_op(&self) -> bool
    {
        match self
        {
            &Operation::TypeVoid { .. } | &Operation::TypeBool { .. } | &Operation::TypeInt { .. } | &Operation::TypeFloat { .. }
            | &Operation::TypeVector { .. } | &Operation::TypeMatrix { .. } | &Operation::TypeArray { .. } | &Operation::TypeRuntimeArray { .. }
            | &Operation::TypeStruct { .. } | &Operation::TypeImage { .. } | &Operation::TypeSampler { .. } | &Operation::TypeSampledImage { .. }
            | &Operation::TypePointer { .. } | &Operation::TypeOpaque { .. } | &Operation::TypeEvent { .. } | &Operation::TypeDeviceEvent { .. }
            | &Operation::TypeQueue { .. } | &Operation::TypeReserveId { .. } | &Operation::TypePipe { .. } => true,
            _ => false
        }
    }
}
#[derive(Debug, Clone)] pub enum Decoration
{
    RelaxedPrecision, SpecId(u32), Block, BufferBlock, RowMajor, ColMajor, ArrayStride(u32), MatrixStride(u32),
    GLSLShared, GLSLPacked, CPacked, BuiltIn(spv::BuiltIn), NoPerspective, Flat, Patch, Centroid, Sample, Invariant, Restrict, Aliased,
    Volatile, Constant, Coherent, NonWritable, NonReadable, Uniform, SaturatedConversion, Stream(u32),
    Location(u32), Component(u32), Index(u32), Binding(u32), DescriptorSet(u32), Offset(u32), XfbBuffer(u32), XfbStride(u32),
    FuncParamAttr(spv::FunctionParameterAttribute), FloatingPointRoundingMode(spv::RoundingMode),
    FloatingPointFastMathMode(u32), LinkageAttributes(String, spv::LinkageMode), NoContraction,
    InputAttachmentIndex(u32), Alignment(u32), OverrideCoverageNV, PassthroughNV, ViewportRelativeNV, SecondaryViewportRelativeNV(u32)
}
impl Decoration
{
    fn parse(args: &mut Vec<u32>) -> (spv::Decoration, Self)
    {
        let d = unsafe { std::mem::transmute(args.remove(0)) };
        (d, match d
        {
            spv::Decoration::RelaxedPrecision => Decoration::RelaxedPrecision,
            spv::Decoration::SpecId => Decoration::SpecId(args.remove(0)),
            spv::Decoration::Block => Decoration::Block,
            spv::Decoration::BufferBlock => Decoration::BufferBlock,
            spv::Decoration::RowMajor => Decoration::RowMajor,
            spv::Decoration::ColMajor => Decoration::ColMajor,
            spv::Decoration::ArrayStride => Decoration::ArrayStride(args.remove(0)),
            spv::Decoration::MatrixStride => Decoration::MatrixStride(args.remove(0)),
            spv::Decoration::GLSLShared => Decoration::GLSLShared,
            spv::Decoration::GLSLPacked => Decoration::GLSLPacked,
            spv::Decoration::CPacked => Decoration::CPacked,
            spv::Decoration::BuiltIn => Decoration::BuiltIn(unsafe { std::mem::transmute(args.remove(0)) }),
            spv::Decoration::NoPerspective => Decoration::NoPerspective,
            spv::Decoration::Flat => Decoration::Flat,
            spv::Decoration::Patch => Decoration::Patch,
            spv::Decoration::Centroid => Decoration::Centroid,
            spv::Decoration::Sample => Decoration::Sample,
            spv::Decoration::Invariant => Decoration::Invariant,
            spv::Decoration::Restrict => Decoration::Restrict,
            spv::Decoration::Aliased => Decoration::Aliased,
            spv::Decoration::Volatile => Decoration::Volatile,
            spv::Decoration::Constant => Decoration::Constant,
            spv::Decoration::Coherent => Decoration::Coherent,
            spv::Decoration::NonWritable => Decoration::NonWritable,
            spv::Decoration::NonReadable => Decoration::NonReadable,
            spv::Decoration::Uniform => Decoration::Uniform,
            spv::Decoration::SaturatedConversion => Decoration::SaturatedConversion,
            spv::Decoration::Stream => Decoration::Stream(args.remove(0)),
            spv::Decoration::Location => Decoration::Location(args.remove(0)),
            spv::Decoration::Component => Decoration::Component(args.remove(0)),
            spv::Decoration::Index => Decoration::Index(args.remove(0)),
            spv::Decoration::Binding => Decoration::Binding(args.remove(0)),
            spv::Decoration::DescriptorSet => Decoration::DescriptorSet(args.remove(0)),
            spv::Decoration::Offset => Decoration::Offset(args.remove(0)),
            spv::Decoration::XfbBuffer => Decoration::XfbBuffer(args.remove(0)),
            spv::Decoration::XfbStride => Decoration::XfbStride(args.remove(0)),
            spv::Decoration::FuncParamAttr => Decoration::FuncParamAttr(unsafe { std::mem::transmute(args.remove(0)) }),
            spv::Decoration::FPRoundingMode => Decoration::FloatingPointRoundingMode(unsafe { std::mem::transmute(args.remove(0)) }),
            spv::Decoration::FPFastMathMode => Decoration::FloatingPointFastMathMode(args.remove(0)),
            spv::Decoration::LinkageAttributes => Decoration::LinkageAttributes(spv::parse_string(args), unsafe { std::mem::transmute(args.remove(0)) }),
            spv::Decoration::NoContraction => Decoration::NoContraction,
            spv::Decoration::InputAttachmentIndex => Decoration::InputAttachmentIndex(args.remove(0)),
            spv::Decoration::Alignment => Decoration::Alignment(args.remove(0)),
            spv::Decoration::OverrideCoverageNV => Decoration::OverrideCoverageNV,
            spv::Decoration::PassthroughNV => Decoration::PassthroughNV,
            spv::Decoration::ViewportRelativeNV => Decoration::ViewportRelativeNV,
            spv::Decoration::SecondaryViewportRelativeNV => Decoration::SecondaryViewportRelativeNV(args.remove(0)),
            _ => unreachable!("Appeared an reserved code")
        })
    }
}
#[derive(Debug, Clone)] enum ExecutionMode
{
    Invocations(u32), SpacingEqual, SpacingFractionalEven, SpacingFractionalOdd, VertexOrderCw, VertexOrderCcw, PixelCenterInteger,
    OriginUpperLeft, OriginLowerLeft, EarlyFragmentTests, PointMode, Xfb, DepthReplacing, DepthGreater, DepthLess, DepthUnchanged,
    LocalSize(u32, u32, u32), LocalSizeHint(u32, u32, u32), InputPoints, InputLines, InputLinesAdjacency, InputTriangles, InputTrianglesAdjacency,
    Quads, Isolines, OutputVertices(u32), OutputPoints, OutputLineStrip, OutputTriangleStrip, VecTypeHint(u32), ContractionOff
}
impl ExecutionMode
{
    fn parse(args: &mut Vec<u32>) -> Self
    {
        match unsafe { std::mem::transmute(args.remove(0)) }
        {
            spv::ExecutionMode::Invocations => ExecutionMode::Invocations(args.remove(0)),
            spv::ExecutionMode::SpacingEqual => ExecutionMode::SpacingEqual,
            spv::ExecutionMode::SpacingFractionalEven => ExecutionMode::SpacingFractionalEven,
            spv::ExecutionMode::SpacingFractionalOdd => ExecutionMode::SpacingFractionalOdd,
            spv::ExecutionMode::VertexOrderCw => ExecutionMode::VertexOrderCw,
            spv::ExecutionMode::VertexOrderCcw => ExecutionMode::VertexOrderCcw,
            spv::ExecutionMode::PixelCenterInteger => ExecutionMode::PixelCenterInteger,
            spv::ExecutionMode::OriginUpperLeft => ExecutionMode::OriginUpperLeft,
            spv::ExecutionMode::OriginLowerLeft => ExecutionMode::OriginLowerLeft,
            spv::ExecutionMode::EarlyFragmentTests => ExecutionMode::EarlyFragmentTests,
            spv::ExecutionMode::PointMode => ExecutionMode::PointMode,
            spv::ExecutionMode::Xfb => ExecutionMode::Xfb,
            spv::ExecutionMode::DepthReplacing => ExecutionMode::DepthReplacing,
            spv::ExecutionMode::DepthGreater => ExecutionMode::DepthGreater,
            spv::ExecutionMode::DepthLess => ExecutionMode::DepthLess,
            spv::ExecutionMode::DepthUnchanged => ExecutionMode::DepthUnchanged,
            spv::ExecutionMode::LocalSize => ExecutionMode::LocalSize(args.remove(0), args.remove(0), args.remove(0)),
            spv::ExecutionMode::LocalSizeHint => ExecutionMode::LocalSizeHint(args.remove(0), args.remove(0), args.remove(0)),
            spv::ExecutionMode::InputPoints => ExecutionMode::InputPoints,
            spv::ExecutionMode::InputLines => ExecutionMode::InputLines,
            spv::ExecutionMode::InputLinesAdjacency => ExecutionMode::InputLinesAdjacency,
            spv::ExecutionMode::Triangles => ExecutionMode::InputTriangles,
            spv::ExecutionMode::InputTrianglesAdjacency => ExecutionMode::InputTrianglesAdjacency,
            spv::ExecutionMode::Quads => ExecutionMode::Quads,
            spv::ExecutionMode::Isolines => ExecutionMode::Isolines,
            spv::ExecutionMode::OutputVertices => ExecutionMode::OutputVertices(args.remove(0)),
            spv::ExecutionMode::OutputPoints => ExecutionMode::OutputPoints,
            spv::ExecutionMode::OutputLineStrip => ExecutionMode::OutputLineStrip,
            spv::ExecutionMode::OutputTriangleStrip => ExecutionMode::OutputTriangleStrip,
            spv::ExecutionMode::VecTypeHint => ExecutionMode::VecTypeHint(args.remove(0)),
            spv::ExecutionMode::ContractionOff => ExecutionMode::ContractionOff
        }
    }
}
