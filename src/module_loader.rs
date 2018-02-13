//! SPIR-V Module Loader

use std;
use std::io::prelude::*;
use std::io::{SeekFrom, Result as IOResult, ErrorKind as IOErrorKind};
use spvdefs as spv;
use spvdefs::Id;
use std::collections::BTreeMap;
use container_ext::AutosizeVec;
use std::fmt::{Formatter, Display, Result as FmtResult};

struct WordStream<Source: Read + Seek> { src: Source, require_conversion: bool }
impl<Source: Read + Seek> WordStream<Source>
{
	fn read(&mut self) -> IOResult<u32>
	{
		let mut word: u32 = 0;
		self.src.read_exact(unsafe { std::mem::transmute::<_, &mut [u8; 4]>(&mut word) }).map(|_| if self.require_conversion { word.swap_bytes() } else { word })
	}
	fn skip_reserved(&mut self) -> IOResult<()> { self.src.seek(SeekFrom::Current(4)).map(drop) }
}

struct OpExtractor<Src: Read + Seek>(WordStream<Src>);
impl<Src: Read + Seek> From<WordStream<Src>> for OpExtractor<Src> { fn from(s: WordStream<Src>) -> Self { OpExtractor(s) } }
impl<Src: Read + Seek> Iterator for OpExtractor<Src>
{
    type Item = IOResult<Operation>;
    fn next(&mut self) -> Option<IOResult<Operation>>
    {
        match self.0.read().map(Operand::from)
        {
            Ok(op) =>
            {
                let mut opargs = Vec::with_capacity(op.word_count as usize - 1);
                for _ in 0 .. opargs.capacity() { opargs.push(match self.0.read() { Ok(v) => v, Err(e) => return Some(Err(e)) }); }
                Some(Ok(Operation::from_parts(op.opcode, opargs)))
            },
            Err(ref e) if e.kind() == IOErrorKind::UnexpectedEof => None, Err(e) => Some(Err(e))
        }
    }
}
#[derive(Debug)]
pub enum SpirvReadError { InvalidMagic }
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
			&SpirvReadError::InvalidMagic => "Invalid Magic Number"
		}
	}
	fn cause(&self) -> Option<&std::error::Error> { None }
}

// Names and Decorations collection
pub type NameMap = BTreeMap<Id, String>;
pub type MemberNameMap = BTreeMap<Id, AutosizeVec<String>>;
pub struct NameMaps { pub toplevel: NameMap, pub member: MemberNameMap }
#[derive(Clone)]
pub struct DecorationSet(BTreeMap<spv::Decoration, Decoration>);
impl DecorationSet
{
    pub fn new() -> Self { DecorationSet(BTreeMap::new()) }
    pub fn register(&mut self, id: spv::Decoration, dec: Decoration)
    {
        if self.0.contains_key(&id) { println!("Warn: Duplicating Decoration {:?}", dec); }
        else { self.0.insert(id, dec); }
    }
    pub fn iter(&self) -> std::collections::btree_map::Iter<spv::Decoration, Decoration> { self.0.iter() }
    pub fn get(&self, id: spv::Decoration) -> Option<&Decoration> { self.0.get(&id) }

    pub fn location(&self) -> Option<u32> { if let Some(&Decoration::Location(l)) = self.get(spv::Decoration::Location) { Some(l) } else { None } }
    pub fn builtin(&self) -> Option<spv::BuiltIn> { if let Some(&Decoration::BuiltIn(b)) = self.get(spv::Decoration::BuiltIn) { Some(b) } else { None } }
    pub fn input_attachment_index(&self) -> Option<u32>
    {
        if let Some(&Decoration::InputAttachmentIndex(n)) = self.get(spv::Decoration::InputAttachmentIndex) { Some(n) } else { None }
    }
    pub fn descriptor_bound_index(&self) -> Option<u32> { if let Some(&Decoration::Binding(n)) = self.get(spv::Decoration::Binding) { Some(n) } else { None } }
    pub fn descriptor_set_index(&self) -> Option<u32>
    {
        if let Some(&Decoration::DescriptorSet(n)) = self.get(spv::Decoration::DescriptorSet) { Some(n) } else { None }
    }
    pub fn array_index(&self) -> Option<u32> { if let Some(&Decoration::Index(n)) = self.get(spv::Decoration::Index) { Some(n) } else { None } }
    pub fn offset(&self) -> Option<u32> { if let Some(&Decoration::Offset(n)) = self.get(spv::Decoration::Offset) { Some(n) } else { None } }
    pub fn spec_id(&self) -> Option<u32> { if let Some(&Decoration::SpecId(n)) = self.get(spv::Decoration::SpecId) { Some(n) } else { None } }
}
impl Default for DecorationSet { fn default() -> Self { Self::new() } }
pub type DecorationMap = BTreeMap<Id, DecorationSet>;
pub type MemberDecorationMap = BTreeMap<Id, AutosizeVec<DecorationSet>>;
pub struct DecorationMaps { pub toplevel: DecorationMap, pub member: MemberDecorationMap }
impl NameMaps
{
    pub fn lookup_in_toplevel(&self, id: Id) -> Option<&str> { self.toplevel.get(&id).map(|x| x as &str) }
    pub fn lookup_member(&self, id: Id, index: usize) -> Option<&str> { self.member.get(&id).and_then(|mn| mn.get(index)).map(|x| x as &str) }

    pub fn find_toplevel_id(&self, name: &str) -> Option<Id> { self.toplevel.iter().find(|&(_, n)| n == name).map(|(&id, _)| id) }
}
impl DecorationMaps
{
    pub fn lookup_in_toplevel(&self, id: Id) -> Option<&DecorationSet> { self.toplevel.get(&id) }
    pub fn lookup_member(&self, id: Id, index: usize) -> Option<&DecorationSet> { self.member.get(&id).and_then(|mn| mn.get(index)) }
}
impl Display for DecorationSet
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult { write!(fmt, "{}", self.0.iter().map(|(_, x)| format!("{:?}", x)).collect::<Vec<_>>().join("|")) }
}

pub struct SpirvModule
{
	pub version: (u8, u8), pub generator_magic: u32, pub id_range: std::ops::Range<u32>,
	pub operations: Vec<Operation>, pub names: NameMaps, pub decorations: DecorationMaps
}
impl SpirvModule
{
	pub fn load<F: Read + Seek>(mut fp: F) -> Result<Self, Box<std::error::Error>>
	{
        let mut stream = WordStream { require_conversion: Self::load_magic(&mut fp)?, src: fp };
        let version = stream.read().map(Self::deconstruct_version)?;
        let genmagic = stream.read()?;
        let bound = stream.read()?;
        stream.skip_reserved()?;

		// Parse Module, collect decorations and names
		let mut operations = Vec::new();
		let mut decorations = DecorationMaps { toplevel: DecorationMap::new(), member: MemberDecorationMap::new() };
		let mut names = NameMaps { toplevel: NameMap::new(), member: MemberNameMap::new() };
        for op in OpExtractor::from(stream)
		{
            match op?
            {
                Operation::Decorate { target, decoid, decoration }
                    => decorations.toplevel.entry(target).or_insert_with(DecorationSet::new).register(decoid, decoration),
                Operation::MemberDecorate { structure_type, member, decoid, decoration }
                    => decorations.member.entry(structure_type).or_insert_with(AutosizeVec::new).entry_or(member as _, DecorationSet::new).register(decoid, decoration),
                Operation::Name(target, name) => { names.toplevel.entry(target).or_insert(name); },
                Operation::MemberName(target, member, name) => names.member.entry(target).or_insert_with(AutosizeVec::new).set(member as _, name),
                op => operations.push(op)
            }
		}

		Ok(SpirvModule { version, generator_magic: genmagic, id_range: 0 .. bound, operations, names, decorations })
	}
	pub fn dump(&self)
	{
		println!("# SPIR-V Module");
		println!("- Version: {}.{}", self.version.0, self.version.1);
		println!("- Generator Magic: {:08x}", self.generator_magic);
		println!("- ID Range: {:?}", self.id_range);
		println!("- Operations");
		for o in &self.operations { println!("-- {:?}", o); }
		println!("- Names");
		for (x, n) in &self.names.toplevel { println!("-- {} = {}", x, n); }
		for (x, m) in &self.names.member { for (y, n) in m.iter().enumerate() { println!("-- {}::{} = {}", x, y, n); } }
		println!("- Decorations");
		for (x, n) in &self.decorations.toplevel { for (did, d) in n.iter() { println!("-- {}.{:?} = {:?}", x, did, d); } }
		for (x, m) in &self.decorations.member { for (y, n) in m.iter().enumerate() { for (did, d) in n.iter() { println!("-- {}::{}.{:?} = {:?}", x, y, did, d); } } }
	}

    /// return: whether requiring swapping an endian / error
	fn load_magic<F: Read>(fp: &mut F) -> Result<bool, Box<std::error::Error>>
	{
		let mut magic: u32 = 0;
		fp.read_exact(unsafe { std::mem::transmute::<_, &mut [u8; 4]>(&mut magic) })?;
        match magic
		{
			0x07230203 => Ok(false), 0x03022307 => Ok(true), _ => Err(SpirvReadError::InvalidMagic.into())
		}
	}
	fn deconstruct_version(v: u32) -> (u8, u8) { (((v & 0x00ff0000) >> 16) as _, ((v & 0x0000ff00) >> 8) as _) }
}
struct Operand { word_count: u16, opcode: spv::Opcode }
impl From<u32> for Operand
{
    fn from(v: u32) -> Self
    {
        Operand { word_count: (v >> 16) as u16, opcode: unsafe { std::mem::transmute(v as u16) } }
    }
}

#[derive(Debug, Clone, Copy)] pub struct TypedResult { pub ty: Id, pub id: Id }
// Semantic SPIR-V object definition
#[derive(Debug, Clone)]
pub enum Operation
{
    Nop, Undef(TypedResult), MemoryModel { addressing: spv::AddressingModel, memory: spv::MemoryModel },
    ExtInstImport(Id, String), ExtInst { result: TypedResult, import_set: Id, instruction: u32, operands: Vec<Id> },
    SourceContinued(String), SourceExtension(String),
    Source { language: spv::SourceLanguage, version: u32, file_id: Option<Id>, source: Option<String> },
    Name(Id, String), MemberName(Id, u32, String), String(Id, String),
    Line { file_id: Id, line: u32, column: u32 }, NoLine,
    Decorate { target: Id, decoid: spv::Decoration, decoration: Decoration },
    MemberDecorate { structure_type: Id, member: u32, decoid: spv::Decoration, decoration: Decoration },
    EntryPoint { model: spv::ExecutionModel, entry_point: Id, name: String, interfaces: Vec<Id> },
    ExecutionMode { entry_point: Id, mode: ExecutionMode },
    Capability(spv::Capability),
    Variable { result: TypedResult, storage: spv::StorageClass, initializer: Option<Id> },
    TypeVoid(Id), TypeBool(Id), TypeInt { result: Id, width: u32, signedness: bool }, TypeFloat { result: Id, width: u32 },
    TypeVector { result: Id, component_ty: Id, count: u32 }, TypeMatrix { result: Id, col_ty: Id, count: u32 },
    TypeImage
    {
        result: Id, sampled_type: Id, dim: spv::Dim, depth: u32, arrayed: u32, ms: u32, sampled: u32, format: spv::ImageFormat,
        qualifier: Option<spv::AccessQualifier>
    },
    TypeSampler(Id), TypeSampledImage { result: Id, image_ty: Id }, TypeArray { result: Id, elm_ty: Id, length: Id },
    TypeRuntimeArray { result: Id, element_type: Id }, TypeStruct { result: Id, member_types: Vec<Id> },
    TypeOpaque { result: Id, typename: String }, TypePointer { result: Id, storage: spv::StorageClass, _type: Id },
    TypeFunction { result: Id, return_type: Id, parameters: Vec<Id> },
    TypeEvent(Id), TypeDeviceEvent(Id), TypeReserveId(Id), TypeQueue(Id), TypePipe(Id), TypeForwardPointer { pointer_type: Id, storage: spv::StorageClass },
    ConstantTrue(TypedResult), ConstantFalse(TypedResult), Constant { result: TypedResult, literals: Vec<u32> }, ConstantComposite { result: TypedResult, constituents: Vec<Id> },
    ConstantSampler { result: TypedResult, addressing_mode: spv::SamplerAddressingMode, param: u32, filter_mode: spv::SamplerFilterMode },
    ConstantNull(TypedResult),
    SpecConstantTrue(TypedResult), SpecConstantFalse(TypedResult), SpecConstant { result: TypedResult, literals: Vec<u32> },
    SpecConstantComposite { result: TypedResult, constituents: Vec<Id> }, SpecConstantOp { result: TypedResult, op: Box<Operation> },
    Function { result: TypedResult, control: u32, fnty: Id }, Return, ReturnValue(Id), FunctionEnd,
    Load { result: TypedResult, from_ptr: Id, memory_access: u32 }, Store { into_ptr: Id, from_ptr: Id, memory_access: u32 },
    AccessChain { result: TypedResult, base: Id, indices: Vec<Id> },
    FMul { result: TypedResult, ops: [Id; 2] },
    CompositeConstruct { result: TypedResult, constituents: Vec<Id> },
    Unknown { code: spv::Opcode, args: Vec<u32> }
}
impl Operation
{
    fn from_parts(code: spv::Opcode, mut args: Vec<u32>) -> Self
    {
        use self::spv::Opcode::*;

        match code
        {
            Nop => Operation::Nop,
            OpExtInstImport =>
            {
                let result = args.remove(0);
                Operation::ExtInstImport(result, spv::decode_string(&mut args))
            },
            ExtInst =>
            {
                let result = TypedResult { ty: args.remove(0), id: args.remove(0) };
                let import_set = args.remove(0); let instruction = args.remove(0);
                Operation::ExtInst { result, import_set, instruction, operands: args }
            },
            MemoryModel => Operation::MemoryModel { addressing: args[0].into(), memory: args[1].into() },
            Undef => Operation::Undef(TypedResult { ty: args[0], id: args[1] }),
            SourceContinued => Operation::SourceContinued(spv::decode_string(&mut args)),
            Source =>
            {
                let lang = args.remove(0); let ver = args.remove(0);
                let file_ref = if !args.is_empty() { Some(args.remove(0)) } else { None };
                let source_str = if !args.is_empty() { Some(spv::decode_string(&mut args)) } else { None };
                Operation::Source { language: unsafe { std::mem::transmute(lang) }, version: ver, file_id: file_ref, source: source_str }
            },
            SourceExtension => Operation::SourceExtension(spv::decode_string(&mut args)),
            Name => Operation::Name(args.remove(0), spv::decode_string(&mut args)),
            MemberName => Operation::MemberName(args.remove(0), args.remove(0), spv::decode_string(&mut args)),
            String => Operation::String(args.remove(0), spv::decode_string(&mut args)),
            Line => Operation::Line { file_id: args[0], line: args[1], column: args[2] }, NoLine => Operation::NoLine,
            Decorate =>
            {
                let t = args.remove(0);
                let (id, o) = Decoration::parse(&mut args);
                Operation::Decorate { target: t, decoid: id, decoration: o }
            },
            MemberDecorate =>
            {
                let (st, mem) = (args.remove(0), args.remove(0));
                let (id, o) = Decoration::parse(&mut args);
                Operation::MemberDecorate { structure_type: st, member: mem, decoid: id, decoration: o }
            },
            EntryPoint => Operation::EntryPoint { model: args.remove(0).into(), entry_point: args.remove(0), name: spv::decode_string(&mut args), interfaces: args },
            ExecutionMode => Operation::ExecutionMode { entry_point: args.remove(0), mode: self::ExecutionMode::parse(&mut args) },
            Capability => Operation::Capability(unsafe { std::mem::transmute(args[0]) }),
            Variable => Operation::Variable
            {
                result: TypedResult { ty: args.remove(0), id: args.remove(0) }, storage: args.remove(0).into(),
                initializer: if !args.is_empty() { Some(args.remove(0)) } else { None }
            },
            TypeVoid => Operation::TypeVoid(args[0]), TypeBool => Operation::TypeBool(args[0]),
            TypeInt => Operation::TypeInt { result: args[0], width: args[1], signedness: args[2] != 0 },
            TypeFloat => Operation::TypeFloat { result: args[0], width: args[1] },
            TypeVector => Operation::TypeVector { result: args[0], component_ty: args[1], count: args[2] },
            TypeMatrix => Operation::TypeMatrix { result: args[0], col_ty: args[1], count: args[2] },
            TypeImage => Operation::TypeImage
            {
                result: args.remove(0), sampled_type: args.remove(0), dim: unsafe { std::mem::transmute(args.remove(0)) },
                depth: args.remove(0), arrayed: args.remove(0), ms: args.remove(0), sampled: args.remove(0),
                format: unsafe { std::mem::transmute(args.remove(0)) },
                qualifier: if !args.is_empty() { Some(unsafe { std::mem::transmute(args.remove(0)) }) } else { None }
            },
            TypeSampler => Operation::TypeSampler(args[0]), TypeSampledImage => Operation::TypeSampledImage { result: args[0], image_ty: args[1] },
            TypeArray => Operation::TypeArray { result: args[0], elm_ty: args[1], length: args[2] },
            TypeRuntimeArray => Operation::TypeRuntimeArray { result: args.remove(0), element_type: args.remove(0) },
            TypeStruct => Operation::TypeStruct { result: args.remove(0), member_types: args },
            TypeOpaque => Operation::TypeOpaque { result: args.remove(0), typename: spv::decode_string(&mut args) },
            TypePointer => Operation::TypePointer
            {
                result: args.remove(0), storage: unsafe { std::mem::transmute(args.remove(0)) }, _type: args.remove(0)
            },
            TypeFunction => Operation::TypeFunction { result: args.remove(0), return_type: args.remove(0), parameters: args },
            TypeEvent => Operation::TypeEvent(args[0]), TypeDeviceEvent => Operation::TypeDeviceEvent(args[0]),
            TypeReserveId => Operation::TypeReserveId(args[0]), TypeQueue => Operation::TypeQueue(args[0]), TypePipe => Operation::TypePipe(args[0]),
            TypeForwardPointer => Operation::TypeForwardPointer { pointer_type: args.remove(0), storage: unsafe { std::mem::transmute(args.remove(0)) } },
            ConstantTrue => Operation::ConstantTrue(TypedResult { ty: args[0], id: args[1] }),
            ConstantFalse => Operation::ConstantFalse(TypedResult { ty: args[0], id: args[1] }),
            Constant => Operation::Constant { result: TypedResult { ty: args.remove(0), id: args.remove(0) }, literals: args },
            ConstantComposite => Operation::ConstantComposite { result: TypedResult { ty: args.remove(0), id: args.remove(0) }, constituents: args },
            ConstantSampler => Operation::ConstantSampler
            {
                result: TypedResult { ty: args[0], id: args[1] }, addressing_mode: args[2].into(), param: args[3], filter_mode: args[4].into()
            },
            ConstantNull => Operation::ConstantNull(TypedResult { ty: args[0], id: args[1] }),
            SpecConstantTrue => Operation::SpecConstantTrue(TypedResult { ty: args[0], id: args[1] }),
            SpecConstantFalse => Operation::SpecConstantFalse(TypedResult { ty: args[0], id: args[1] }),
            SpecConstant => Operation::SpecConstant { result: TypedResult { ty: args.remove(0), id: args.remove(0) }, literals: args },
            SpecConstantComposite => Operation::SpecConstantComposite { result: TypedResult { ty: args.remove(0), id: args.remove(0) }, constituents: args },
            SpecConstantOp => Operation::SpecConstantOp
            {
                result: TypedResult { ty: args.remove(0), id: args.remove(0) }, op: Box::new(Operation::from_parts(unsafe { std::mem::transmute(args.remove(0) as u16) }, args))
            },
            Function => Operation::Function { result: TypedResult { ty: args[0], id: args[1] }, control: args[2], fnty: args[3] },
            Return => Operation::Return, FunctionEnd => Operation::FunctionEnd, ReturnValue => Operation::ReturnValue(args[0]),
            Load => Operation::Load { result: TypedResult { ty: args[0], id: args[1] }, from_ptr: args[2], memory_access: args.get(3).map(|&x| x).unwrap_or(0) },
            Store => Operation::Store { into_ptr: args[0], from_ptr: args[1], memory_access: args.get(2).map(|&x| x).unwrap_or(0) },
            AccessChain =>
            {
                let result = TypedResult { ty: args.remove(0), id: args.remove(0) };
                let base = args.remove(0);
                Operation::AccessChain { result, base, indices: args }
            },
            FMul => Operation::FMul { result: TypedResult { ty: args[0], id: args[1] }, ops: [args[2], args[3]] },
            CompositeConstruct => Operation::CompositeConstruct { result: TypedResult { ty: args.remove(0), id: args.remove(0) }, constituents: args },
            _ => Operation::Unknown { code, args }
        }
    }

    pub fn is_type_op(&self) -> bool
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
	pub fn is_constant_op(&self) -> bool
	{
		match self
		{
			&Operation::Constant { .. } | &Operation::ConstantTrue { .. } | &Operation::ConstantFalse { .. } |
			&Operation::ConstantComposite { .. } | &Operation::ConstantSampler { .. } | &Operation::ConstantNull { .. } |
			&Operation::SpecConstant { .. } | &Operation::SpecConstantTrue { .. } | &Operation::SpecConstantFalse { .. } |
			&Operation::SpecConstantOp { .. } | &Operation::SpecConstantComposite { .. } => true,
			_ => false
		}
	}
    /// id of value, id of type, ref to self
    pub fn strip_constant_result(&self) -> Option<(&TypedResult, &Self)>
    {
		match *self
		{
			Operation::Constant { ref result, .. } | Operation::ConstantTrue(ref result) | Operation::ConstantFalse(ref result) | Operation::ConstantNull(ref result) |
            Operation::ConstantComposite { ref result, .. } | Operation::ConstantSampler { ref result, .. } |
            Operation::SpecConstant { ref result, .. } | Operation::SpecConstantTrue(ref result) | Operation::SpecConstantFalse(ref result) |
            Operation::SpecConstantComposite { ref result, .. } | Operation::SpecConstantOp { ref result, .. } => Some((result, self)),
			_ => None
		}
    }
	pub fn result_id(&self) -> Option<Id>
	{
        use self::Operation::*;

		match *self
		{
			ExtInstImport(result, _) | Name(result, _) | String(result, _) |
			TypeVoid(result) | TypeBool(result) | TypeInt { result, .. } | TypeFloat { result, .. } |
			TypeSampler(result) | TypeImage { result, .. } | TypeSampledImage { result, .. } |
			TypeArray { result, .. } | TypeRuntimeArray { result, .. } | TypeVector { result, .. } |
			TypeMatrix { result, ..  } | TypePointer { result, .. } | TypeOpaque { result, .. } |
			TypeFunction { result, .. } | TypeEvent(result) | TypeDeviceEvent(result) | TypeReserveId(result) | TypeQueue(result) | TypePipe(result) |
			TypeStruct { result, .. } => Some(result),
            Undef(ref result) | Variable { ref result, .. } | ConstantTrue(ref result) | ConstantFalse(ref result) | Constant { ref result, .. } |
            ConstantSampler { ref result, .. } | ConstantNull(ref result) |
            SpecConstantTrue(ref result) | SpecConstantFalse(ref result) | SpecConstant { ref result, .. } |
            SpecConstantComposite { ref result, .. } | SpecConstantOp { ref result, .. } => Some(result.id),
			_ => None
		}
	}
    pub fn result_type(&self) -> Option<Id> { self.strip_constant_result().map(|(r, _)| r.ty) }
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
            spv::Decoration::LinkageAttributes => Decoration::LinkageAttributes(spv::decode_string(args), unsafe { std::mem::transmute(args.remove(0)) }),
            spv::Decoration::NoContraction => Decoration::NoContraction,
            spv::Decoration::InputAttachmentIndex => Decoration::InputAttachmentIndex(args.remove(0)),
            spv::Decoration::Alignment => Decoration::Alignment(args.remove(0)),
            spv::Decoration::OverrideCoverageNV => Decoration::OverrideCoverageNV,
            spv::Decoration::PassthroughNV => Decoration::PassthroughNV,
            spv::Decoration::ViewportRelativeNV => Decoration::ViewportRelativeNV,
            spv::Decoration::SecondaryViewportRelativeNV => Decoration::SecondaryViewportRelativeNV(args.remove(0)),
            _ => unreachable!("Appeared a reserved code")
        })
    }
}
#[derive(Debug, Clone)] pub enum ExecutionMode
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
