//! SPIR-V Module Loader

use std;
use std::io::prelude::*;
use spvdefs as spv;
use spvdefs::Id;
use std::collections::BTreeMap;
use container_ext::AutosizeVec;

struct WordStream<Source: Read + Seek>
{
	src: Source, require_conversion: bool
}
impl<Source: Read + Seek> WordStream<Source>
{
	pub fn read(&mut self) -> std::io::Result<u32>
	{
		let mut word: u32 = 0;
		self.src.read_exact(unsafe { std::mem::transmute::<_, &mut [u8; 4]>(&mut word) })
			.map(|_| if self.require_conversion { word.swap_bytes() } else { word })
	}
	pub fn skip_reserved(&mut self) -> std::io::Result<()>
	{
		self.src.seek(std::io::SeekFrom::Current(4)).map(|_| ())
	}
}
#[derive(Debug)]
pub enum SpirvReadError
{
	InvalidMagic
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
pub struct DecorationList(BTreeMap<spv::Decoration, Decoration>);
impl DecorationList
{
    pub fn new() -> Self { DecorationList(BTreeMap::new()) }
    pub fn register(&mut self, id: spv::Decoration, dec: Decoration)
    {
        if self.0.contains_key(&id) { println!("Warn: Duplicating Decoration {:?}", dec); }
        else { self.0.insert(id, dec); }
    }
    pub fn iter(&self) -> std::collections::btree_map::Iter<spv::Decoration, Decoration> { self.0.iter() }
    pub fn get(&self, id: spv::Decoration) -> Option<&Decoration> { self.0.get(&id) }
}
impl Default for DecorationList { fn default() -> Self { Self::new() } }
pub type DecorationMap = BTreeMap<Id, DecorationList>;
pub type MemberDecorationMap = BTreeMap<Id, AutosizeVec<DecorationList>>;
pub struct DecorationMaps { pub toplevel: DecorationMap, pub member: MemberDecorationMap }

enum OperandParsingResult { Term, Continue(Operation), Error(Box<std::error::Error>) }
macro_rules! try_op
{
	($e: expr) => { match $e { Ok(x) => x, Err(e) => return OperandParsingResult::Error(e.into()) } }
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
		let rc = try!(Self::load_magic(&mut fp));
		let mut stream = WordStream { src: fp, require_conversion: rc };

		let (v_major, v_minor) = try!(stream.read().map(Self::deconstruct_version));
		let genmagic = try!(stream.read());
		let bound = try!(stream.read());
		try!(stream.skip_reserved());

		// Parse Module, collect decorations and names
		let mut operations = Vec::new();
		let mut decorations = DecorationMaps { toplevel: DecorationMap::new(), member: MemberDecorationMap::new() };
		let mut names = NameMaps { toplevel: NameMap::new(), member: MemberNameMap::new() };
		loop
		{
			match Self::parse_op(&mut stream)
			{
				OperandParsingResult::Term => break,
				OperandParsingResult::Error(e) => return Err(e),
				OperandParsingResult::Continue(op) =>
				{
					match op
					{
						Operation::Decorate { target, decoid, decoration }
							=> decorations.toplevel.entry(target).or_insert_with(DecorationList::new).register(decoid, decoration),
						Operation::MemberDecorate { structure_type, member, decoid, decoration }
							=> decorations.member.entry(structure_type).or_insert_with(AutosizeVec::new).entry_or(member as usize, DecorationList::new)
							.register(decoid, decoration),
						Operation::Name { target, name }
							=> { names.toplevel.entry(target).or_insert(name); },
						Operation::MemberName { _type, member, name }
							=> names.member.entry(_type).or_insert_with(AutosizeVec::new).set(member as usize, name),
						_ => operations.push(op)
					}
				}
			}
		}

		Ok(SpirvModule
		{
			version: (v_major, v_minor), generator_magic: genmagic, id_range: 0 .. bound, operations: operations, names: names, decorations: decorations
		})
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

	fn load_magic<F: Read>(fp: &mut F) -> Result<bool, Box<std::error::Error>>
	{
		let mut magic: u32 = 0;
		fp.read_exact(unsafe { std::mem::transmute::<_, &mut [u8; 4]>(&mut magic) }).map_err(From::from).and_then(|_| match magic
		{
			0x07230203 => Ok(false),
			0x03022307 => Ok(true),
			_ => Err(From::from(SpirvReadError::InvalidMagic))
		})
	}
	fn deconstruct_version(v: u32) -> (u8, u8)
	{
		(((v & 0x00ff0000) >> 16) as u8, ((v & 0x0000ff00) >> 8) as u8)
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
}
struct Operand { word_count: u16, opcode: spv::Opcode }
impl std::convert::From<u32> for Operand
{
    fn from(v: u32) -> Self
    {
        Operand { word_count: (v >> 16) as u16, opcode: unsafe { std::mem::transmute(v as u16) } }
    }
}

// Semantic SPIR-V object definition
#[derive(Debug, Clone)]
pub enum Operation
{
    Nop, Undef { result: Id, result_type: Id }, MemoryModel { addressing: spv::AddressingModel, memory: spv::MemoryModel },
    ExtInstImport { result: Id, name: String },
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
            Opcode::OpExtInstImport =>
            {
                let result = args.remove(0);
                Operation::ExtInstImport { result, name: spv::parse_string(&mut args) }
            },
            Opcode::MemoryModel => Operation::MemoryModel { addressing: args[0].into(), memory: args[1].into() },
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
	pub fn result_id(&self) -> Option<Id>
	{
		match self
		{
			&Operation::Undef { result, .. } | &Operation::Variable { result, .. } | &Operation::ExtInstImport { result, .. } |
			&Operation::TypeVoid { result } | &Operation::TypeBool { result } | &Operation::TypeInt { result, .. } | &Operation::TypeFloat { result, .. } |
			&Operation::TypeSampler { result, .. } | &Operation::TypeImage { result, .. } | &Operation::TypeSampledImage { result, .. } |
			&Operation::TypeArray { result, .. } | &Operation::TypeRuntimeArray { result, .. } | &Operation::TypeVector { result, .. } |
			&Operation::TypeMatrix { result, ..  } | &Operation::TypePointer { result, .. } | &Operation::TypeOpaque { result, .. } |
			&Operation::TypeFunction { result, .. } | &Operation::TypeEvent { result, .. } | &Operation::TypeDeviceEvent { result, .. } |
			&Operation::TypeReserveId { result, .. } | &Operation::TypeQueue { result, .. } | &Operation::TypePipe { result, .. } |
			&Operation::TypeStruct { result, .. } |
			&Operation::ConstantTrue { result, .. } | &Operation::ConstantFalse { result, .. } | &Operation::Constant { result, .. } |
			&Operation::ConstantSampler { result, .. }| &Operation::ConstantNull { result, .. } | &Operation::ConstantComposite { result, .. } |
			&Operation::SpecConstant { result, .. } | &Operation::SpecConstantTrue { result, .. } | &Operation::SpecConstantFalse { result, .. } |
			&Operation::SpecConstantOp { result, .. } | &Operation::SpecConstantComposite { result, .. } => Some(result),
			_ => None
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
