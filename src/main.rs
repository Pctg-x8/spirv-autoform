use std::io::prelude::*;
use std::io::BufReader;
use std::collections::*;
use std::borrow::Cow;

fn main()
{
    match std::env::args().nth(1)
    {
        Some(n) => std::fs::File::open(n).map(BufReader::new).map_err(From::from).and_then(parse_spirv).unwrap(),
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

struct OperationSlot { name: Option<String>, operation: Option<Operation> }
#[derive(Clone)]
enum SpirvType
{
    Void, Bool, Int(u8, bool), Float(u8), Vector(u32, Box<SpirvType>), Matrix(u32, Box<SpirvType>),
    Array(u32, Box<SpirvType>), DynamicArray(Box<SpirvType>), Pointer(spv::StorageClass, Box<SpirvType>), Structure(Vec<SpirvType>),
    Image
    {
        sampled_type: Box<SpirvType>, dim: spv::Dim, depth: u32, arrayed: u32, ms: u32, sampled: u32, format: spv::ImageFormat,
        qualifier: Option<spv::AccessQualifier>
    }, Sampler, SampledImage(Box<SpirvType>), Function(Box<SpirvType>, Vec<SpirvType>)
}
impl std::fmt::Debug for SpirvType
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
            &SpirvType::Pointer(_, ref p) => write!(fmt, "pointer of {:?}", p),
            &SpirvType::Structure(ref m) => write!(fmt, "struct {:?}", m),
            &SpirvType::Image { ref sampled_type, .. } => write!(fmt, "Image sampled with type {:?}", sampled_type),
            &SpirvType::Sampler => write!(fmt, "sampler"),
            &SpirvType::SampledImage(ref i) => write!(fmt, "sampled image of {:?}", i),
            &SpirvType::Function(ref r, ref p) => write!(fmt, "({:?}) => {:?}", p, r)
        }
    }
}
struct InputVariable<'s> { name: &'s str, _type: SpirvType, decorations: Cow<'s, [Decoration]> }

pub struct TypeAggregator(Vec<Option<Box<SpirvType>>>);
impl TypeAggregator
{
    // Public APIs //
    fn new(cap: usize) -> Self { TypeAggregator(vec![None; cap]) }
    fn lookup(&mut self, ops: &Vec<OperationSlot>, index: usize) -> &Box<SpirvType>
    {
        if self.0[index].is_none() { self.0[index] = Some(self.try_resolve(ops, ops[index].operation.as_ref().unwrap())); }
        self.0[index].as_ref().unwrap()
    }

    // Private APIs //
    fn try_resolve(&mut self, ops: &Vec<OperationSlot>, op: &Operation) -> Box<SpirvType>
    {
        Box::new(match op
        {
            &Operation::TypeVoid { .. } => SpirvType::Void,
            &Operation::TypeBool { .. } => SpirvType::Bool,
            &Operation::TypeInt { width, signedness, .. } => SpirvType::Int(width as u8, signedness == 1),
            &Operation::TypeFloat { width, .. } => SpirvType::Float(width as u8),
            &Operation::TypeVector { component_type, component_count, .. }
                => SpirvType::Vector(component_count, self.lookup(ops, component_type as usize).clone()),
            &Operation::TypeMatrix { column_type, column_count, .. } => SpirvType::Matrix(column_count, self.lookup(ops, column_type as usize).clone()),
            &Operation::TypeArray { element_type, length, .. } => SpirvType::Array(length, self.lookup(ops, element_type as usize).clone()),
            &Operation::TypeRuntimeArray { element_type, .. } => SpirvType::DynamicArray(self.lookup(ops, element_type as usize).clone()),
            &Operation::TypePointer { ref storage, _type, .. } => SpirvType::Pointer(storage.clone(), self.lookup(ops, _type as usize).clone()),
            &Operation::TypeStruct { ref member_types, .. }
                => SpirvType::Structure(member_types.iter().map(|&x| *self.lookup(ops, x as usize).clone()).collect()),
            &Operation::TypeImage { sampled_type, ref dim, depth, arrayed, ms, sampled, ref format, ref qualifier, .. } => SpirvType::Image
            {
                sampled_type: self.lookup(ops, sampled_type as usize).clone(), dim: dim.clone(), depth: depth, arrayed: arrayed, ms: ms, sampled: sampled,
                format: format.clone(), qualifier: qualifier.clone()
            },
            &Operation::TypeSampler { .. } => SpirvType::Sampler,
            &Operation::TypeSampledImage { image_type, .. } => SpirvType::SampledImage(self.lookup(ops, image_type as usize).clone()),
            &Operation::TypeFunction { return_type, ref parameters, .. } => SpirvType::Function(
                self.lookup(ops, return_type as usize).clone(), parameters.iter().map(|&x| *self.lookup(ops, x as usize).clone()).collect()),
            _ => unreachable!("Not a type: {:?}", op)
        })
    }
}

fn parse_spirv<F: Read + Seek>(mut fp: F) -> Result<(), Box<std::error::Error>>
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

    let mut type_aggregation = TypeAggregator::new(bound as usize);
    let mut operation_slots = Vec::with_capacity(bound as usize);
    for _ in 0 .. bound as usize
    {
        operation_slots.push(OperationSlot { name: None, operation: None });
    }
    let mut decorations = HashMap::new();
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
                    | Operation::TypePipe { result } => operation_slots[result as usize].operation = Some(op),
                    Operation::Variable { storage: spv::StorageClass::Input, result, .. } =>
                    {
                        // println!("!! Input Variable found! identified as {}", result);
                        operation_slots[result as usize].operation = Some(op);
                    },
                    Operation::Decorate { target, decoration } => decorations.entry(target).or_insert(Vec::new()).push(decoration),
                    Operation::Name { target, name } => operation_slots[target as usize].name = Some(name),
                    _ => ()
                }
            }
        }
    }

    let mut inputs = Vec::new();
    for (n, op) in operation_slots.iter().enumerate()
    {
        match op.name
        {
            Some(ref nm) => println!("#{}({}) => {:?}", n, nm, op.operation),
            None => println!("#{} => {:?}", n, op.operation)
        }
        if let Some(Operation::Variable { storage: spv::StorageClass::Input, result_type, .. }) = op.operation
        {
            inputs.push(InputVariable
            {
                name: op.name.as_ref().unwrap(), _type: *type_aggregation.lookup(&operation_slots, result_type as usize).clone(),
                decorations: decorations.get(&(n as u32)).map(|x| Cow::Borrowed(&x[..])).unwrap_or(Vec::new().into())
            });
        }
    }
    for (n, d) in decorations.iter()
    {
        println!("Decorations for #{}", n);
        for dec in d { println!("-- {:?}", dec); }
    }
    println!("Inputs: ");
    for n in inputs.iter()
    {
        println!("{}: {:?} {:?}", n.name, n._type, n.decorations);
    }

    Ok(())
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
#[derive(Debug)]
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
    Decorate { target: Id, decoration: Decoration },
    MemberDecorate { structure_type: Id, member: u32, decoration: Decoration },
    EntryPoint { model: spv::ExecutionModel, entry_point: Id, name: String, interfaces: Vec<Id> },
    ExecutionMode { entry_point: Id, mode: ExecutionMode },
    Capability { capability: spv::Capability },
    Variable { result: Id, result_type: Id, storage: spv::StorageClass, initializer: Option<Id> },
    TypeVoid { result: Id }, TypeBool { result: Id }, TypeInt { result: Id, width: u32, signedness: u32 },
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
    Unknown { code: spv::Opcode, args: Vec<u32> }
}
impl Operation
{
    fn from_parts(code: spv::Opcode, mut args: Vec<u32>) -> Self
    {
        use spv::Opcode;

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
            Opcode::Decorate => Operation::Decorate { target: args.remove(0), decoration: Decoration::parse(&mut args) },
            Opcode::MemberDecorate => Operation::MemberDecorate { structure_type: args.remove(0), member: args.remove(0), decoration: Decoration::parse(&mut args) },
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
            Opcode::TypeInt => Operation::TypeInt { result: args.remove(0), width: args.remove(0), signedness: args.remove(0) },
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
            _ => Operation::Unknown { code: code, args: args }
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
    fn parse(args: &mut Vec<u32>) -> Self
    {
        let m = unsafe { std::mem::transmute(args.remove(0)) };
        match m
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
        }
    }
}
#[derive(Debug)] enum ExecutionMode
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

// SPIR-V 1.0 Definitions //
mod spv
{
    #![allow(dead_code, non_camel_case_types)]

    /// Word Stream to Literal String
    pub fn parse_string(args: &mut Vec<u32>) -> String
    {
        let mut octets = Vec::new();
        for word in args.drain(..)
        {
            let (o1, o2, o3, o4) = (
                (word & 0x000000ff) as u8,
                ((word & 0x0000ff00) >>  8) as u8,
                ((word & 0x00ff0000) >> 16) as u8,
                ((word & 0xff000000) >> 24) as u8
            );
            if o1 == 0x00 { break; }
            octets.push(o1);
            if o2 == 0x00 { break; }
            octets.push(o2);
            if o3 == 0x00 { break; }
            octets.push(o3);
            if o4 == 0x00 { break; }
            octets.push(o4);
        }
        String::from_utf8(octets).unwrap()
    }

    /// 3.2 Source Language: Used by OpSource
    #[repr(u32)] #[derive(Debug)] pub enum SourceLanguage
    {
        Unknown, ESSL, GLSL, OpenCL_C, OpenCL_CPP
    }
    /// 3.3 Execution Model: Used by OpEntryPoint
    #[repr(u32)] #[derive(Debug, Clone)] pub enum ExecutionModel
    {
        Vertex, TessellationControl, TessellationEvaluation, Geometry, Fragment,
        GLCompute, Kernel
    }
    /// 3.4 Addressing Model: Used by OpMemoryModel
    #[repr(u32)] pub enum AddressingModel
    {
        Logical, Physical32, Physical64
    }
    /// 3.5 Memory Model: Used by OpMemoryModel
    #[repr(u32)] pub enum MemoryModel
    {
        Simple, GLSL450, OpenCL
    }
    /// 3.6 Execution Mode: Declare the modes an entry point will execute in. Used by OpExecutionMode
    #[repr(u32)] #[derive(Clone)] pub enum ExecutionMode
    {
        Invocations, SpacingEqual, SpacingFractionalEven, SpacingFractionalOdd, VertexOrderCw,
        VertexOrderCcw, PixelCenterInteger, OriginUpperLeft, OriginLowerLeft, EarlyFragmentTests,
        PointMode, Xfb, DepthReplacing, DepthGreater, DepthLess, DepthUnchanged,
        LocalSize, LocalSizeHint, InputPoints, InputLines, InputLinesAdjacency, Triangles,
        InputTrianglesAdjacency, Quads, Isolines, OutputVertices, OutputPoints, OutputLineStrip,
        OutputTriangleStrip, VecTypeHint, ContractionOff
    }
    /// 3.7 Storage Class: Class of storage for declared variables(does not include intermediate values).
    /// Used by OpTypePointer, OpTypeForwardPointer, OpVariable and OpGenericCastToPtrExplicit
    #[repr(u32)] #[derive(Debug, Clone)] pub enum StorageClass
    {
        UniformConstant, Input, Uniform, Output, Workgroup, CrossWorkgroup, Private, Function,
        Generic, PushConstant, AtomicCounter, Image
    }
    /// 3.8 Dim: Dimensionality of an image. Used by OpTypeImage
    #[repr(u32)] #[derive(Debug, Clone)] pub enum Dim
    {
        _1, _2, _3, Cube, Rect, Buffer, SubpassData
    }
    /// 3.9 Sampler Addressing Mode: Addressing mode for creating constant samplers.
    /// Used by OpConstantSampler
    #[repr(u32)] pub enum SamplerAddressingMode
    {
        None, ClampToEdge, Clamp, Repeat, RepeatMirrored
    }
    /// 3.10 Sampler Filter Mode: Filter mode for creating constant samplers. Used by OpConstantSampler
    #[repr(u32)] pub enum SamplerFilterMode { Nearest, Linear }
    /// 3.11 Image Format: Declarative image format. Used by OpTypeImage
    #[repr(u32)] #[derive(Debug, Clone)] pub enum ImageFormat
    {
        Unknown, Rgba32f, Rgba16f, R32f, Rgba8, Rgba8Snorm, Rg32f, Rg16f, R11fG11fB10f,
        R16f, Rgba16, Rgb10A2, Rg16, Rg8, R16, R8, Rgba16Snorm, Rg16Snorm, Rg8Snorm, R16Snorm, R8Snorm,
        Rgba32i, Rgba16i, Rgba8i, R32i, Rg32i, Rg16i, Rg8i, R16i, R8i, Rgba32ui, Rgba16ui, Rgba8ui, R32ui,
        Rgb10a2ui, Rg32ui, Rg16ui, Rg8ui, R16ui, R8ui
    }
    /// 3.12 Image Channel Order: Image channel order returned by OpImageQueryOrder
    #[repr(u32)] pub enum ImageChannelOrder
    {
        R, A, RG, RA, RGB, RGBA, BGRA, ARGB, Intensity, Luminance, Rx, RGx, RGBx, Depth, DepthStencil,
        sRGB, sRGBx, sRGBA, sBGRA, ABGR
    }
    /// 3.13 Image Channel Data Type: Image channel data type returned by OpImageQueryFormat
    #[repr(u32)] pub enum ImageChannelDataType
    {
        SnormInt8, SnormInt16, UnormInt8, UnormInt16, UnormShort565, UnormShort555,
        UnormInt101010, SignedInt8, SignedInt16, SignedInt32, UnsignedInt8, UnsignedInt16, UnsignedInt32,
        HalfFloat, Float, UnormInt24, UnormInt101010_2
    }
    /// 3.14 Image Operands: Additional operands to sampling, or getting texels from, an image.
    /// Bits that are set can indicate that another operand follows.
    /// If there are multiple following operands indicated, they are ordered: Those indicated by
    /// smaller-numbered bits appear first. At least one bit must be set (None is invalid).
    /// This value is a mask; it can be formed by combining the bits from multiple rows in the table below.
    pub const IMAGE_OPERANDS_NONE: u32 = 0x00;
    pub const IMAGE_OPERANDS_BIAS: u32 = 0x01;
    pub const IMAGE_OPERANDS_LOD: u32 = 0x02;
    pub const IMAGE_OPERANDS_GRAD: u32 = 0x04;
    pub const IMAGE_OPERANDS_CONST_OFFSET: u32 = 0x08;
    pub const IMAGE_OPERANDS_OFFSET: u32 = 0x10;
    pub const IMAGE_OPERANDS_CONST_OFFSETS: u32 = 0x20;
    pub const IMAGE_OPERANDS_SAMPLE: u32 = 0x40;
    pub const IMAGE_OPERANDS_MINLOD: u32 = 0x80;
    /// 3.15 FP Fast Math Mode: Enables fast math operations which are otherwise unsafe.
    pub const FAST_MATH_MODE_NOTNAN: u32 = 0x01;
    pub const FAST_MATH_MODE_NOTINF: u32 = 0x02;
    pub const FAST_MATH_MODE_NSZ: u32 = 0x04;
    pub const FAST_MATH_MODE_ALLOW_RECIP: u32 = 0x08;
    pub const FAST_MATH_MODE_FAST: u32 = 0x10;
    /// 3.16 FP Rounding Mode: Associate a rounding mode to a floating-point conversion instruction.
    #[repr(u32)] #[derive(Debug, Clone)] pub enum RoundingMode { RTE, RTZ, RTP, RTN }
    /// 3.17 Linkage Type: Associate a linkage type to functions or global variables. See linkage.
    #[repr(u32)] #[derive(Debug, Clone)] pub enum LinkageMode { Export, Import }
    /// 3.18 Access Qualifier: Defines the access permissions. Used by OpTypeImage and OpTypePipe.
    #[repr(u32)] #[derive(Debug, Clone)] pub enum AccessQualifier { ReadOnly, WriteOnly, ReadWrite }
    /// 3.19 Function Paramter Attribute: Adds additional information to the return type and
    /// to each parameter of a function.
    #[repr(u32)] #[derive(Debug, Clone)] pub enum FunctionParameterAttribute
    {
        Zext, Sext, ByVal, Sret, NoAlias, NoCapture, NoWrite, NoReadWrite
    }
    /// 3.20 Decoration: Used by OpDecorate and OpMemberDecorate
    #[repr(u32)] #[derive(Debug)] pub enum Decoration
    {
        RelaxedPrecision, SpecId, Block, BufferBlock, RowMajor, ColMajor, ArrayStride, MatrixStride,
        GLSLShared, GLSLPacked, CPacked, BuiltIn, Resv1, NoPerspective, Flat, Patch, Centroid, Sample,
        Invariant, Restrict, Aliased, Volatile, Constant, Coherent, NonWritable, NonReadable,
        Uniform, Resv2, SaturatedConversion, Stream, Location, Component, Index, Binding, DescriptorSet,
        Offset, XfbBuffer, XfbStride, FuncParamAttr, FPRoundingMode, FPFastMathMode, LinkageAttributes,
        NoContraction, InputAttachmentIndex, Alignment,
        OverrideCoverageNV = 5248, PassthroughNV = 5250, ViewportRelativeNV = 5252,
        SecondaryViewportRelativeNV = 5256
    }
    /// 3.21 BuiltIn: Used when Decoration is BuiltIn. Apply to either
    /// - the result <id> of the variable declaration of the built-in variable, or
    /// - a structure-type member, if the built-in is a member of a structure.
    /// As stated per entry below, these have additional semantics and constraints
    /// described by the client API.
    #[repr(u32)] #[derive(Debug, Clone)] pub enum BuiltIn
    {
        Position, PointSize, ClipDistance, CullDistance, VertexId,
        InstanceId, PrimitiveId, InvocationId, Layer, ViewportIndex, TessLevelOuter,
        TessLevelInner, TessCoord, PatchVertices, FragCoord, PointCoord, FrontFacing, SampleId,
        SamplePosition, SampleMask, FragDepth, HelperInvocation, NumWorkgroups, WorkgroupSize,
        WorkgroupId, LocalInvocationId, GlobalInvocationId, LocalInvocationIndex, WorkDim,
        GlobalSize, EnqueuedWorkgroupSize, GlobalOffset, GlobalLinearId, SubgroupSize = 36, SubgroupMaxSize,
        NumSubgroups, NumEnqueuedSubgroups, SubgroupId, SubgroupLocalInvocationId,
        VertexIndex, InstanceIndex,
        SubgroupEqMaskKHR = 4416, SubgroupGeMaskKHR, SubgroupGtMaskKHR, SubgroupLeMaskKHR,
        SubgroupLtMaskKHR,
        BaseVertex = 4424, BaseInstance, DrawIndex, DeviceIndex = 4438, ViewIndex = 4440,
        ViewportMaskNV = 5253, SecondaryPositionNV = 5257, SecondaryViewportMaskNV,
        PositionPerViewNV = 5261, ViewportMaskPerViewNV
    }
    /// 3.22 Selection Control: Used by OpSelectionMerge
    pub const SELECTION_CONTROL_FLATTEN: u32 = 0x01;
    pub const SELECTION_CONTROL_DONT_FLATTEN: u32 = 0x02;
    /// 3.23 Loop Control: Used by OpLoopMerge
    pub const LOOP_CONTROL_UNROLL: u32 = 0x01;
    pub const LOOP_CONTROL_DONT_UNROLL: u32 = 0x02;
    /// 3.24 Function Control: Used by OpFunction
    pub const FUNCTION_CONTROL_INLINE: u32 = 0x01;
    pub const FUNCTION_CONTROL_DONT_INLINE: u32 = 0x02;
    pub const FUNCTION_CONTROL_PURE: u32 = 0x04;
    pub const FUNCTION_CONTROL_CONST: u32 = 0x08;
    /// 3.25 Memory Semantics <id>
    pub const MEMORY_SEMANTICS_RELAXED: u32 = 0x00;
    pub const MEMORY_SEMANTICS_ACQUIRE: u32 = 0x02;
    pub const MEMORY_SEMANTICS_RELEASE: u32 = 0x04;
    pub const MEMORY_SEMANTICS_ACQUIRE_RELEASE: u32 = 0x08;
    pub const MEMORY_SEMANTICS_SEQUENTIALLY_CONSISTENT: u32 = 0x10;
    pub const MEMORY_SEMANTICS_UNIFORM_MEMORY: u32 = 0x40;
    pub const MEMORY_SEMANTICS_SUBGROUP_MEMORY: u32 = 0x80;
    pub const MEMORY_SEMANTICS_WORKGROUP_MEMORY: u32 = 0x100;
    pub const MEMORY_SEMANTICS_CROSS_WORKGROUP_MEMORY: u32 = 0x200;
    pub const MEMORY_SEMANTICS_ATOMIC_COUNTER_MEMORY: u32 = 0x400;
    pub const MEMORY_SEMANTICS_IMAGE_MEMORY: u32 = 0x800;
    /// 3.26 Memory Access: Memory access semantics
    pub const MEMORY_ACCESS_VOLATILE: u32 = 0x01;
    pub const MEMORY_ACCESS_ALIGNED: u32 = 0x02;
    pub const MEMORY_ACCESS_NOTEMPORAL: u32 = 0x04;
    /// 3.27 Scope <id>
    #[repr(u32)] pub enum IdScope { CrossDevice, Device, Workgroup, Subgroup, Invocation }
    /// 3.28 Group Operation: Defines the class of workgroup or subgroup operation.
    #[repr(u32)] pub enum GroupOperation { Reduce, InclusiveScan, ExclusiveScan }
    /// 3.29 Kernel Enqueue Flags: Specify when the child kernel begins execution.
    #[repr(u32)] pub enum KernelEnqueueFlags { NoWait, WaitKernel, WaitWorkGroup }
    /// 3.30 Kernel Profiling Info: Specify the profiling information to be queried.
    pub const KERNEL_PROFILING_INFO_CMD_EXEC_TIME: u32 = 0x01;
    /// 3.31 Capability
    #[repr(u32)] #[derive(Debug, Clone)] pub enum Capability
    {
        Matrix, Shader, Geometry, Tessellation, Addresses, Linkage, Kernel, Vector16, Float16Buffer,
        Float16, Float64, Int64, Int64Atomics, ImageBasic, ImageReadWrite, ImageMipmap, Pipes,
        Groups, DeviceEnqueue, LiteralSampler, AtomicStorage, Int16, TessellationPointSize,
        GeometryPointSize, ImageGatherExtended, StorageImageMultisample, UniformBufferArrayDynamicIndexing,
        SampledImageArrayDynamicIndexing, StorageBufferArrayDynamicIndexing,
        StorageImageArrayDynamicIndexing, ClipDistance, CullDistance, ImageCubeArray, SampleRateShading,
        ImageRect, SampledRect, GenericPointer, Int8, InputAttachment, SparseResidency, MinLod,
        Sampled1D, Image1D, SampledCubeArray, SampledBuffer, ImageBuffer, ImageMSArray,
        StorageImageExtendedFormats, ImageQuery, DerivativeControl, InterpolationFunction,
        TransformFeedback, GeometryStreams, StorageImageReadWithoutFormat,
        StorageImageWriteWithoutFormat, MultiViewport,
        SubgroupBallotKHR = 4423, DrawParamters = 4427,
        SubgroupVoteKHR = 4431, StorageUniformBufferBlock16 = 4433, StorageUniform16,
        StoragePushConstant16, StorageInputOutput16, DeviceGroup,
        MultiView = 4439, SampleMaskOverrideCoverageNV = 5249, GeometryShaderPassthroughNV = 5251,
        ShaderViewportIndexLayerNV = 5254, ShaderViewportMaskNV, ShaderStereoViewNV = 5259,
        PerViewAttributesNV
    }
    /// 3.32 Instructions
    #[repr(u16)] #[derive(Debug)] pub enum Opcode
    {
        Nop, Undef, SourceContinued, Source, SourceExtension, Name, MemberName, String,
        Line, NoLine = 317, Decorate = 71, MemberDecorate, DecorationGroup, GroupDecorate,
        GroupMemberDecorate, OpExtension = 10, OpExtInstImport, ExtInst,
        MemoryModel = 14, EntryPoint, ExecutionMode, Capability,
        TypeVoid = 19, TypeBool, TypeInt, TypeFloat, TypeVector, TypeMatrix, TypeImage, TypeSampler,
        TypeSampledImage, TypeArray, TypeRuntimeArray, TypeStruct, TypeOpaque, TypePointer,
        TypeFunction, TypeEvent, TypeDeviceEvent, TypeReserveId, TypeQueue, TypePipe, TypeForwardPointer,
        ConstantTrue = 41, ConstantFalse, Constant, ConstantComposite, ConstantSampler, ConstantNull,
        SpecConstantTrue = 48, SpecConstantFalse, SpecConstant, SpecConstantComposite,
        SpecConstantOp, Variable = 59, ImageTexelPointer, Load, Store, CopyMemory, CopyMemorySized,
        AccessChain, InBoundsAccessChain, PtrAccessChain, ArrayLength, GenericPtrMemSemantics,
        InBoundsPtrAccessChain, Function = 54, FunctionParameter, FunctionEnd, FunctionCall,
        SampledImage = 86, ImageSampleImplicitLod, ImageSampleExplicitLod, ImageSampleDrefImplicitLod,
        ImageSampleDrefExplicitLod, ImageSampleProjImplicitLod, ImageSampleProjExplicitLod,
        ImageSampleProjDrefImplicitLod, ImageSampleProjDrefExplicitLod, ImageFetch, ImageGather,
        ImageDrefGather, ImageRead, ImageWrite, Image, ImageQueryFormat, ImageQueryOrder,
        ImageQuerySizeLod, ImageQuerySize, ImageQueryLod, ImageQueryLevels, ImageQuerySamples,
        ImageSparseSampleImplicitLod = 305, ImageSparseSampleExplicitLod, ImageSparseSampleDrefImplicitLod,
        ImageSparseSampleDrefExplicitLod, ImageSparseSampleProjImplicitLod,
        ImageSparseSampleProjExplicitLod, ImageSparseSampleProjDrefImplicitLod,
        ImageSparseSampleProjDrefExplicitLod, ImageSparseFetch, ImageSparseGather,
        ImageSparseDrefGather, ImageSparseTexelsResident, ImageSparseRead = 320,
        ConvertFToU = 109, ConvertFToS, ConvertSToF, ConvertUToF, UConvert, SConvert, FConvert,
        QuantizeToF16, ConvertPtrToU, SatConvertSToU, SatConvertUToS, ConvertUToPtr, PtrCastToGeneric,
        GenericCastToPtr, GenericCastToPtrExplicit, Bitcast, VectorExtractDynamic = 77,
        VectorInsertDynamic, VectorShuffle, CompositeConstruct, CompositeExtract, CompositeInsert,
        CopyObject, Transpose, SNegate = 127, FNegate, IAdd, FAdd, ISub, FSub, IMul, FMul, UDiv, SDiv,
        FDiv, UMod, SRem, SMod, FRem, FMod, VectorTimesScalar, MatrixTimesScalar, VectorTimesMatrix,
        MatrixTimesVector, MatrixTimesMatrix, OuterProduct, Dot, IAddCarry, ISubBorrow,
        UMulExtended, SMulExtended, ShiftRightLogical = 194, ShiftRightArithmetic, ShiftLeftLogical,
        BitwiseOr, BirwiseXor, BitwiseAnd, Not, BitFieldInsert, BitFieldSExtract, BitFieldUExtract,
        BitReverse, BitCount, Any = 154, All, IsNan, IsInf, IsFinite, IsNormal, SignBitSet,
        LessOrGreater, Ordered, Unordered, LogicalEqual, LogicalNotEqual, LogicalOr,
        LogicalAnd, LogicalNot, Select, IEqual, INotEqual, UGreaterThan, SGreaterThan, UGreaterThanEqual,
        SGreaterThanEqual, ULessThan, SLessThan, ULessThanEqual, SLessThanEqual, FOrdEqual, FUnordEqual,
        FOrdNotEqual, FUnordNotEqual, FOrdLessThan, FUnordLessThan, FOrdGreaterThan, FUnordGreaterThan,
        FOrdLessThanEqual, FUnordLessThanEqual, FOrdGreaterThanEqual, FUnordGreaterThanEqual,
        DPdx = 207, DPdy, Fwidth, DPdxFine, DPdyFine, FwidthFine, DPdxCoarse, DPdyCoarse, FwidthCoarse,
        Phi = 245, LoopMerge, SelectionMerge, Label, Branch, BranchConditional, Switch,
        Kill, Return, ReturnValue, Unreachable, LifetimeStart, LifetimeStop,
        AtomicLoad = 227, AtomicStore, AtomicExchange, AtomicCompareExchange,
        AtomicCompareExchangeWeak, AtomicIIncrement, AtomicIDecrement, AtomcIAdd, AtomicISub,
        AtomicSMin, AtomicUMin, AtomicSMax, AtomicUMax, AtomicAnd, AtomicOr, AtomicXor,
        AtomicFlagTestAndSet = 318, AtomicFlagClear, EmitVertex = 218, EndPrimitive,
        EmitStreamVertex, EndStreamPrimitive, ControlBarrier = 224, MemoryBarrier,
        GroupAsyncCopy = 259, GroupWaitEvents, GroupAll, GroupAny, GroupBroadcast, GroupIAdd, GroupFAdd,
        GroupFMin, GroupUMin, GroupSMin, GroupFMax, GroupUMax, GroupSMax,
        SubgroupBallotKHR = 4421, SubgroupFirstInvocationKHR = 4422, SubgroupReadInvocationKHR = 4432,
        EnqueueMarker = 291, EnqueueKernel, GetKernelNDrangeSubGroupCount, GetKernelNDrangeMaxSubGroupSize,
        GetKernelWorkGroupSize, GetKernelPreferredWorkGroupSizeMultiple, RetainEvent, ReleaseEvent,
        CreateUserEvent, IsValidEvent, SetUserEventStatus, CaptureEventProfilingInfo, GetDefaultQueue,
        BuildNDrange, ReadPipe = 274, WritePipe, ReservedReadPipe, ReservedWritePipe,
        ReserveReadPipePackets, ReserveWritePipePackets, CommitReadPipe, CommitWritePipe,
        IsValidReserveId, GetNumPipePackets, GetMaxPipePackets, GroupReserveReadPipePackets,
        GroupReserveWritePipePackets, GroupCommitReatPipe, GroupCommitWritePipe
    }
}
