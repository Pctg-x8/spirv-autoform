
//! SPIR-V 1.0 Definitions
#![allow(dead_code, non_camel_case_types)]

pub type Id = u32;

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
#[repr(u32)] #[derive(Debug, Clone)] pub enum SourceLanguage
{
	Unknown, ESSL, GLSL, OpenCL_C, OpenCL_CPP
}
/// 3.3 Execution Model: Used by OpEntryPoint
#[repr(u32)] #[derive(Debug, Clone, Copy)] pub enum ExecutionModel
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
	PointMode, Xfb, DepthReplacing, DepthGreater = 14, DepthLess, DepthUnchanged,
	LocalSize, LocalSizeHint, InputPoints, InputLines, InputLinesAdjacency, Triangles,
	InputTrianglesAdjacency, Quads, Isolines, OutputVertices, OutputPoints, OutputLineStrip,
	OutputTriangleStrip, VecTypeHint, ContractionOff
}
/// 3.7 Storage Class: Class of storage for declared variables(does not include intermediate values).
/// Used by OpTypePointer, OpTypeForwardPointer, OpVariable and OpGenericCastToPtrExplicit
#[repr(u32)] #[derive(Debug, Clone, Copy, PartialEq, Eq)] pub enum StorageClass
{
	UniformConstant, Input, Uniform, Output, Workgroup, CrossWorkgroup, Private, Function,
	Generic, PushConstant, AtomicCounter, Image
}
/// 3.8 Dim: Dimensionality of an image. Used by OpTypeImage
#[repr(u32)] #[derive(Debug, Clone, PartialEq, Eq, Copy)] pub enum Dim
{
	_1, _2, _3, Cube, Rect, Buffer, SubpassData
}
/// 3.9 Sampler Addressing Mode: Addressing mode for creating constant samplers.
/// Used by OpConstantSampler
#[repr(u32)] #[derive(Debug, Clone, Copy)] pub enum SamplerAddressingMode
{
	None, ClampToEdge, Clamp, Repeat, RepeatMirrored
}
/// 3.10 Sampler Filter Mode: Filter mode for creating constant samplers. Used by OpConstantSampler
#[repr(u32)] #[derive(Debug, Clone, Copy)] pub enum SamplerFilterMode { Nearest, Linear }
/// 3.11 Image Format: Declarative image format. Used by OpTypeImage
#[repr(u32)] #[derive(Debug, Clone, PartialEq, Eq)] pub enum ImageFormat
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
#[repr(u32)] #[derive(Debug, Clone, PartialEq, Eq)] pub enum AccessQualifier { ReadOnly, WriteOnly, ReadWrite }
/// 3.19 Function Paramter Attribute: Adds additional information to the return type and
/// to each parameter of a function.
#[repr(u32)] #[derive(Debug, Clone)] pub enum FunctionParameterAttribute
{
	Zext, Sext, ByVal, Sret, NoAlias, NoCapture, NoWrite, NoReadWrite
}
/// 3.20 Decoration: Used by OpDecorate and OpMemberDecorate
#[repr(u32)] #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)] pub enum Decoration
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
#[repr(u32)] #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)] pub enum BuiltIn
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
#[repr(u16)] #[derive(Debug, Clone)] pub enum Opcode
{
	// Miscellaneous Instructions //
	Nop, Undef,
	// Debug Instructions //
	SourceContinued, Source, SourceExtension, Name, MemberName, String, Line, NoLine = 317,
	// Annotation Instructions //
	Decorate = 71, MemberDecorate, DecorationGroup, GroupDecorate, GroupMemberDecorate,
	// Extension Instructions //
	OpExtension = 10, OpExtInstImport, ExtInst,
	// Mode-Setting Instructions //
	MemoryModel = 14, EntryPoint, ExecutionMode, Capability,
	// Type-Declaration Instructions //
	TypeVoid = 19, TypeBool, TypeInt, TypeFloat, TypeVector, TypeMatrix, TypeImage, TypeSampler,
	TypeSampledImage, TypeArray, TypeRuntimeArray, TypeStruct, TypeOpaque, TypePointer,
	TypeFunction, TypeEvent, TypeDeviceEvent, TypeReserveId, TypeQueue, TypePipe, TypeForwardPointer,
	// Constant-Creation Instructions //
	ConstantTrue = 41, ConstantFalse, Constant, ConstantComposite, ConstantSampler, ConstantNull,
	SpecConstantTrue = 48, SpecConstantFalse, SpecConstant, SpecConstantComposite, SpecConstantOp,
	// Memory Instructions //
	Variable = 59, ImageTexelPointer, Load, Store, CopyMemory, CopyMemorySized,
	AccessChain, InBoundsAccessChain, PtrAccessChain, ArrayLength, GenericPtrMemSemantics, InBoundsPtrAccessChain,
	// Function Instructions //
	Function = 54, FunctionParameter, FunctionEnd, FunctionCall,
	// Image Instructions //
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
	// Conversion Instructions //
	ConvertFToU = 109, ConvertFToS, ConvertSToF, ConvertUToF, UConvert, SConvert, FConvert,
	QuantizeToF16, ConvertPtrToU, SatConvertSToU, SatConvertUToS, ConvertUToPtr, PtrCastToGeneric,
	GenericCastToPtr, GenericCastToPtrExplicit, Bitcast,
	// Composite Instructions //
	VectorExtractDynamic = 77, VectorInsertDynamic, VectorShuffle, CompositeConstruct,
	CompositeExtract, CompositeInsert, CopyObject, Transpose,
	// Arithmetic Instructions //
	SNegate = 126, FNegate, IAdd, FAdd, ISub, FSub, IMul, FMul, UDiv, SDiv,
	FDiv, UMod, SRem, SMod, FRem, FMod, VectorTimesScalar, MatrixTimesScalar, VectorTimesMatrix,
	MatrixTimesVector, MatrixTimesMatrix, OuterProduct, Dot, IAddCarry, ISubBorrow, UMulExtended, SMulExtended,
	// Bit Instructions //
	ShiftRightLogical = 194, ShiftRightArithmetic, ShiftLeftLogical, BitwiseOr, BirwiseXor, BitwiseAnd,
	Not, BitFieldInsert, BitFieldSExtract, BitFieldUExtract, BitReverse, BitCount,
	// Relational and Logical Instructions //
	Any = 154, All, IsNan, IsInf, IsFinite, IsNormal, SignBitSet,
	LessOrGreater, Ordered, Unordered, LogicalEqual, LogicalNotEqual, LogicalOr,
	LogicalAnd, LogicalNot, Select, IEqual, INotEqual, UGreaterThan, SGreaterThan, UGreaterThanEqual,
	SGreaterThanEqual, ULessThan, SLessThan, ULessThanEqual, SLessThanEqual, FOrdEqual, FUnordEqual,
	FOrdNotEqual, FUnordNotEqual, FOrdLessThan, FUnordLessThan, FOrdGreaterThan, FUnordGreaterThan,
	FOrdLessThanEqual, FUnordLessThanEqual, FOrdGreaterThanEqual, FUnordGreaterThanEqual,
	// Derivative Instructions //
	DPdx = 207, DPdy, Fwidth, DPdxFine, DPdyFine, FwidthFine, DPdxCoarse, DPdyCoarse, FwidthCoarse,
	// Control-Flow Instructions //
	Phi = 245, LoopMerge, SelectionMerge, Label, Branch, BranchConditional, Switch,
	Kill, Return, ReturnValue, Unreachable, LifetimeStart, LifetimeStop,
	// Atomic Instructions //
	AtomicLoad = 227, AtomicStore, AtomicExchange, AtomicCompareExchange, AtomicCompareExchangeWeak,
	AtomicIIncrement, AtomicIDecrement, AtomcIAdd, AtomicISub, AtomicSMin, AtomicUMin, AtomicSMax, AtomicUMax,
	AtomicAnd, AtomicOr, AtomicXor, AtomicFlagTestAndSet = 318, AtomicFlagClear,
	// Primitive Instructions //
	EmitVertex = 218, EndPrimitive, EmitStreamVertex, EndStreamPrimitive,
	// Barrier Instructions //
	ControlBarrier = 224, MemoryBarrier,
	// Group Instructions //
	GroupAsyncCopy = 259, GroupWaitEvents, GroupAll, GroupAny, GroupBroadcast, GroupIAdd, GroupFAdd,
	GroupFMin, GroupUMin, GroupSMin, GroupFMax, GroupUMax, GroupSMax,
	SubgroupBallotKHR = 4421, SubgroupFirstInvocationKHR = 4422, SubgroupReadInvocationKHR = 4432,
	// Device-Side Enqueue Instructions //
	EnqueueMarker = 291, EnqueueKernel, GetKernelNDrangeSubGroupCount, GetKernelNDrangeMaxSubGroupSize,
	GetKernelWorkGroupSize, GetKernelPreferredWorkGroupSizeMultiple, RetainEvent, ReleaseEvent,
	CreateUserEvent, IsValidEvent, SetUserEventStatus, CaptureEventProfilingInfo, GetDefaultQueue, BuildNDrange,
	// Pipe Instructions //
	ReadPipe = 274, WritePipe, ReservedReadPipe, ReservedWritePipe,
	ReserveReadPipePackets, ReserveWritePipePackets, CommitReadPipe, CommitWritePipe,
	IsValidReserveId, GetNumPipePackets, GetMaxPipePackets, GroupReserveReadPipePackets,
	GroupReserveWritePipePackets, GroupCommitReatPipe, GroupCommitWritePipe
}
