//! spirv-autoform: Parse SPIR-V Module and find Shader Interface

mod container_ext;
mod spvdefs;
mod spv;

mod module_loader;
mod collector;
mod shader_interface;

pub use module_loader::{SpirvModule, Operation, Decoration, ExecutionMode};
pub use collector::{CollectedData, ErrorReporter, AssignedOperations, TypeAggregator};
pub use shader_interface::ShaderInterface;