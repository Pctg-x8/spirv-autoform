//! SPIR-V Types

use std::collections::BTreeMap;
use spvdefs::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructureElement<'n> { pub name: Option<&'n str>, pub tyid: Id }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TyStructure<'m> { pub id: Id, pub members: Vec<StructureElement<'m>> }
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Type<'n>
{
    Void, Bool, Int(u8, bool), Float(u8), Vector(u32, Box<Typedef<'n>>), Matrix(u32, Box<Typedef<'n>>),
    Array(u32, Box<Typedef<'n>>), DynamicArray(Box<Typedef<'n>>), Pointer(StorageClass, Box<Typedef<'n>>), Structure(TyStructure<'n>),
    Image
    {
        sampled_type: Box<Typedef<'n>>, dim: Dim, depth: u32, arrayed: u32, ms: u32, sampled: u32, format: ImageFormat,
        qualifier: Option<AccessQualifier>
    }, Sampler, SampledImage(Box<Typedef<'n>>), Function(Box<Typedef<'n>>, Vec<Typedef<'n>>)
}
#[derive(Clone, PartialEq, Eq, Debug)] pub struct Typedef<'n> { pub name: Option<&'n str>, pub def: Type<'n> }
pub type TypedefMap<'n> = BTreeMap<Id, Typedef<'n>>;

use std::fmt::{Display, Formatter, Result as FmtResult};
impl<'n> Display for Type<'n>
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult
    {
        match self
        {
            &Type::Void => write!(fmt, "void"),
            &Type::Bool => write!(fmt, "bool"),
            &Type::Int(bits, true) => write!(fmt, "int{}", bits),
            &Type::Int(bits, false) => write!(fmt, "uint{}", bits),
            &Type::Float(bits) => write!(fmt, "float{}", bits),
            &Type::Vector(n, ref e) => write!(fmt, "vec{}<{}>", n, e),
            &Type::Matrix(n, ref e) => write!(fmt, "mat{}<{}>", n, e),
            &Type::Array(n, ref e) => write!(fmt, "{}[{}]", e, n),
            &Type::DynamicArray(ref e) => write!(fmt, "{}[]", e),
            &Type::Pointer(ref s, ref p) => write!(fmt, "&{:?} {}", s, p),
            &Type::Structure(ref m) => write!(fmt, "struct {:?}", m),
            &Type::Image { ref sampled_type, .. } => write!(fmt, "Image<{}>", sampled_type),
            &Type::Sampler => write!(fmt, "sampler"),
            &Type::SampledImage(ref i) => write!(fmt, "SampledImage<{}>", i),
            &Type::Function(ref r, ref p) => write!(fmt, "({}) => {}", p.iter().map(ToString::to_string).collect::<Vec<_>>().join(", "), r)
        }
    }
}
impl<'n> Display for Typedef<'n>
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult
    {
        match self
        {
            &Typedef { name: Some(ref name), def: Type::Structure(ref m) } => write!(fmt, "struct {} {{ {} }}", name, m.members.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")),
            &Typedef { def: Type::Structure(ref m), .. } => write!(fmt, "struct {{ {} }}", m.members.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")),
            &Typedef { ref def, .. } => def.fmt(fmt)
        }
    }
}
impl<'s> Display for StructureElement<'s>
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult { write!(fmt, "{}: ty#{}", self.name.unwrap_or("_"), self.tyid) }
}
impl<'n> Typedef<'n>
{
    /// Dereference a typedef if it is a pointer type
    pub fn dereference(&self) -> Option<&Typedef<'n>>
    {
        match *self
        {
            Typedef { def: Type::Pointer(_, ref p), .. } => Some(p),
            _ => None
        }
    }
    pub fn structure(&self) -> Option<&TyStructure<'n>> { self.def.structure() }
}

impl<'n> Type<'n>
{
    pub fn structure(&self) -> Option<&TyStructure<'n>>
    {
        if let &Type::Structure(ref s) = self { Some(s) } else { None }
    }
}

impl<'n> TyStructure<'n>
{
    pub fn find_member(&self, name: &str) -> Option<&StructureElement<'n>> { self.members.iter().find(|e| e.name == Some(name)) }
}

macro_rules! quote_spvt
{
    () => { ::spv::Type::Void };
    (bool) => { ::spv::Type::Bool };
    (i8) => { ::spv::Type::Int(8, true) };
    (u8) => { ::spv::Type::Int(8, false) };
    (i16) => { ::spv::Type::Int(16, true) };
    (u16) => { ::spv::Type::Int(16, false) };
    (i32) => { ::spv::Type::Int(32, true) };
    (u32) => { ::spv::Type::Int(32, false) };
    (i64) => { ::spv::Type::Int(64, true) };
    (u64) => { ::spv::Type::Int(64, false) };
    (f32) => { ::spv::Type::Float(32) };
    (f64) => { ::spv::Type::Float(64) };
    [$t: pat] => { ::spv::Type::DynamicArray($t) };
    [$t: pat, $n: pat] => { ::spv::Type::Array($n, $t) };
    (vec [ $n: pat, $t: pat ]) => { ::spv::Type::Vector($n, $t) };
    (mat [ $n: pat, $t: pat ]) => { ::spv::Type::Matrix($n, $t) };
    (vec$n: expr => $t: ty) => { ::spv::Type::Vector($n, spv::Typedef { def: quote_spvt!($t), .. }) };
    (mat$n: expr => $t: ty) => { ::spv::Type::Matrix($n, spv::Typedef { def: quote_spvt!($t), .. }) };
}
