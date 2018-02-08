//! SPIR-V Types

use std;
use std::borrow::Cow;
use std::collections::BTreeMap;
use spvdefs::*;

#[derive(Clone, Debug)]
pub struct StructureElement<'n> { pub name: Option<&'n str>, pub _type: Typedef<'n> }
#[derive(Clone, Debug)]
pub struct TyStructure<'m> { pub id: Id, pub members: Vec<StructureElement<'m>> }
#[derive(Clone)]
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
#[derive(Clone)] pub struct Typedef<'n> { pub name: Option<Cow<'n, str>>, pub def: Type<'n> }
pub type TypedefMap<'n> = BTreeMap<Id, Typedef<'n>>;

impl<'n> std::fmt::Debug for Type<'n>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        match self
        {
            &Type::Void => write!(fmt, "void"),
            &Type::Bool => write!(fmt, "bool"),
            &Type::Int(bits, true) => write!(fmt, "signed {}bit int", bits),
            &Type::Int(bits, false) => write!(fmt, "unsigned {}bit int", bits),
            &Type::Float(bits) => write!(fmt, "{}bit float", bits),
            &Type::Vector(n, ref e) => write!(fmt, "vec{} of {:?}", n, e),
            &Type::Matrix(n, ref e) => write!(fmt, "mat{} of {:?}", n, e),
            &Type::Array(n, ref e) => write!(fmt, "array of {:?} with {} element(s)", e, n),
            &Type::DynamicArray(ref e) => write!(fmt, "array of {:?}", e),
            &Type::Pointer(ref s, ref p) => write!(fmt, "pointer to {:?} of {:?}", s, p),
            &Type::Structure(ref m) => write!(fmt, "struct {:?}", m),
            &Type::Image { ref sampled_type, .. } => write!(fmt, "Image sampled with type {:?}", sampled_type),
            &Type::Sampler => write!(fmt, "sampler"),
            &Type::SampledImage(ref i) => write!(fmt, "sampled image of {:?}", i),
            &Type::Function(ref r, ref p) => write!(fmt, "({:?}) => {:?}", p, r)
        }
    }
}
impl<'n> std::fmt::Debug for Typedef<'n>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result
    {
        match self
        {
            &Typedef { ref name, def: Type::Structure(ref m) } => write!(fmt, "struct {:?} {:?}", name, m),
            &Typedef { ref def, .. } => def.fmt(fmt)
        }
    }
}
impl<'n> Typedef<'n>
{
    pub fn dereference(&self) -> &Typedef<'n>
    {
        match self
        {
            &Typedef { def: Type::Pointer(_, ref p), .. } => p,
            s => s
        }
    }
}

impl<'n> Type<'n>
{
    pub fn structure(&self) -> Option<&TyStructure<'n>>
    {
        if let &Type::Structure(ref s) = self { Some(s) } else { None }
    }
}
