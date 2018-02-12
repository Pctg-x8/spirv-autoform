//! Data(Type/Operation) Collector

use {std, spv};
use std::ops::Deref;
use std::io::prelude::Write;
use std::collections::BTreeMap;
use module_loader::*;
use spvdefs::Id;
use std::fmt::Display;

pub enum ParsingError<'s>
{
    TypeNotFound(Id), InvalidType(&'s str), DuplicatedTypeID(Id), MismatchDataLength(&'s spv::Type<'s>),
    UnknownType { type_ref: &'s spv::Type<'s>, op: &'s str }
}

pub struct ErrorReporter
{
    pub has_error: bool,
    pub context_stack: Vec<String>
}
impl ErrorReporter
{
    pub fn new() -> Self { ErrorReporter { has_error: false, context_stack: Vec::new() } }
    pub fn report<Msg: Display>(&mut self, msg: Msg)
    {
        writeln!(std::io::stderr(), "*Error* {}", msg).unwrap();
        self.has_error = true;
    }
    pub fn report_typed(&mut self, e: ParsingError)
    {
        let header = if let Some(ch) = self.context_stack.last() { format!("{}: ", ch) } else { "".to_owned() };

        match e
        {
            ParsingError::TypeNotFound(type_ref) =>
                self.report(format!("{}A type definition #{} is not found", header, type_ref)),
            ParsingError::InvalidType(op) =>
                self.report(format!("{}Invalid type for the {}", header, op)),
            ParsingError::UnknownType { type_ref, op } =>
                self.report(format!("{}Unknown type ({:?}) for the {}", header, type_ref, op)),
            ParsingError::DuplicatedTypeID(id) =>
                self.report(format!("{}Type Definition for #{} is found once more.", header, id)),
            ParsingError::MismatchDataLength(ty) =>
                self.report(format!("{}Mismatching a data length for the type {:?}", header, ty))
        }
    }
    pub fn enter_context(&mut self, header: String)
    {
        self.context_stack.push(header);
    }
    pub fn leave_context(&mut self) { self.context_stack.pop(); }
}

pub struct CollectedData<'m>
{
    pub assigned: AssignedOperations<'m>,
    pub types: TypeAggregator<'m>,
    pub constants: ConstantCollector
}

pub struct AssignedOperations<'m>(Vec<Option<&'m Operation>>);
impl<'m> AssignedOperations<'m>
{
    pub fn collect(module: &'m SpirvModule) -> Self
    {
        let mut sink = vec![None; module.id_range.len()];
        for (id, o) in module.operations.iter().filter_map(|o| o.result_id().map(|i| (i, o)))
        {
            sink[id as usize] = Some(o);
        }
        AssignedOperations(sink)
    }
    pub fn at(&self, index: Id) -> Option<&'m Operation> { if index < self.0.len() as u32 { self.0[index as usize].clone() } else { None } }
}
impl<'m> Deref for AssignedOperations<'m> { type Target = [Option<&'m Operation>]; fn deref(&self) -> &Self::Target { &self.0[..] } }

pub struct TypeAggregator<'n>(spv::TypedefMap<'n>);
impl<'n> TypeAggregator<'n>
{
    pub fn resolve_all(ops: &AssignedOperations<'n>, names: &'n NameMaps, err: &mut ErrorReporter) -> Self
    {
        let mut t = TypeAggregator(spv::TypedefMap::new());
        for (n, op) in ops.iter().enumerate().filter(|&(_, op)| op.map(Operation::is_type_op).unwrap_or(false))
        {
            if t.0.contains_key(&(n as Id)) { err.report(format!("Type Definition for ID {} has been found once more.", n)); }
            else
            {
                let r = t.try_resolve(ops, names, n as Id, &op.unwrap());
                t.0.insert(n as Id, r);
            }
        }
        t
    }
    pub fn get(&self, id: Id) -> Option<&spv::Typedef<'n>> { self.0.get(&id) }
    pub fn require(&self, id: Id) -> &spv::Typedef<'n>
    {
        if let Some(t) = self.get(id) { t } else { panic!("<MODULE CORRUPTION> Cannot find a type for id {}", id); }
    }

    fn lookup(&mut self, ops: &AssignedOperations, names: &'n NameMaps, id: Id) -> &spv::Typedef<'n>
    {
        if !self.0.contains_key(&id)
        {
            let resolved = self.try_resolve(ops, names, id, ops[id as usize].as_ref().unwrap());
            self.0.insert(id, resolved);
        }
        self.0.get(&id).unwrap()
    }
    fn try_resolve(&mut self, ops: &AssignedOperations, names: &'n NameMaps, id: Id, op: &Operation) -> spv::Typedef<'n>
    {
        let t = match *op
        {
            Operation::TypeVoid(_) => spv::Type::Void,
            Operation::TypeBool(_) => spv::Type::Bool,
            Operation::TypeInt { width, signedness, .. } => spv::Type::Int(width as u8, signedness),
            Operation::TypeFloat { width, .. } => spv::Type::Float(width as u8),
            Operation::TypeVector { component_ty, count, .. } => spv::Type::Vector(count, Box::new(self.lookup(ops, names, component_ty).clone())),
            Operation::TypeMatrix { col_ty, count, .. }       => spv::Type::Matrix(count, Box::new(self.lookup(ops, names, col_ty).clone())),
            Operation::TypeArray { elm_ty, length, .. }       => spv::Type::Array(length, Box::new(self.lookup(ops, names, elm_ty).clone())),
            Operation::TypeRuntimeArray { element_type, .. }  => spv::Type::DynamicArray(Box::new(self.lookup(ops, names, element_type).clone())),
            Operation::TypePointer { storage, _type, .. } => spv::Type::Pointer(storage, Box::new(self.lookup(ops, names, _type).clone())),
            Operation::TypeStruct { ref member_types, result } => spv::Type::Structure(spv::TyStructure
            {
                id: result, members: member_types.iter().enumerate()
                    .map(|(n, &x)| spv::StructureElement { name: names.lookup_member(id, n), _type: self.lookup(ops, names, x).clone() })
                    .collect()
            }),
            Operation::TypeImage { sampled_type, dim, depth, arrayed, ms, sampled, format, qualifier, .. } => spv::Type::Image
            {
                sampled_type: Box::new(self.lookup(ops, names, sampled_type).clone()), dim, depth, arrayed, ms, sampled, format, qualifier
            },
            Operation::TypeSampler(_) => spv::Type::Sampler,
            Operation::TypeSampledImage { image_ty, .. } => spv::Type::SampledImage(Box::new(self.lookup(ops, names, image_ty).clone())),
            Operation::TypeFunction { return_type, ref parameters, .. } => spv::Type::Function(
                Box::new(self.lookup(ops, names, return_type).clone()),
                parameters.iter().map(|&x| self.lookup(ops, names, x).clone()).collect()),
            _ => unreachable!("Not a type operator: {:?}", op)
        };

        spv::Typedef { name: names.lookup_in_toplevel(id).map(From::from), def: t }
    }

    pub fn dump(&self)
    {
        println!("## Aggregated Types");
        for (n, t) in &self.0 { println!("- {}: {:?}", n, t); }
    }
}

/// Undefined constant value
#[derive(Debug, Clone)]
pub struct Undef<T>(std::marker::PhantomData<T>);
pub fn const_undef<T>() -> Undef<T> { Undef(std::marker::PhantomData) }
/// A constant value
#[derive(Debug, Clone)]
pub struct Constant<T: std::fmt::Debug + Clone>(T);
/// A combination of some value refs(i.e. vec4)
#[derive(Debug, Clone)]
pub struct CompositeConstant<T>(Vec<Id>, std::marker::PhantomData<T>);
pub fn const_composite<T>(ids: Vec<Id>) -> CompositeConstant<T> { CompositeConstant(ids, std::marker::PhantomData) }
/// A constant value
pub trait ConstantValue : std::fmt::Debug
{
    fn clone_inner(&self) -> Box<ConstantValue>;
}
impl<T: std::fmt::Debug + 'static> ConstantValue for Undef<T>
{
    fn clone_inner(&self) -> Box<ConstantValue> { Box::new(Undef(std::marker::PhantomData::<T>)) }
}
impl<T: std::fmt::Debug + Clone + 'static> ConstantValue for Constant<T>
{
    fn clone_inner(&self) -> Box<ConstantValue> { Box::new(Constant(self.0.clone())) }
}
impl<T: std::fmt::Debug + 'static> ConstantValue for CompositeConstant<T>
{
    fn clone_inner(&self) -> Box<ConstantValue> { Box::new(CompositeConstant(self.0.clone(), std::marker::PhantomData::<T>)) }
}

pub trait FromLiterals { fn from_literals(v: &[u32]) -> Self; }
impl FromLiterals for u8 { fn from_literals(v: &[u32]) -> u8 { v[0] as u8 } }
impl FromLiterals for u16 { fn from_literals(v: &[u32]) -> u16 { v[0] as u16 } }
impl FromLiterals for u32 { fn from_literals(v: &[u32]) -> u32 { v[0] } }
impl FromLiterals for u64 { fn from_literals(v: &[u32]) -> u64 { v[0] as u64 | (std::ops::Shl::shl(v[1] as u64, 32)) } }
impl FromLiterals for i8 { fn from_literals(v: &[u32]) -> i8 { unsafe { std::mem::transmute(u8::from_literals(v)) } } }
impl FromLiterals for i16 { fn from_literals(v: &[u32]) -> i16 { unsafe { std::mem::transmute(u16::from_literals(v)) } } }
impl FromLiterals for i32 { fn from_literals(v: &[u32]) -> i32 { unsafe { std::mem::transmute(u32::from_literals(v)) } } }
impl FromLiterals for i64 { fn from_literals(v: &[u32]) -> i64 { unsafe { std::mem::transmute(u64::from_literals(v)) } } }
impl FromLiterals for f32 { fn from_literals(v: &[u32]) -> f32 { unsafe { std::mem::transmute(v[0]) } } }
impl FromLiterals for f64 { fn from_literals(v: &[u32]) -> f64 { unsafe { std::mem::transmute(u64::from_literals(v)) } } }
pub struct ConstantCollector
{
    embed: BTreeMap<Id, Box<ConstantValue>>, pub specialized: BTreeMap<Id, Box<ConstantValue>>
}
impl ConstantCollector
{
	pub fn collect(ops: &AssignedOperations, types: &TypeAggregator, er: &mut ErrorReporter) -> Self
	{
        let (mut embed, mut specialized) = (BTreeMap::new(), BTreeMap::new());

        for (res, op) in ops.iter().filter_map(|x| x.and_then(Operation::strip_constant_result))
        {
            er.enter_context(format!("Collecting Constant #{}", res.id));
            if let Some(ty) = types.get(res.ty)
            {
                match *op
                {
                    Operation::Undef(_) => match Self::process_undef(ty) { Ok(v) => { embed.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::Constant { ref literals, .. } => match Self::process_constant(ty, literals) { Ok(v) => { embed.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::SpecConstant { ref literals, .. } => match Self::process_constant(ty, literals) { Ok(v) => { specialized.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::ConstantTrue (_) => match Self::process_bool_constant(ty, true)  { Ok(v) => { embed.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::ConstantFalse(_) => match Self::process_bool_constant(ty, false) { Ok(v) => { embed.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::SpecConstantTrue (_) => match Self::process_bool_constant(ty, true)  { Ok(v) => { specialized.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::SpecConstantFalse(_) => match Self::process_bool_constant(ty, false) { Ok(v) => { specialized.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::ConstantComposite { ref constituents, .. } => match Self::process_composite_constant(ty, constituents) { Ok(v) => { embed.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::SpecConstantComposite { ref constituents, .. } => match Self::process_composite_constant(ty, constituents) { Ok(v) => { specialized.insert(res.id, v); }, Err(e) => er.report_typed(e) },
                    Operation::SpecConstantOp { .. } => { println!("unimplemented: OpSpecConstantOp"); }
                    _ => unreachable!()
                };
            }
            er.leave_context();
        }

        ConstantCollector { embed, specialized }
	}

    fn process_undef(ty: &spv::Typedef) -> Result<Box<ConstantValue>, ParsingError<'static>>
    {
        match &ty.def
        {
            &quote_spvt!(bool) => Ok(Box::new(const_undef::<bool>())),
            &quote_spvt!(i8)   => Ok(Box::new(const_undef::<i8>())),
            &quote_spvt!(u8)   => Ok(Box::new(const_undef::<u8>())),
            &quote_spvt!(i16)  => Ok(Box::new(const_undef::<i16>())),
            &quote_spvt!(u16)  => Ok(Box::new(const_undef::<u16>())),
            &quote_spvt!(i32)  => Ok(Box::new(const_undef::<i32>())),
            &quote_spvt!(u32)  => Ok(Box::new(const_undef::<u32>())),
            &quote_spvt!(i64)  => Ok(Box::new(const_undef::<i64>())),
            &quote_spvt!(u64)  => Ok(Box::new(const_undef::<u64>())),
            &quote_spvt!(f32)  => Ok(Box::new(const_undef::<f32>())),
            &quote_spvt!(f64)  => Ok(Box::new(const_undef::<f64>())),
            _ => Err(ParsingError::InvalidType("OpUndef"))
        }
    }
    fn process_constant(ty: &spv::Typedef, literals: &[u32]) -> Result<Box<ConstantValue>, ParsingError<'static>>
    {
        match &ty.def
        {
            &quote_spvt!(i8)  => Ok(Box::new(Constant(i8::from_literals(literals)))),
            &quote_spvt!(u8)  => Ok(Box::new(Constant(u8::from_literals(literals)))),
            &quote_spvt!(i16) => Ok(Box::new(Constant(i16::from_literals(literals)))),
            &quote_spvt!(u16) => Ok(Box::new(Constant(u16::from_literals(literals)))),
            &quote_spvt!(i32) => Ok(Box::new(Constant(i32::from_literals(literals)))),
            &quote_spvt!(u32) => Ok(Box::new(Constant(u32::from_literals(literals)))),
            &quote_spvt!(i64) => Ok(Box::new(Constant(i64::from_literals(literals)))),
            &quote_spvt!(u64) => Ok(Box::new(Constant(u64::from_literals(literals)))),
            &quote_spvt!(f32) => Ok(Box::new(Constant(f32::from_literals(literals)))),
            &quote_spvt!(f64) => Ok(Box::new(Constant(f64::from_literals(literals)))),
            _ => Err(ParsingError::InvalidType("OpConstant"))
        }
    }
    fn process_bool_constant(ty: &spv::Typedef, value: bool) -> Result<Box<ConstantValue>, ParsingError<'static>>
    {
        if ty.def == quote_spvt!(bool) { Ok(Box::new(Constant(value))) } else { Err(ParsingError::InvalidType(if value { "OpConstantTrue" } else { "OpConstantFalse" })) }
    }
    fn process_composite_constant<'t>(ty: &'t spv::Typedef, values: &[u32]) -> Result<Box<ConstantValue>, ParsingError<'t>>
    {
        match &ty.def
        {
            &quote_spvt![ref td, n] => match &td.def
            {
                &quote_spvt!(i8) => Ok(Box::new(const_composite::<i8>(values[..n as usize].to_owned()))),
                _ => Err(ParsingError::UnknownType { type_ref: &td.def, op: "OpTypeArray" })
            },
            &quote_spvt!(vec[n, ref td]) => if values.len() == n as usize
            {
                match &td.def
                {
                    &quote_spvt!(f32) => Ok(Box::new(const_composite::<f32>(values.to_owned()))),
                    _ => Err(ParsingError::UnknownType { type_ref: &td.def, op: "OpTypeVector" })
                }
            }
            else { Err(ParsingError::MismatchDataLength(&ty.def)) },
            _ => Err(ParsingError::InvalidType("OpConstantComposite"))
        }
    }
}
