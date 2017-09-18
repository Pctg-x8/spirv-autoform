//! Data(Type/Operation) Collector

use {std, spv};
use std::ops::Deref;
use std::borrow::Cow;
use std::io::prelude::Write;
use std::collections::BTreeMap;
use module_loader::*;
use spvdefs::Id;

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
    pub fn report(&mut self, msg: &str)
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
                self.report(&format!("{}A type definition #{} is not found", header, type_ref)),
            ParsingError::InvalidType(op) =>
                self.report(&format!("{}Invalid type for the {}", header, op)),
            ParsingError::UnknownType { type_ref, op } =>
                self.report(&format!("{}Unknown type ({:?}) for the {}", header, type_ref, op)),
            ParsingError::DuplicatedTypeID(id) =>
                self.report(&format!("{}Type Definition for #{} is found once more.", header, id)),
            ParsingError::MismatchDataLength(ty) =>
                self.report(&format!("{}Mismatching a data length for the type {:?}", header, ty))
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
impl<'m> Deref for AssignedOperations<'m> { type Target = [Option<&'m Operation>]; fn deref(&self) -> &Self::Target { &self.0[..] } }

pub struct TypeAggregator<'n>(spv::TypedefMap<'n>);
impl<'n> TypeAggregator<'n>
{
    pub fn resolve_all(ops: &AssignedOperations<'n>, names: &'n NameMaps, err: &mut ErrorReporter) -> Self
    {
        let mut t = TypeAggregator(spv::TypedefMap::new());
        for (n, op) in ops.iter().enumerate().filter(|&(_, op)| op.map(Operation::is_type_op).unwrap_or(false))
        {
            if t.0.contains_key(&(n as Id))
            {
                err.report(&format!("Type Definition for ID {} has been found once more.", n));
            }
            else
            {
                let r = t.try_resolve(ops, names, n as Id, &op.unwrap());
                t.0.insert(n as Id, r);
            }
        }
        t
    }
    pub fn get(&self, id: Id) -> Option<&spv::Typedef<'n>> { self.0.get(&id) }

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
        let t = match op
        {
            &Operation::TypeVoid { .. } => spv::Type::Void,
            &Operation::TypeBool { .. } => spv::Type::Bool,
            &Operation::TypeInt { width, signedness, .. } => spv::Type::Int(width as _, signedness),
            &Operation::TypeFloat { width, .. } => spv::Type::Float(width as _),
            &Operation::TypeVector { component_type, component_count, .. }
                => spv::Type::Vector(component_count, Box::new(self.lookup(ops, names, component_type).clone())),
            &Operation::TypeMatrix { column_type, column_count, .. }
                => spv::Type::Matrix(column_count, Box::new(self.lookup(ops, names, column_type).clone())),
            &Operation::TypeArray { element_type, length, .. } => spv::Type::Array(length, Box::new(self.lookup(ops, names, element_type).clone())),
            &Operation::TypeRuntimeArray { element_type, .. } => spv::Type::DynamicArray(Box::new(self.lookup(ops, names, element_type).clone())),
            &Operation::TypePointer { ref storage, _type, .. }
                => spv::Type::Pointer(storage.clone(), Box::new(self.lookup(ops, names, _type).clone())),
            &Operation::TypeStruct { ref member_types, .. } => spv::Type::Structure(member_types.iter().enumerate().map(|(n, &x)| spv::StructureElement
            {
                name: names.member.get(&id).and_then(|mb| mb.get(n)).map(|x| Cow::Borrowed(x as &str)),
                _type: self.lookup(ops, names, x).clone()
            }).collect()),
            &Operation::TypeImage { sampled_type, ref dim, depth, arrayed, ms, sampled, ref format, ref qualifier, .. } => spv::Type::Image
            {
                sampled_type: Box::new(self.lookup(ops, names, sampled_type).clone()),
                dim: dim.clone(), depth: depth, arrayed: arrayed, ms: ms, sampled: sampled, format: format.clone(), qualifier: qualifier.clone()
            },
            &Operation::TypeSampler { .. } => spv::Type::Sampler,
            &Operation::TypeSampledImage { image_type, .. } => spv::Type::SampledImage(Box::new(self.lookup(ops, names, image_type).clone())),
            &Operation::TypeFunction { return_type, ref parameters, .. } => spv::Type::Function(
                Box::new(self.lookup(ops, names, return_type).clone()),
                parameters.iter().map(|&x| self.lookup(ops, names, x).clone()).collect()),
            _ => unreachable!("Unresolvable as a type: {:?}", op)
        };

        spv::Typedef { name: names.toplevel.get(&id).map(|x| Cow::Borrowed(x as &str)), def: t }
    }
}

macro_rules! quote_spvt
{
    () => { spv::Type::Void };
    (bool) => { spv::Type::Bool };
    (i8) => { spv::Type::Int(8, true) };
    (u8) => { spv::Type::Int(8, false) };
    (i16) => { spv::Type::Int(16, true) };
    (u16) => { spv::Type::Int(16, false) };
    (i32) => { spv::Type::Int(32, true) };
    (u32) => { spv::Type::Int(32, false) };
    (i64) => { spv::Type::Int(64, true) };
    (u64) => { spv::Type::Int(64, false) };
    (f32) => { spv::Type::Float(32) };
    (f64) => { spv::Type::Float(64) };
    [$t: pat] => { spv::Type::DynamicArray($t) };
    [$t: pat, $n: pat] => { spv::Type::Array($n, $t) };
    (vec [ $n: pat, $t: pat ]) => { spv::Type::Vector($n, $t) };
    (mat [ $n: pat, $t: pat ]) => { spv::Type::Matrix($n, $t) };
    (vec$n: expr => $t: ty) => { spv::Type::Vector($n, spv::Typedef { def: quote_spvt!($t), .. }) };
    (mat$n: expr => $t: ty) => { spv::Type::Matrix($n, spv::Typedef { def: quote_spvt!($t), .. }) };
}

/// Undefined constant value
#[derive(Debug, Clone)]
pub struct Undef<T>(std::marker::PhantomData<T>);
/// A constant value
#[derive(Debug, Clone)]
pub struct Constant<T: std::fmt::Debug + Clone>(T);
/// A combination of some value refs(i.e. vec4)
#[derive(Debug, Clone)]
pub struct CompositeConstant<T>(Vec<Id>, std::marker::PhantomData<T>);
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

        for (id, tyid, op) in ops.iter().filter_map(|x| x.and_then(Operation::strip_constant_result))
        {
            er.enter_context(format!("Collecting Constant #{}", id));
            if let Some(ty) = types.get(tyid)
            {
                match op
                {
                    &Operation::Undef { .. } => Self::process_undef(&mut embed, id, ty, er),
                    &Operation::Constant { ref literals, .. } => Self::process_constant(&mut embed, id, ty, literals, er),
                    &Operation::SpecConstant { ref literals, .. } => Self::process_constant(&mut specialized, id, ty, literals, er),
                    &Operation::ConstantTrue { .. } => Self::process_bool_constant(&mut embed, id, ty, true, er),
                    &Operation::SpecConstantTrue { .. } => Self::process_bool_constant(&mut specialized, id, ty, true, er),
                    &Operation::ConstantFalse { .. } => Self::process_bool_constant(&mut embed, id, ty, false, er),
                    &Operation::SpecConstantFalse { .. } => Self::process_bool_constant(&mut specialized, id, ty, false, er),
                    &Operation::ConstantComposite { ref constituents, .. } =>
                        Self::process_composite_constant(&mut embed, id, ty, constituents, er),
                    &Operation::SpecConstantComposite { ref constituents, .. } =>
                        Self::process_composite_constant(&mut specialized, id, ty, constituents, er),
                    &Operation::SpecConstantOp { .. } => { println!("unimplemented: OpSpecConstantOp"); }
                    _ => unreachable!()
                }
            }
            er.leave_context();
        }

        ConstantCollector { embed, specialized }
	}

    fn process_undef(selector: &mut BTreeMap<Id, Box<ConstantValue>>, id: Id, ty: &spv::Typedef, er: &mut ErrorReporter)
    {
        match &ty.def
        {
            &quote_spvt!(bool) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<bool>))); },
            &quote_spvt!(i8) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<i8>))); },
            &quote_spvt!(u8) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<u8>))); },
            &quote_spvt!(i16) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<i16>))); },
            &quote_spvt!(u16) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<u16>))); },
            &quote_spvt!(i32) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<i32>))); },
            &quote_spvt!(u32) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<u32>))); },
            &quote_spvt!(i64) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<i64>))); },
            &quote_spvt!(u64) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<u64>))); },
            &quote_spvt!(f32) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<f32>))); },
            &quote_spvt!(f64) => { selector.insert(id, Box::new(Undef(std::marker::PhantomData::<f64>))); },
            _ => er.report_typed(ParsingError::InvalidType("OpUndef"))
        }
    }
    fn process_constant(selector: &mut BTreeMap<Id, Box<ConstantValue>>, id: Id, ty: &spv::Typedef, literals: &[u32], er: &mut ErrorReporter)
    {
        match &ty.def
        {
            &quote_spvt!(i8) => { selector.insert(id, Box::new(Constant(i8::from_literals(literals)))); },
            &quote_spvt!(u8) => { selector.insert(id, Box::new(Constant(u8::from_literals(literals)))); },
            &quote_spvt!(i16) => { selector.insert(id, Box::new(Constant(i16::from_literals(literals)))); },
            &quote_spvt!(u16) => { selector.insert(id, Box::new(Constant(u16::from_literals(literals)))); },
            &quote_spvt!(i32) => { selector.insert(id, Box::new(Constant(i32::from_literals(literals)))); },
            &quote_spvt!(u32) => { selector.insert(id, Box::new(Constant(u32::from_literals(literals)))); },
            &quote_spvt!(i64) => { selector.insert(id, Box::new(Constant(i64::from_literals(literals)))); },
            &quote_spvt!(u64) => { selector.insert(id, Box::new(Constant(u64::from_literals(literals)))); },
            &quote_spvt!(f32) => { selector.insert(id, Box::new(Constant(f32::from_literals(literals)))); },
            &quote_spvt!(f64) => { selector.insert(id, Box::new(Constant(f64::from_literals(literals)))); },
            _ => er.report_typed(ParsingError::InvalidType("OpConstant"))
        }
    }
    fn process_bool_constant(selector: &mut BTreeMap<Id, Box<ConstantValue>>, id: Id, ty: &spv::Typedef, value: bool, er: &mut ErrorReporter)
    {
        if ty.def == quote_spvt!(bool) { selector.insert(id, Box::new(Constant(value))); }
        else { er.report_typed(ParsingError::InvalidType(if value { "OpConstantTrue" } else { "OpConstantFalse" })); }
    }
    fn process_composite_constant(selector: &mut BTreeMap<Id, Box<ConstantValue>>, id: Id, ty: &spv::Typedef, values: &[u32], er: &mut ErrorReporter)
    {
        match &ty.def
        {
            &quote_spvt![ref td, n] => match &td.def
            {
                &quote_spvt!(i8) => { selector.insert(id, Box::new(CompositeConstant(values[..n as usize].to_owned(), std::marker::PhantomData::<i8>))); },
                _ => er.report_typed(ParsingError::UnknownType { type_ref: &td.def, op: "OpTypeArray" })
            },
            &quote_spvt!(vec[n, ref td]) => if values.len() == n as usize
            {
                match &td.def
                {
                    &quote_spvt!(f32) => { selector.insert(id, Box::new(CompositeConstant(values.to_owned(), std::marker::PhantomData::<f32>))); },
                    _ => er.report_typed(ParsingError::UnknownType { type_ref: &td.def, op: "OpTypeVector" })
                }
            }
            else { er.report_typed(ParsingError::MismatchDataLength(&ty.def)) },
            _ => er.report_typed(ParsingError::InvalidType("OpConstantComposite"))
        }
    }
}
