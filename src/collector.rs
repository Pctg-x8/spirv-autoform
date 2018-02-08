//! Data(Type/Operation) Collector

use {std, spv};
use std::ops::Deref;
use std::io::prelude::Write;
use module_loader::*;
use spvdefs::Id;
use std::fmt::Display;

pub struct ErrorReporter { pub has_error: bool }
impl ErrorReporter
{
    pub fn new() -> Self { ErrorReporter { has_error: false } }
    pub fn report<Msg: Display>(&mut self, msg: Msg)
    {
        writeln!(std::io::stderr(), "*Error* {}", msg).unwrap();
        self.has_error = true;
    }
}

pub struct CollectedData<'m>
{
    pub assigned: AssignedOperations<'m>, pub types: TypeAggregator<'m>
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
}
impl<'m> Deref for AssignedOperations<'m> { type Target = [Option<&'m Operation>]; fn deref(&self) -> &Self::Target { &self.0[..] } }

pub struct TypeAggregator<'n>(spv::TypedefMap<'n>);
impl<'n> TypeAggregator<'n>
{
    pub fn resolve_all(ops: &AssignedOperations<'n>, names: &'n NameMaps, err: &mut ErrorReporter) -> Self
    {
        let mut t = spv::TypedefMap::new();
        for (n, op) in ops.iter().enumerate().filter(|&(_, op)| op.map(Operation::is_type_op).unwrap_or(false))
        {
            if t.contains_key(&(n as Id)) { err.report(format!("Type Definition for ID {} has been found once more.", n)); }
            else
            {
                let r = Self::try_resolve(&mut t, ops, names, n as Id, &op.unwrap());
                t.insert(n as Id, r);
            }
        }
        TypeAggregator(t)
    }
    pub fn get(&self, id: Id) -> Option<&spv::Typedef<'n>> { self.0.get(&id) }

    fn lookup<'s>(sink: &'s mut spv::TypedefMap<'n>, ops: &AssignedOperations, names: &'n NameMaps, id: Id) -> &'s spv::Typedef<'n>
    {
        if !sink.contains_key(&id)
        {
            let resolved = Self::try_resolve(sink, ops, names, id, ops[id as usize].as_ref().unwrap());
            sink.insert(id, resolved);
        }
        sink.get(&id).as_ref().unwrap()
    }
    fn try_resolve(sink: &mut spv::TypedefMap<'n>, ops: &AssignedOperations, names: &'n NameMaps, id: Id, op: &Operation) -> spv::Typedef<'n>
    {
        let t = match op
        {
            &Operation::TypeVoid { .. } => spv::Type::Void,
            &Operation::TypeBool { .. } => spv::Type::Bool,
            &Operation::TypeInt { width, signedness, .. } => spv::Type::Int(width as u8, signedness),
            &Operation::TypeFloat { width, .. } => spv::Type::Float(width as u8),
            &Operation::TypeVector { component_type, component_count, .. }
                => spv::Type::Vector(component_count, Box::new(Self::lookup(sink, ops, names, component_type).clone())),
            &Operation::TypeMatrix { column_type, column_count, .. }
                => spv::Type::Matrix(column_count, Box::new(Self::lookup(sink, ops, names, column_type).clone())),
            &Operation::TypeArray { element_type, length, .. } => spv::Type::Array(length, Box::new(Self::lookup(sink, ops, names, element_type).clone())),
            &Operation::TypeRuntimeArray { element_type, .. } => spv::Type::DynamicArray(Box::new(Self::lookup(sink, ops, names, element_type).clone())),
            &Operation::TypePointer { ref storage, _type, .. }
                => spv::Type::Pointer(storage.clone(), Box::new(Self::lookup(sink, ops, names, _type).clone())),
            &Operation::TypeStruct { ref member_types, result } => spv::Type::Structure(spv::TyStructure
            {
                id: result, members: member_types.iter().enumerate()
                    .map(|(n, &x)| spv::StructureElement { name: names.lookup_member(id, n), _type: Self::lookup(sink, ops, names, x).clone() })
                    .collect()
            }),
            &Operation::TypeImage { sampled_type, ref dim, depth, arrayed, ms, sampled, ref format, ref qualifier, .. } => spv::Type::Image
            {
                sampled_type: Box::new(Self::lookup(sink, ops, names, sampled_type).clone()),
                dim: dim.clone(), depth: depth, arrayed: arrayed, ms: ms, sampled: sampled, format: format.clone(), qualifier: qualifier.clone()
            },
            &Operation::TypeSampler { .. } => spv::Type::Sampler,
            &Operation::TypeSampledImage { image_type, .. } => spv::Type::SampledImage(Box::new(Self::lookup(sink, ops, names, image_type).clone())),
            &Operation::TypeFunction { return_type, ref parameters, .. } => spv::Type::Function(
                Box::new(Self::lookup(sink, ops, names, return_type).clone()),
                parameters.iter().map(|&x| Self::lookup(sink, ops, names, x).clone()).collect()),
            _ => unreachable!("Unresolvable as a type: {:?}", op)
        };

        spv::Typedef { name: names.lookup_in_toplevel(id).map(From::from), def: t }
    }

    pub fn dump(&self)
    {
        println!("## Aggregated Types");
        for (n, t) in &self.0 { println!("- {}: {:?}", n, t); }
    }
}
