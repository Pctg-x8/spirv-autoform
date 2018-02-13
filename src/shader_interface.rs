//! Shader Interface

use {std, spv, spvdefs};
use container_ext::*;
use module_loader::*;
use collector::*;
use spvdefs::Id;
use std::collections::BTreeMap;
use std::borrow::*;

use std::fmt::{Display, Formatter, Result as FmtResult};

#[derive(Clone, Debug)]
pub enum Descriptor<'n>
{
    Empty, UniformBuffer(&'n spv::Typedef<'n>), SampledImage(&'n spv::Typedef<'n>)
}
impl<'n> Descriptor<'n>
{
    pub fn uniform_buffer(&self) -> Option<&'n spv::Typedef<'n>>
    {
        if let &Descriptor::UniformBuffer(b) = self { Some(b) } else { None }
    }
}
impl<'n> HasPlaceholder for Descriptor<'n> { fn placeholder() -> Self { Descriptor::Empty } }
pub struct DescriptorSet<'n>(BTreeMap<u32, AutosizeVec<Descriptor<'n>>>);
pub struct DescriptorSetSlots<'n>(BTreeMap<u32, DescriptorSet<'n>>);
impl<'n> DescriptorSetSlots<'n>
{
    fn new() -> Self { DescriptorSetSlots(BTreeMap::new()) }
    pub fn binding(&self, binding: u32) -> Option<&DescriptorSet<'n>> { self.0.get(&binding) }
    fn binding_entry(&mut self, binding: u32) -> &mut DescriptorSet<'n>
    {
        self.0.entry(binding).or_insert_with(DescriptorSet::new)
    }
    fn iter(&self) -> std::collections::btree_map::Iter<u32, DescriptorSet<'n>> { self.0.iter() }
}
impl<'n> DescriptorSet<'n>
{
    fn new() -> Self { DescriptorSet(BTreeMap::new()) }
    pub fn set_index(&self, index: u32) -> Option<&[Descriptor<'n>]> { self.0.get(&index).map(|x| &x[..]) }
    fn set_entry(&mut self, index: u32) -> &mut AutosizeVec<Descriptor<'n>>
    {
        self.0.entry(index).or_insert_with(AutosizeVec::new)
    }
    fn iter(&self) -> std::collections::btree_map::Iter<u32, AutosizeVec<Descriptor<'n>>> { self.0.iter() }
}
#[derive(Clone, Debug)]
struct SpirvVariableRef<'n> { path: Vec<&'n str>, ty: &'n spv::Typedef<'n> }
impl<'n> Display for SpirvVariableRef<'n>
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult { write!(fmt, "{}: {}", self.path.join("::"), self.ty) }
}
#[derive(Debug)]
struct SpirvConstantVariable<'n> { name: &'n str, ty: &'n spv::Typedef<'n>, value: Box<ConstantValue> }
impl<'n> Display for SpirvConstantVariable<'n>
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult { write!(fmt, "{}: {} = {:?}", self.name, self.ty, self.value) }
}

#[derive(Debug, Clone, Copy)]
enum NameId { Toplevel(Id), Member(Id, u32) }
impl NameId
{
    pub fn path<'m>(self, module: &'m SpirvModule) -> Vec<&'m str>
    {
        match self
        {
            NameId::Toplevel(id) => vec![module.names.lookup_in_toplevel(id).unwrap_or("<anon>")],
            NameId::Member(pid, index) => vec![module.names.lookup_in_toplevel(pid).unwrap_or("<Anon>"), module.names.lookup_member(pid, index as _).unwrap_or("<anon>")]
        }
    }
    pub fn decorations<'m>(self, module: &'m SpirvModule) -> Option<Cow<'m, DecorationSet>>
    {
        let baseid = match self { NameId::Toplevel(id) | NameId::Member(id, _) => id };
        let basedeco = module.decorations.lookup_in_toplevel(baseid);
        match self
        {
            NameId::Toplevel(_) => basedeco.map(Cow::Borrowed), NameId::Member(_, index) => if let Some(bd) = basedeco
            {
                let mut decos = bd.clone(); if let Some(v) = module.decorations.lookup_member(baseid, index as _) { for (&id, dec) in v.iter() { decos.register(id, dec.clone()); } } Some(Cow::Owned(decos))
            }
            else { module.decorations.lookup_member(baseid, index as _).map(Cow::Borrowed) }
        }
    }
}
impl Display for NameId
{
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult
    {
        match *self { NameId::Toplevel(id) => id.fmt(fmt), NameId::Member(pid, index) => write!(fmt, "{}::{}", pid, index) }
    }
}
impl<'n> SpirvVariableRef<'n>
{
    fn from(varname: NameId, varty: Id, module: &'n SpirvModule, types: &'n TypeAggregator<'n>) -> Self
    {
        SpirvVariableRef { path: varname.path(module), ty: types.require(varty) }
    }
}

pub struct ShaderInterface<'m>
{
    module: &'m SpirvModule, collected: &'m CollectedData<'m>,
    exec_model: spvdefs::ExecutionModel, inputs: BTreeMap<Id, SpirvVariableRef<'m>>, builtins: BTreeMap<spvdefs::BuiltIn, Vec<SpirvVariableRef<'m>>>,
    outputs: BTreeMap<Id, SpirvVariableRef<'m>>, pub descriptors: DescriptorSetSlots<'m>,
    input_attachments: BTreeMap<u32, Vec<SpirvVariableRef<'m>>>,
    spec_constants: BTreeMap<u32, SpirvConstantVariable<'m>>
}
enum RegistrationExcepts<'r>
{
    DuplicateLocation(u32, &'r SpirvVariableRef<'r>), MissingDescription, Undecorated
}

impl<'m> ShaderInterface<'m>
{
    pub fn make(module: &'m SpirvModule, collected: &'m CollectedData<'m>, er: &mut ErrorReporter) -> Result<Self, SpirvReadError>
    {
        let mut this = ShaderInterface
        {
            module, collected, exec_model: spvdefs::ExecutionModel::Vertex,
            inputs: BTreeMap::new(), builtins: BTreeMap::new(), outputs: BTreeMap::new(),
            descriptors: DescriptorSetSlots::new(), input_attachments: BTreeMap::new(), spec_constants: BTreeMap::new()
        };
        // Getting all input/output/descripted variables or pointers
        for op in module.operations.iter()
        {
            match *op
            {
                Operation::EntryPoint { model, .. } => { this.exec_model = model; },
                Operation::Variable { storage: spvdefs::StorageClass::Input, result, .. } => match this.register_input(module, &collected.types, NameId::Toplevel(result.id), result.ty).err()
                {
                    Some(RegistrationExcepts::Undecorated) => println!("Warning: Undecorated input variable (#{})", result.id),
                    Some(RegistrationExcepts::MissingDescription) => println!("Warning: A non-builtin input variable found that has no location (#{})", result.id),
                    Some(RegistrationExcepts::DuplicateLocation(l, v)) => er.report(format!("Input #{} has been found twice (previous declaration was for {:?})", l, v.path)),
                    None => ()
                },
                Operation::Variable { storage: spvdefs::StorageClass::Output, result, .. } => match this.register_output(module, &collected.types, NameId::Toplevel(result.id), result.ty).err()
                {
                    Some(RegistrationExcepts::Undecorated) => println!("Warning: Undecorated output variable (#{})", result.id),
                    Some(RegistrationExcepts::MissingDescription) => println!("Warning: A non-builtin output variable found that has no location (#{})", result.id),
                    Some(RegistrationExcepts::DuplicateLocation(l, v)) => er.report(format!("Output #{} has been found twice (previous declaration was for {:?})", l, v.path)),
                    None => ()
                },
                Operation::Variable { storage, ref result, .. } if storage == spvdefs::StorageClass::Uniform || storage == spvdefs::StorageClass::UniformConstant =>
                {
                    let decos = if let Some(d) = module.decorations.lookup_in_toplevel(result.id) { d }
                        else { println!("Warning: Undecorated Uniform/UniformConstant Variable: {}", result.id); continue; };
                    let ty = collected.types.require(result.ty);
                    let content_ty = ty.dereference().expect("<MODULE CORRUPTION> Uniform/UniformConstant requires a pointer type");
                    if let spv::Type::Image { dim: spvdefs::Dim::SubpassData, .. } = content_ty.def
                    {
                        // input attachment
                        match decos.input_attachment_index()
                        {
                            Some(iax) => this.input_attachments.entry(iax).or_insert_with(Vec::new).push(SpirvVariableRef { path: vec![module.names.lookup_in_toplevel(result.id).unwrap()], ty }),
                            _ => er.report("Require `input_attachment_index` decoration for SubpassData")
                        }
                    }
                    else
                    {
                        match (decos.descriptor_bound_index(), decos.descriptor_set_index())
                        {
                            (Some(b), Some(s)) =>
                            {
                                let array_index = decos.array_index().unwrap_or(0);
                                let desc = if let spv::Type::SampledImage(ref si) = content_ty.def { Descriptor::SampledImage(si) } else { Descriptor::UniformBuffer(content_ty) };
                                this.descriptors.binding_entry(b).set_entry(s).set(array_index as _, desc);
                            },
                            (None, Some(_)) => er.report("Required `binding` decoration for Uniform".to_owned()),
                            (Some(_), None) => er.report("Required `set` decoration for Uniform".to_owned()),
                            (None, None) => er.report("Required `binding` and `set` decorations for Uniform".to_owned())
                        }
                    }
                },
                Operation::TypePointer { storage: spvdefs::StorageClass::Output, _type: parent_id, .. } => if let &spv::Typedef { def: spv::Type::Structure(ref m), .. } = collected.types.require(parent_id)
                {
                    for (nid, m) in m.members.iter().enumerate().map(|(n, m)| (NameId::Member(parent_id, n as _), m))
                    {
                        match this.register_output(module, &collected.types, nid, m.tyid).err()
                        {
                            Some(RegistrationExcepts::Undecorated) => println!("Warning: Undecorated output variable (#{})", nid),
                            Some(RegistrationExcepts::MissingDescription) => println!("Warning: A non-builtin output variable found that has no location (#{})", nid),
                            Some(RegistrationExcepts::DuplicateLocation(l, v)) => er.report(format!("Output #{} has been found twice (previous declaration was for {:?})", l, v.path)),
                            None => ()
                        }
                    }
                },
                Operation::TypePointer { storage: spvdefs::StorageClass::Input, _type: parent_id, .. } => if let &spv::Typedef { def: spv::Type::Structure(ref m), .. } = collected.types.require(parent_id)
                {
                    for (nid, m) in m.members.iter().enumerate().map(|(n, m)| (NameId::Member(parent_id, n as _), m))
                    {
                        match this.register_input(module, &collected.types, nid, m.tyid).err()
                        {
                            Some(RegistrationExcepts::Undecorated) => println!("Warning: Undecorated input variable (#{})", nid),
                            Some(RegistrationExcepts::MissingDescription) => println!("Warning: A non-builtin input variable found that has no location (#{})", nid),
                            Some(RegistrationExcepts::DuplicateLocation(l, v)) => er.report(format!("Input #{} has been found twice (previous declaration was for {:?})", l, v.path)),
                            None => ()
                        }
                    }
                },
                _ => ()
            }
        }
        let mut spec_constants = BTreeMap::new();
        for (&id, c) in collected.constants.specialized.iter()
        {
            let sid = if let Some(s) = module.decorations.lookup_in_toplevel(id).and_then(DecorationSet::spec_id) { s }
                else { println!("Warning: OpSpecConstant** #{} is not decorated by SpecId", id); continue; };
            if spec_constants.contains_key(&sid) { println!("Warning: Duplicated specialization constant id {}", sid); continue; }

            let name = module.names.lookup_in_toplevel(id).unwrap_or("<anon>");
            let ty = collected.types.require(collected.assigned.at(id).expect("Referring illegal id").result_type().expect("Could not find a result type"));
            spec_constants.insert(sid, SpirvConstantVariable { name, ty, value: c.clone_inner() });
        }

        Ok(this)
    }
    fn register_input(&mut self, module: &'m SpirvModule, types: &'m TypeAggregator<'m>, nameid: NameId, tyid: Id) -> Result<(), RegistrationExcepts>
    {
        let decos = if let Some(d) = nameid.decorations(module) { d } else { return Err(RegistrationExcepts::Undecorated); };
        if let Some(loc) = decos.location()
        {
            use std::collections::btree_map::Entry;
            match self.inputs.entry(loc)
            {
                Entry::Occupied(e) => Err(RegistrationExcepts::DuplicateLocation(loc, e.into_mut())),
                Entry::Vacant(v) => { v.insert(SpirvVariableRef::from(nameid, tyid, module, types)); Ok(()) }
            }
        }
        else if let Some(b) = decos.builtin() { self.builtins.entry(b).or_insert_with(Vec::new).push(SpirvVariableRef::from(nameid, tyid, module, types)); Ok(()) }
        else { Err(RegistrationExcepts::MissingDescription) }
    }
    fn register_output(&mut self, module: &'m SpirvModule, types: &'m TypeAggregator<'m>, nameid: NameId, tyid: Id) -> Result<(), RegistrationExcepts>
    {
        let decos = if let Some(d) = nameid.decorations(module) { d } else { return Err(RegistrationExcepts::Undecorated) };
        if let Some(loc) = decos.location()
        {
            use std::collections::btree_map::Entry;
            match self.outputs.entry(loc)
            {
                Entry::Occupied(e) => Err(RegistrationExcepts::DuplicateLocation(loc, e.into_mut())),
                Entry::Vacant(v) => { v.insert(SpirvVariableRef::from(nameid, tyid, module, types)); Ok(()) }
            }
        }
        else if let Some(b) = decos.builtin() { self.builtins.entry(b).or_insert_with(Vec::new).push(SpirvVariableRef::from(nameid, tyid, module, types)); Ok(()) }
        else { Err(RegistrationExcepts::MissingDescription) }
    }
    pub fn dump(&self)
    {
        println!("## ShaderInterface");
        println!("- Execution Model: {:?}", self.exec_model);
        println!("- Inputs: ");
        for (l, v) in self.inputs.iter() { println!("-- #{}: {}", l, v); }
        println!("- Outputs: ");
        for (l, v) in self.outputs.iter() { println!("-- #{}: {}", l, v); }
        println!("- Built-Ins: ");
        for (l, v) in self.builtins.iter().filter(|&(_, v)| !v.is_empty())
        {
            println!("-- {:?}: {:?}", l, v.iter().map(ToString::to_string).collect::<Vec<_>>());
        }
        println!("- Descriptors: ");
        for (b, ds) in self.descriptors.iter()
        {
            println!("-- Descriptor Bound #{}", b);
            for (s, da) in ds.iter()
            {
                println!("-- set {}: {:?}", s, da);
            }
        }
        println!("- Input Attachments: ");
        for (x, ia) in self.input_attachments.iter()
        {
            println!("-- #{}: {:?}", x, ia.iter().map(ToString::to_string).collect::<Vec<_>>());
        }
        println!("- Specialized Constants: ");
        for (x, c) in self.spec_constants.iter()
        {
            println!("-- #{}: {}", x, c);
        }
    }
    pub fn find_typedef(&self, name: &str) -> Option<&'m spv::Typedef<'m>>
    {
        self.module.names.find_toplevel_id(name).and_then(|id| self.collected.types.get(id))
    }
}

#[derive(Debug, Clone)]
pub struct PlacedStructureMember<'s>
{
    pub name: &'s str, pub offset: usize, pub tyid: Id
}
impl<'m> ShaderInterface<'m>
{
    pub fn structure_layout_for(&self, structure: &spv::TyStructure<'m>, decorations: &DecorationMaps) -> Vec<PlacedStructureMember<'m>>
    {
        structure.members.iter().enumerate().map(|(i, m)|
        {
            let offset = if let Some(decos) = decorations.lookup_member(structure.id, i)
            {
                if let Some(o) = decos.offset() { o as _ }
                else { println!("Warning: Undecorated member by Offset"); 0 }
            } else { println!("Warning: No decorations for member"); 0 };
            PlacedStructureMember { name: m.name.unwrap(), tyid: m.tyid, offset }
        }).collect()
    }
}
