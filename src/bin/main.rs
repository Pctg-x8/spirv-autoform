extern crate spirv_autoform;
use spirv_autoform::*;
use std::io::BufReader;

fn main()
{
    match std::env::args().nth(1)
    {
        Some(n) =>
        {
            let module = std::fs::File::open(n).map(BufReader::new).map_err(From::from).and_then(SpirvModule::load).unwrap();
            module.dump();
            let mut err = ErrorReporter::new();
            let ao = AssignedOperations::collect(&module);
            let types = TypeAggregator::resolve_all(&ao, &module.names, &mut err);
            let constants = ConstantCollector::collect(&ao, &types, &mut err);
            let collected = CollectedData { types, constants, assigned: ao };
            if err.has_error { panic!("Some errors occured"); }
            collected.types.dump(&module);
            collected.constants.dump();
            let sinterface = ShaderInterface::make(&module, &collected, &mut err).unwrap();
            sinterface.dump();

            println!("# Variables in Input storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::Input)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in Output storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::Output)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in Uniform storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::Uniform)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in UniformConstant storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::UniformConstant)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in Workgroup storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::Workgroup)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in Private storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::Private)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in Function storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::Function)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in Generic storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::Generic)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in AtomicCounter storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::AtomicCounter)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in PushConstant storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::PushConstant)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("# Variables in Image storage");
            for (res, init) in sinterface.iter_variables(spvdefs::StorageClass::Image)
            {
                println!("- {}: {} = {:?}", module.names.lookup_in_toplevel(res.id).unwrap_or("_"), collected.types.require(res.ty), init);
                if let Some(d) = module.decorations.lookup_in_toplevel(res.id) { println!("-- Decorations: {}", d); }
            }
            println!("");
            
            /*let um_structure = sinterface.find_typedef("UniformMemory").and_then(Typedef::structure).unwrap();
            let st = sinterface.structure_layout_for(um_structure, &module.decorations);
            println!("# Layout for UniformMemory");
            for ps in st { println!("* {} => {}: ty#{}", ps.offset, ps.name, ps.tyid); }
            println!("UniformMemory::enemy_instance_data = {:?}", um_structure.find_member("enemy_instance_data"));*/
        },
        None => show_help()
    }
}
fn show_help()
{
    println!("usage>app [inputFilePath]");
}

