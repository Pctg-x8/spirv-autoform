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
            collected.types.dump();
            collected.constants.dump();
            let sinterface = ShaderInterface::make(&module, &collected, &mut err).unwrap();
            sinterface.dump();
            
            let um_structure = sinterface.find_typedef("UniformMemory").and_then(Typedef::structure).unwrap();
            let st = sinterface.structure_layout_for(um_structure, &module.decorations);
            for ps in st { println!("* {} => {}: {}", ps.offset, ps.name, ps.ty); }
            println!("UniformMemory::enemy_instance_data = {:?}", um_structure.find_member("enemy_instance_data"));
        },
        None => show_help()
    }
}
fn show_help()
{
    println!("usage>app [inputFilePath]");
}

