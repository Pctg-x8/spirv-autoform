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
            let sinterface = ShaderInterface::make(&module, &collected, &mut err).unwrap();
            sinterface.dump();
            let st = sinterface.structure_layout_for(sinterface.descriptors.binding(0).unwrap().set_index(0).unwrap()[0].uniform_buffer().unwrap().def.structure().unwrap(), &module.decorations);
            for ps in st { println!("* {} => {}: {}", ps.offset, ps.name, ps.ty); }
        },
        None => show_help()
    }
}
fn show_help()
{
    println!("usage>app [inputFilePath]");
}

