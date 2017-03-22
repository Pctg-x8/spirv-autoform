use std::io::BufReader;

mod container_ext;
mod spvdefs;
mod spv;

mod module_loader;
use module_loader::*;
mod collector;
use collector::*;
mod shader_interface;
use shader_interface::*;

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
            let collected = CollectedData
            {
                types: TypeAggregator::resolve_all(&ao, &module.names, &mut err),
                assigned: ao
            };
            if err.has_error { panic!("Some errors occured"); }
            let sinterface = ShaderInterface::make(&module, &collected, &mut err).unwrap();
            sinterface.dump();
        },
        None => show_help()
    }
}
fn show_help()
{
    println!("usage>app [inputFilePath]");
}

