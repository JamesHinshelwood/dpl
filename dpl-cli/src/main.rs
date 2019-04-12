use dpl::parse_term;
use std::fs;
use std::io;
use std::io::Read;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(StructOpt, Debug)]
#[structopt(name = "dpl")]
struct Opt {
    /// Source file
    #[structopt(name = "FILE")]
    file: Option<PathBuf>,
}

fn main() -> io::Result<()> {
    let opt = Opt::from_args();

    let term = if let Some(path) = opt.file {
        fs::read_to_string(path)?
    } else {
        let mut term = String::new();
        io::stdin().read_to_string(&mut term)?;
        term
    };

    match parse_term(&term) {
        Ok(term) => {
            let ty = term.infer_type();

            println!("{}", term);
            match ty {
                Ok(ty) => {
                    println!("has type");
                    println!("{}", ty);
                }
                Err(err) => {
                    println!("type error");
                    println!("{}", err);
                }
            }
        }
        Err(err) => {
            println!("Parse error");
            println!("{}", err);
        }
    }
    Ok(())
}
