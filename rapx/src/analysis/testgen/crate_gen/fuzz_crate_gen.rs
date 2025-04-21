use crate::analysis::opt::Opt;
use crate::rap_info;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;

pub struct FuzzProjectOption {
    pub crate_name: String,
    pub output_dir: Option<PathBuf>,
    pub verbose: bool,
}

impl FuzzProjectOption {
    pub fn crate_name(&self) -> &String {
        &self.crate_name
    }
    pub fn output_dir(&self) -> &Option<PathBuf> {
        &self.output_dir
    }
    pub fn verbose(&self) -> bool {
        self.verbose
    }
}

/// Generator for fuzz driver projects.
pub struct FuzzProjectGenerator {
    option: FuzzProjectOption,
    generated_path: Option<PathBuf>,
}

impl FuzzProjectGenerator {
    /// 创建新的项目生成器
    pub fn new(option: FuzzProjectOption) -> Self {
        Self {
            option,
            generated_path: None,
        }
    }

    pub fn generate(&mut self, rs_str: &str) -> io::Result<PathBuf> {
        // new crate name
        let crate_name = format!("{}_fuzz_driver", self.option.crate_name());

        let output_dir = match &self.option.output_dir() {
            Some(dir) => dir.clone(),
            None => {
                let current_dir = std::env::current_dir()?;
                let parent_dir = match current_dir.parent() {
                    Some(parent) => parent.to_path_buf(),
                    None => {
                        return Err(io::Error::new(
                            io::ErrorKind::Other,
                            "Failed to get parent directory",
                        ));
                    }
                };
                parent_dir
            }
        };

        let crate_path = output_dir.join(&crate_name);

        // check if the project already exists
        if crate_path.exists() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!(
                    "crate '{}' already exists, please delete and retry!",
                    crate_name
                ),
            ));
        }

        // create the new project
        rap_info!("Creating new project: {}", crate_name);
        let mut command = Command::new("cargo");
        command
            .arg("new")
            .arg(&crate_name)
            .current_dir(&output_dir)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let process = command.spawn()?;
        let output = process.wait_with_output()?;

        if !output.status.success() {
            let error = String::from_utf8_lossy(&output.stderr);
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Failed to create cargo project: {}", error),
            ));
        }

        // write the Rust code to main.rs
        let main_path = crate_path.join("src").join("main.rs");
        let mut main_file = File::create(main_path)?;
        main_file.write_all(rs_str.as_bytes())?;

        // add dependencies to Cargo.toml
        self.update_cargo_toml(&crate_path)?;

        self.generated_path = Some(crate_path.clone());
        rap_info!(
            "Successfully created fuzz driver project at: {}",
            crate_path.display()
        );
        Ok(crate_path)
    }

    fn update_cargo_toml(&self, project_path: &Path) -> io::Result<()> {
        let cargo_toml_path = project_path.join("Cargo.toml");
        let mut file = fs::OpenOptions::new()
            .write(true)
            .append(true)
            .open(cargo_toml_path)?;
        writeln!(
            file,
            "{} = {{ path = \"../{}\" }}",
            self.option.crate_name(),
            self.option.crate_name(),
        )?;
        Ok(())
    }

    pub fn run(&self) -> io::Result<()> {
        let path = match &self.generated_path {
            Some(path) => path,
            None => {
                return Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    "No project has been generated yet",
                ));
            }
        };
        rap_info!("Running fuzz driver project at: {}", path.display());
        let crate_path = path.clone();
        let verbose = self.option.verbose();

        thread::spawn(move || {
            let mut command = Command::new("cargo");
            command
                .arg("run")
                .current_dir(&crate_path)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped());

            if verbose {
                command.arg("--verbose");
                rap_info!(
                    "Executing: cargo run --verbose (in {})",
                    crate_path.display()
                );
            } else {
                rap_info!("Executing: cargo run (in {})", crate_path.display());
            }

            match command.spawn() {
                Ok(process) => match process.wait_with_output() {
                    Ok(output) => {
                        let status = output.status;
                        let stdout = String::from_utf8_lossy(&output.stdout);
                        let stderr = String::from_utf8_lossy(&output.stderr);

                        if status.success() {
                            rap_info!("Project executed successfully");
                            if !stdout.is_empty() {
                                rap_info!("Standard output:\n{}", stdout);
                            }
                        } else {
                            rap_info!("Project execution failed with status: {}", status);
                            if !stderr.is_empty() {
                                rap_info!("Error output:\n{}", stderr);
                            }
                            if !stdout.is_empty() && verbose {
                                rap_info!("Standard output:\n{}", stdout);
                            }
                        }
                    }
                    Err(e) => {
                        rap_info!("Failed to get command output: {}", e);
                    }
                },
                Err(e) => {
                    rap_info!("Failed to execute command: {}", e);
                }
            }
        });

        Ok(())
    }
}
