use crate::rap_info;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

pub struct RsProjectOption {
    pub tested_crate_path: PathBuf,
    pub tested_crate_name: String,
    pub project_path: PathBuf,
    pub project_name: String,
    pub verbose: bool,
}

/// Generator for fuzz driver projects.
pub struct CargoProjectBuilder {
    option: RsProjectOption,
}

pub struct RsProject {
    option: RsProjectOption,
}

impl CargoProjectBuilder {
    pub fn new(option: RsProjectOption) -> Self {
        Self { option }
    }

    pub fn build(self) -> io::Result<RsProject> {
        let project_path = self.option.project_path.as_path();

        // remove project path if it exists
        // if self.option.project_path.exists() {
        //     fs::remove_dir_all(self.option.project_path)?;
        // }

        // create the new project
        rap_info!("Creating new project at {}", project_path.display());

        let mut command = Command::new("cargo");
        command
            .arg("new")
            .arg(project_path)
            .arg("--vcs")
            .arg("none")
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

        // add dependencies to Cargo.toml
        self.update_cargo_toml(&project_path)?;

        rap_info!(
            "Successfully created fuzz driver project at: {}",
            project_path.display()
        );
        Ok(RsProject {
            option: self.option,
        })
    }

    fn update_cargo_toml(&self, project_path: &Path) -> io::Result<()> {
        let cargo_toml_path = project_path.join("Cargo.toml");
        let mut file = fs::OpenOptions::new()
            .write(true)
            .append(true)
            .open(cargo_toml_path)?;
        writeln!(
            file,
            "{} = {{ path = \"{}\" }}",
            self.option.tested_crate_name,
            self.option.tested_crate_path.display(),
        )?;
        Ok(())
    }
}

pub enum TestResult {
    FailInCheck(Option<i32>),
    RunSuccess(Option<i32>),
}

pub struct MiriReport {
    pub project_name: String,
    pub project_path: PathBuf,
    pub result: TestResult,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

pub fn miri_env_vars() -> &'static [(&'static str, &'static str)] {
    &[
        (
            "MIRIFLAGS",
            "-Zmiri-ignore-leaks -Zmiri-disable-stacked-borrows",
        ),
        ("RUSTFLAGS", "-Awarnings"),
        ("RUST_BACKTRACE", "1"),
    ]
}

pub fn miri_env_vars_str() -> String {
    miri_env_vars()
        .iter()
        .fold(String::new(), |s, (k, v)| {
            if v.contains(" ") {
                format!("{s} {k}=\"{v}\"")
            } else {
                format!("{s} {k}={v}")
            }
        })
        .trim()
        .to_owned()
}

impl MiriReport {
    pub fn reproduce_str(&self) -> String {
        format!(
            "cd {} && cargo check && {} cargo miri run",
            self.project_path.display(),
            miri_env_vars_str()
        )
    }

    pub fn get_retcode(&self) -> Option<i32> {
        match self.result {
            TestResult::FailInCheck(retcode) | TestResult::RunSuccess(retcode) => retcode,
        }
    }

    pub fn brief(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("Project Name: {}\n", self.project_name));
        s.push_str(&format!("Reproduce Line:\n{}\n", self.reproduce_str()));
        s.push_str(&format!("retcode = {:?} ", self.get_retcode()));

        match self.result {
            TestResult::FailInCheck(_) => {
                s.push_str("(fail in `cargo check`)\n");
            }
            TestResult::RunSuccess(Some(0)) => {
                s.push_str("\n");
                // no need to print any detail if success
                return s;
            }
            TestResult::RunSuccess(_) => {
                s.push_str("(Fail in `cargo miri`)\n");
            }
        }

        s.push_str(&format!(
            "stdout:{}\n",
            String::from_utf8_lossy(&self.stdout)
        ));
        s.push_str(&format!(
            "stderr:{}\n",
            String::from_utf8_lossy(&self.stderr)
        ));

        s
    }
}

impl RsProject {
    pub fn create_src_file(&self, file_name: &str, content: &str) -> io::Result<()> {
        let src_path = self.option.project_path.join("src").join(file_name);
        let mut file = File::create(src_path)?;
        file.write_all(content.as_bytes())?;
        Ok(())
    }

    pub fn run_miri(&self) -> io::Result<MiriReport> {
        let project_path = self.option.project_path.as_path();
        rap_info!("Running fuzz driver project at: {}", project_path.display());

        // first run `cargo check` to ensure the code can be compiled
        let mut command = Command::new("cargo");
        command
            .arg("check")
            .current_dir(&project_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        let output = command.output()?;
        match output.status.code() {
            Some(0) => {}
            retcode => {
                return Ok(MiriReport {
                    project_name: self.option.project_name.clone(),
                    project_path: self.option.project_path.clone(),
                    result: TestResult::FailInCheck(retcode),
                    stdout: output.stdout,
                    stderr: output.stderr,
                });
            }
        }

        let vars = miri_env_vars();
        let mut command = Command::new("cargo");
        command
            .arg("miri")
            .arg("run")
            .envs(vars.to_owned())
            .current_dir(&project_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let output = command.output()?;

        let retcode = output.status.code();

        Ok(MiriReport {
            project_name: self.option.project_name.clone(),
            project_path: self.option.project_path.clone(),
            result: TestResult::RunSuccess(retcode),
            stdout: output.stdout,
            stderr: output.stderr,
        })
    }
}
