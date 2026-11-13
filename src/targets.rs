//! The output targets, the libraries whose syntax the Lean text is written in. Each is a module
//! of `targets/` defining a `TARGET`, listed in `TARGETS`.

use serde::{Deserialize, Serialize};

use crate::input::Input;
use crate::verify::Certificate;

pub mod mathlib;

/// The output targets, in the order of the page's buttons. The first is the default.
pub const TARGETS: &[Target] = &[mathlib::TARGET];

/// An output target. It serializes without `render`, for the page (`wasm::targets`).
#[derive(Serialize)]
pub struct Target {
    /// The name in `--target`, `?target=` and the outputs' `target`.
    pub name: &'static str,
    /// The label of the target's button on the page.
    pub label: &'static str,
    /// What the text proves primality with, as the page's intro names it ("… proving p prime with
    /// Mathlib's `primality` tactic"). Code goes in backticks.
    pub tool: &'static str,
    /// The release the text was checked against, shown above the code (`None` for a library's
    /// development head).
    pub release: Option<&'static str>,
    /// An online editor whose default project has the library and which reads its code from the
    /// URL fragment `#code=…` (`None` when there is none).
    pub playground: Option<&'static str>,
    #[serde(skip)]
    pub render: Render,
}

/// The imported modules and the Lean text for a certificate `verify::verify` accepted, stating the
/// input as `input.term`. An error fails the run and hides every target's text, so a target must
/// state every certificate the driver produces.
pub type Render = fn(&Certificate, &Input) -> Result<(Vec<String>, String), String>;

/// The Lean file of the target named `target`, as the page's code block and the command-line tool
/// show it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Output {
    pub target: String,
    /// An import line per module the text needs, a blank line and the text.
    pub code: String,
}

impl Target {
    /// The output of this target (see `Render`). The error names the target.
    pub fn output(&self, cert: &Certificate, input: &Input) -> Result<Output, String> {
        let (imports, text) = (self.render)(cert, input)
            .map_err(|message| format!("the {} target: {message}", self.label))?;
        let imports: String = imports
            .iter()
            .map(|module| format!("import {module}\n"))
            .collect();
        Ok(Output {
            target: self.name.to_string(),
            code: format!("{imports}\n{text}"),
        })
    }
}

/// The target named `name`.
pub fn find(name: &str) -> Option<&'static Target> {
    TARGETS.iter().find(|target| target.name == name)
}

/// The output of every target, in the order of `TARGETS`, or the error of the first target whose
/// renderer fails.
pub fn render_outputs(cert: &Certificate, input: &Input) -> Result<Vec<Output>, String> {
    TARGETS
        .iter()
        .map(|target| target.output(cert, input))
        .collect()
}
