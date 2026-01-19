import Lake
open Lake DSL

package «geolog-proofs» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

-- Import model-theory-topos from GitHub
require «model-theory-topos» from git
  "https://github.com/kyoDralliam/model-theory-topos.git" @ "main"

@[default_target]
lean_lib «GeologProofs» where
  globs := #[.submodules `GeologProofs]
