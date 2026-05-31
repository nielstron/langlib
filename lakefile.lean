import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

-- API documentation generator. Only fetched/built when `-Kdoc=on` is passed
-- (e.g. in the documentation CI workflow), so the normal build is unaffected.
meta if get_config? doc = some "on" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.28.0"

package langlib where
  testDriver := "LanglibTest"

@[default_target]
lean_lib Langlib where
  srcDir := "src"

lean_lib LanglibTest where
  srcDir := "test"
  roots := #[`LanglibTest]
