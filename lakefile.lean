import Lake
open Lake DSL

package «ssi» where
  version := v!"1.0.0"

@[default_target]
lean_lib «SSI» where
  -- roots default to `SSI`
