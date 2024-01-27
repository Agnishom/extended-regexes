import Lake
open Lake DSL

package regex {
  -- add package configuration options here
}

lean_lib Regex

@[default_target]
lean_exe regex where
  root := `Regex.Regex

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
