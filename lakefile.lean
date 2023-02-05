import Lake
open Lake DSL

package «decision» {
  -- add package configuration options here
}

lean_lib «Decision» {
  -- add library configuration options here
}

require mathlib4 from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_exe «decision» {
  root := `Main
}
