import Lake
open Lake DSL

package «enrichment» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «Enrichment» {
  -- add library configuration options here
}