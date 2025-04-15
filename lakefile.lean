import Lake
open Lake DSL

package «braid_project» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  moreGlobalServerArgs := #[
    "--load-dynlib", "./.lake/packages/Canonical/.lake/build/lib/libcanonical.dylib",
    "--load-dynlib", "./.lake/packages/Canonical/.lake/build/lib/lean/Canonical.dylib"
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Canonical from git
  "https://github.com/chasenorman/CanonicalLean.git"

@[default_target]
lean_lib «BraidProject» where
  -- add any library configuration options here
