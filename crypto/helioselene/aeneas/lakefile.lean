import Lake
open Lake DSL

-- The Aeneas Lean library, shipped with the Aeneas nightly release
-- (https://github.com/AeneasVerif/aeneas, release nightly-2026.07.06-45061fa).
-- Adjust this path to wherever the release tarball was extracted.
require aeneas from "/home/user/aeneas-toolchain/aeneas-bin/backends/lean"

package «helioselene-core» where

@[default_target] lean_lib «HelioseleneCore» where
  globs := #[.one `HelioseleneCore, .submodules `HelioseleneCore]
