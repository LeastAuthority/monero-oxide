# Aeneas translation of the helioselene verified field arithmetic and the Selene and Helios group-law cores

This directory contains a Lean 4 model of `crypto/helioselene`'s
`field::verified` module — the code
[formally verified by Veridise in Dafny](https://github.com/VeridiseAuditing/helioselene-dafny-proofs)
per the header of `src/field/verified/mod.rs` — and, since the widened
second (2026-07-07), third (2026-07-08), and fifth (2026-07-10)
translation runs, of `verified::sqrt`, the **Selene and Helios group-law
cores**, and both curves' scalar-multiplication ladders from
`src/point.rs`, mechanically translated from
the Rust source with [Charon](https://github.com/AeneasVerif/charon) (MIR →
LLBC extraction) and [Aeneas](https://github.com/AeneasVerif/aeneas) (LLBC →
pure Lean functions).

The model is a **functional** model: it captures input/output behaviour
(including panics and non-termination) of the Rust functions under one fixed
build configuration, and nothing else. Section
[Assumptions required for equivalence](#assumptions-required-for-equivalence)
enumerates exactly what has to be trusted, assumed, or supplied before a Lean
theorem about this model says anything about the compiled Rust.

For a human review, start with [`HUMAN_AUDIT_TASK.md`](HUMAN_AUDIT_TASK.md).
It combines every proof assumption, explicit/compiler-generated axiom,
external semantic model, production or translation-only Rust change, domain
restriction, and erased/out-of-scope property into one evidence-driven audit
checklist. The three `human_audit_assumptions*.txt` files remain the detailed
historical ledgers behind that task.

## 1. Overview

### What was translated

Translation roots (unchanged since the third run; latest extraction is the
fifth run, 2026-07-10, see [§3](#3-toolchain-and-provenance)):
`helioselene::field::verified`, `helioselene::point::selene` **and**
`helioselene::point::helios`, i.e. everything reachable from those modules
except the explicit exclusions below. Concretely,
`HelioseleneCore/Funs.lean` contains definitions for:

- **Reduction** (`src/field/verified/red.rs`): `red256`, `red512`, and the
  constant `TWO_MODULUS_255_DISTANCE`.
- **Inversion** (`src/field/verified/invert.rs`): `invert`, its inner `step`
  (with inner `select` and the constant `MODULUS_XOR_TWO_MODULUS`), and
  `sub_with_bounded_overflow`.
- **Square root** (`src/field/verified/sqrt.rs`, NEW with the second run):
  `sqrt` (with its five extracted loops `sqrt_loop0` … `sqrt_loop4`) and the
  constant `MODULUS_PLUS_ONE_DIV_FOUR`. Its bitvec iterator chain was
  rewritten to an index loop in the translation patch ([§4](#4-changes-made-to-the-rust-code), hunk 5).
- **Field operations** (`src/field/verified/mod.rs`): the `Add`, `Sub`,
  `Neg`, `Mul` trait impls for `HelioseleneField`, `double`, `square`,
  `is_zero`, `is_odd`, `from_repr` (with its inner `reduced`), `to_repr`,
  the helpers `add_with_bounded_overflow`, `select_word`, `sub_value`,
  `red1`, and the constant `MODULUS_255_DISTANCE`.
- **Items from `src/field/mod.rs` pulled in by the call graph**: the
  `MODULUS` constant, `HelioseleneField`'s
  `ConditionallySelectable::conditional_select`, the `ff::Field`
  associated items `ZERO` and `is_zero` (used by `Neg` and `invert`), and —
  NEW with the second run — `from_u256`, `ct_eq` (`ConstantTimeEq`),
  `PartialEq::eq`, the `ff::Field` items `ONE`/`double`/`square`/`invert`/
  `sqrt`, the `ff::PrimeField` items `is_odd`/`from_repr`/`to_repr`, and the
  derived `Clone`/`Copy`/`Default`/`Debug` instance records.
- **The Selene group-law core** (`src/point.rs` via the `curve!` macro, NEW
  with the second run): the `point.selene.*` namespace — the constants `B`,
  `G_X`, `G_Y`, the generator `G`, `curve_equation`, `recover_y`,
  `SelenePoint.from_xy`, the `Add`/`Sub`/`Neg` (and `AddAssign`/`SubAssign`,
  owned and shared) impls, `Group::{identity, double, generator,
  is_identity}`, `ConstantTimeEq::ct_eq`, `PartialEq::eq`,
  `ConditionallySelectable::conditional_select`, and
  `GroupEncoding::{from_bytes, to_bytes}` (60 new `point.selene.*`
  declarations). In total the second run added 130 new `Funs.lean`
  declarations (the 60 above, 12 `field.verified.sqrt.*`, and 58
  field-layer/`dalek_ff_group` trait-instance records and helpers) and 20
  new `Types.lean` trait/type declarations (see `MAPPING.md`, appended
  section, for the per-declaration index).
- **The Helios group-law core** (`src/point.rs` via the same `curve!`
  macro, NEW with the third run, 2026-07-08): the `point.helios.*`
  namespace — the same item list as for Selene (constants `B`, `G_X`,
  `G_Y`, the generator `G`, `curve_equation`, `recover_y`,
  `HeliosPoint.from_xy`, the `Add`/`Sub`/`Neg` (and
  `AddAssign`/`SubAssign`, owned and shared) impls, `Group::{identity,
  double, generator, is_identity}`, `ct_eq`, `PartialEq::eq`,
  `conditional_select`, and `GroupEncoding::{from_bytes, to_bytes}`) — 60
  new `point.helios.*` declarations. Helios' coordinate type is the
  foreign `dalek_ff_group::FieldElement` (the 25519 field — see §5c for
  the idealized boundary this creates), and `HelioseleneField` is its
  *scalar* type, so the third run also materialised `HelioseleneField`'s
  `ff::Field`/`ff::PrimeField`/`Assign`-variant trait records (38 new
  declarations, required as `Group` scalar evidence for `HeliosPoint`) and
  one `&`-`Neg` record for `FieldElement`. In total the third run added 99
  new `Funs.lean` declarations and 4 new `Types.lean` declarations, plus
  20 new externals (§5c); see `MAPPING.md`'s 2026-07-08 appendix for the
  per-declaration index.
- **Scalar multiplication for both curves** (`src/point.rs`, NEW with the
  fifth run, 2026-07-10): the owned and shared `Mul`/`MulAssign` impls,
  including concrete `mul_loop.body`/`mul_loop` definitions for Selene and
  Helios, plus the translated `point.clear_scalar_bit` helper. These are 21
  concrete scalar-related declarations in `Funs.lean` (13 declarations net
  new; the eight trait records already existed) and replace the eight former
  existence-only point-scalar axioms. The translation-only Rust rewrite is
  recorded and justified line by line in §4 hunk 8. This extraction adds the
  executable ladder. `Spec/ScalarMul.lean` exposes each generated ladder through
  an exact result-valued Lean `SMul` adapter and proves definitionally (through
  the generic `resultSmul_ok`, whose proof is `rfl`) that acting on `.ok point`
  calls that generated body. `Spec/ScalarMulLaws.lean` then proves both complete
  generated ladders (precomputation, 256 loop iterations, scalar-byte cleanup
  and scalar cleanup) total and equal to natural repeated addition in the
  corresponding verified quotient group. It descends those generated results
  to law-bearing `SMul` actions and supplies unconditional `DistribSMul` laws.
  The scalar-ring laws are packaged as `Module` instances conditional on the
  exact still-external curve-exponent statements; no order axiom or certificate
  is introduced (details and theorem names in §7).

All of this translated with **zero `sorry`s** in the generated model, and the
hand-written proof tree under `HelioseleneCore/Spec/` is also **sorry-free**
as of 2026-07-10 (`Invert.step_congruence` and `Selene.sqrt_complete` are
both proved; see [§7](#7-formalization-status-2026-07-10)). The resulting
Lean package builds (`lake build`; `.olean` artifacts for
all modules are present in `.lake/build`). Rust `for` loops are extracted as
separate
`*_loop` / `*_loop.body` definitions per the Aeneas loop encoding (see
[§5e](#e-loop-and-divergence-modeling)).

On top of the generated model, the `Spec/Selene/` proof tree
(`Curve.lean`/`Ops.lean`/`GroupLaw.lean`) proves the Selene group law — the
headline `ΘAddEquiv : SClass ≃+ W.toAffine.Point` is **sorry-free** — and
the `Spec/Helios/` proof tree
(`Prime25519.lean`/`Curve.lean`/`Ops.lean`/`GroupLaw.lean`) proves the
Helios group law over the **idealized** dalek coordinate boundary:
`Helios.ΘAddEquiv : HClass ≃+ W.toAffine.Point`, also **sorry-free** — see
[§7](#7-formalization-status-2026-07-10) for the full status and the Helios
boundary-fidelity assumption.

### What was NOT translated, and why

- `verified::pow` (excluded via `--exclude`): iterates over
  `FieldBits`/`bitvec` bit views using iterator adapters
  (`.to_le_bits().iter_mut().rev().enumerate()`) whose signatures involve
  nested borrows, which Aeneas cannot currently express; it additionally
  calls `crate::u8_from_bool`, which is built on `core::hint::black_box`
  (an optimisation barrier with no functional meaning that the toolchain
  does not model). (`verified::sqrt` had the same iterator-adapter problem
  — `.to_le_bits().iter().take(253).rev().skip(128)` — and was excluded
  from the FIRST run; it is now translated after the patch rewrote the
  chain into an equivalent index loop, §4 hunk 5.)
- Within `point.rs`, the `Sum` impls (iterator adapters), `Group::random`
  (`RngCore` + retry loop), and point `Zeroize::zeroize` remain **opaque**
  ([§3](#3-toolchain-and-provenance)) for both `curve!` instantiations;
  they surface only as existence-only axioms
  ([§5c](#c-trusted-base-external-models-and-residual-axioms)) needed to
  state the `Group`/`GroupEncoding` trait bounds. The scalar ladders were in
  this list through the fourth run but are concrete since the fifth run
  after §4 hunk 8 removed the bitvec/`black_box` and loop-loan blockers.
  (The **Helios**
  instantiation of the `curve!` macro, entirely outside the translation
  roots through the second run, is **translated since the third run**;
  `ciphersuite.rs` (hash-to-curve) remains entirely outside.) The third
  run also declared `HelioseleneField`'s `ff::Field::sqrt_ratio` opaque —
  a NEW trust-relevant opacity: unlike the other opaque items it surfaces
  as a fresh existence-only axiom
  (`field.HelioseleneField.Insts.FfField.sqrt_ratio`, FunsExternal.lean),
  because the now-materialised `ff.Field HelioseleneField` record must
  state the method; see [§3](#3-toolchain-and-provenance) for why it had
  to be opaque and §5c for its status (outside every proof cone).
- The `Sum`/`Product` impls for `HelioseleneField` were declared **opaque**
  (see [§3](#3-toolchain-and-provenance)). Through the second run they did
  not appear in the output at all; since the third run they surface as
  four existence-only axioms (§5c), because the now-materialised
  `ff.Field HelioseleneField` record must state its `Sum`/`Product` parent
  clauses. No translated function depends on their bodies (verified by grep
  over `Funs.lean`; see [§5g](#g-struct-flattening-and-trait-encoding)).
  (`ff::Field::sqrt` for `HelioseleneField`, opaque in the first run, is now
  translated; `ff::Field::sqrt_ratio` is opaque since the third run — see
  above.)
- Foreign crates (`crypto-bigint`, `subtle`, and — new in the second run's
  call graph — `dalek-ff-group`, Selene's scalar type **and, since the
  third run, Helios' coordinate type**) are **not translated** — Charon's
  default treatment of foreign bodies leaves them as external
  declarations. `crypto-bigint`/`subtle` are instantiated here with
  concrete definitional models (`TypesExternal.lean` /
  `FunsExternal.lean`). The `dalek_ff_group::FieldElement` surface was
  covered by existence-only axioms through the second run (it was needed
  only as trait-instance evidence); since the third run it is the
  **load-bearing idealized boundary** of the Helios stage: 28 of its items
  are concrete `ZMod (2^255 − 19)` definitional models (including, since the
  fifth run, canonical little-endian `to_repr` and zeroization), and 23
  remain existence-only axioms. The fidelity of the concrete models to the
  Rust crates is the trusted base of the model; see
  [§5c](#c-trusted-base-external-models-and-residual-axioms) and, for the
  per-item Helios obligations, `human_audit_assumptions_helios.txt`.

## 2. Directory contents

| File | Role | Edit? |
|---|---|---|
| `HUMAN_AUDIT_TASK.md` | **Start here for human assurance.** Consolidated audit task covering all field/Selene/Helios/scalar proof boundaries, exact inventories of 6 type models, 92 concrete function models, 39 explicit axioms and 25 quarantined validation axioms, all Rust changes, expected theorem axiom cones, scope exclusions, and completion criteria. | **Yes** — audit process |
| `HelioseleneCore.lean` | Library entry point: `import HelioseleneCore.Funs` (the `aeneas -gen-lib-entry` output) plus `import HelioseleneCore.Spec.Field` (the proof tree). | Import list only |
| `HelioseleneCore/Types.lean` | Generated type definitions: `Add`/`Sub`/`Mul`/`Neg`, `Zeroize`/`DefaultIsZeroes`, and the other trait declaration records; `crypto_bigint.limb.Limb := Std.U64`; `field.HelioseleneField := crypto_bigint.uint.Uint 4#usize`. | No — regenerate |
| `HelioseleneCore/Funs.lean` | Generated function definitions (~5,556 lines): the translated call graph listed in §1, including both concrete scalar ladders and their extracted loops since the fifth run. | No — regenerate |
| `HelioseleneCore/TypesExternal.lean` | Concrete computable **definitions** (not axioms) modeling the 6 external types: the original 3 — `Uint LIMBS := Aeneas.Std.Array U64 LIMBS` (little-endian limb vector), `subtle.Choice := Bool`, `subtle.CtOption T := T × Bool` — plus, appended for the second run, `crypto_bigint.ct_choice.CtChoice := Bool`, `dalek_ff_group.field.FieldElement := ZMod (2^255 − 19)` (since the third run the Helios coordinate type — a **load-bearing** identification, see §5c) and `rand_core.error.Error`. Instantiated from the generated template; each `def` carries a doc comment citing the crate source it models. | **Yes** — hand-written models (§5c) |
| `HelioseleneCore/FunsExternal.lean` | Concrete computable **definitions** modeling the external functions/constants of `crypto-bigint`/`subtle`/`ff`/`zeroize`/`dalek-ff-group`: **92 top-level `def` declarations**, including model helpers and the fifth-run `usize::ct_eq`, blanket/array zeroization, dalek scalar zeroization, and canonical dalek `to_repr`; each Rust-facing model is documented against the crate source. It also contains **39 existence-only axioms** used as trait evidence or by still-unproved paths (23 `dalek_ff_group::FieldElement`, 4 out-of-scope `SelenePoint`, 4 `HeliosPoint`, 4 `HelioseleneField` `Sum`/`Product`, 1 `HelioseleneField` `sqrt_ratio`, 2 `Uint`, 1 `crypto-bigint` `Debug::fmt`); see §5c. | **Yes** — hand-written models (§5c) |
| `HelioseleneCore/Validation.lean` | Generated differential validation of the (computable) model against 964 independent test vectors, checked by `native_decide` (§7). **Not imported by the library entry point** — built only via the lakefile's submodule glob, so its `native_decide` axioms stay out of every proof's dependency cone. | No — regenerate (`gen_validation.py`) |
| `HelioseleneCore/ValidationSelene.lean` | Same pattern for the Selene scope: 100 independent vectors (sqrt/add/double/neg/ct_eq/from_xy) through the translated `point.selene.*` code, plus ad-hoc structural checks and per-class corrupted-vector **negative controls**, checked by `native_decide`. Imported by nothing. | No — regenerate (`gen_validation_selene.py`) |
| `HelioseleneCore/ValidationHelios.lean` | Same pattern for the Helios scope: 75 independent vectors (add/double/neg/ct_eq/from_xy) through the translated `point.helios.*` code, plus structural checks and per-class corrupted-vector **negative controls**, checked by `native_decide`. Imported by nothing. **Weaker signal than `ValidationSelene.lean`**: the Helios coordinate field is idealized (§5c), so the vectors validate the translated group-law formulas and model plumbing, not any field-arithmetic implementation (scope caveat in the file header). | No — regenerate (`tools/gen_validation_helios.py`) |
| `HelioseleneCore/Spec/Externals.lean` | Spec lemmas for the external models, plus kernel-only re-derivation of the generated hex-string constants (`MODULUS_ok` etc.). | **Yes** — proofs |
| `HelioseleneCore/Spec/Phi.lean` | The abstraction layer: reduced carrier `HField`, bijection `φ`/`equivZMod` with `ZMod p`, `Fintype HField`, `card_hfield`. | **Yes** — proofs |
| `HelioseleneCore/Spec/Prime.lean` | Kernel-only Pratt-certificate proof of `p_prime` (§7). | No — regenerate (`gen_prime.py`) |
| `HelioseleneCore/Spec/Linear.lean` | Proved contracts for the linear ops: `red1_ok`, `add_ok`, `double_ok`, `sub_ok`, `neg_ok`, `is_zero_ok`, `is_odd_ok`. | **Yes** — proofs |
| `HelioseleneCore/Spec/Repr.lean` | Proved contracts for the byte encodings: `from_repr_ok`, `to_repr_ok`. | **Yes** — proofs |
| `HelioseleneCore/Spec/Reduction.lean` | Proved contracts for reduction and multiplication: `red256_ok`, `red512_ok`, `mul_ok`, `square_ok`. | **Yes** — proofs |
| `HelioseleneCore/Spec/Invert.lean` | Sorry-free contract for constant-time inversion (`invert_ok`), including the machine-level `step_congruence` proof for the repaired four-limb 0/p/2p carry chain (§7). | **Yes** — proofs |
| `HelioseleneCore/Spec/Field.lean` | `Field HField` instance and the ring isomorphism `φRing : HField ≃+* ZMod p`; axiom audit (§7). | **Yes** — proofs |
| `HelioseleneCore/Spec/ScalarMul.lean` | Exact mathlib-facing `SMul` adapters for both generated point-scalar ladders at Aeneas's `Result Point` boundary, with definitional theorems tying `scalar • .ok point` to the generated bodies. The generated `Mul` records are already installed into `group::ScalarMul` by `Funs.lean`. This is a type-level bridge; `SMul` itself has no laws. | **Yes** — definitions/proofs |
| `HelioseleneCore/Spec/ScalarMulLaws.lean` | Sorry-free correctness proof for both full generated ladders: canonical scalar bytes, bit clearing, 16-entry precomputation, constant-time scan, all 256 loop iterations and cleanup. Descends the exact generated outputs to `SMul` on `SClass`/`HClass`, proves equality with natural repeated addition and unconditional `DistribSMul`; constructs the full `Module` laws from explicitly named Selene/Helios exponent certificates, neither of which is assumed or instantiated here. | **Yes** — definitions/proofs |
| `HelioseleneCore/Spec/Selene/Curve.lean` | Kernel-checkable Selene curve constants and number theory: `B_ok`/`G_Y_ok`/`G_X_ok`/`G_ok` constant agreement, `B_nonresidue`, `cubic_no_root`/`no_two_torsion`, `delta_ne_zero`, generator-on-curve (§7). | **Yes** — proofs |
| `HelioseleneCore/Spec/Selene/Ops.lean` | ZMod-level coordinate contracts for every translated Selene operation (`add_coords_ok`, `double_coords_ok`, …, `sqrt_ok`, `sqrt_complete`, `recover_y_ok`), all proved (§7). | **Yes** — proofs |
| `HelioseleneCore/Spec/Selene/GroupLaw.lean` | The Selene group law: `SClass` quotient with the descended translated operations, `AddCommGroup SClass`, deciders, and the sorry-free headline `ΘAddEquiv : SClass ≃+ W.toAffine.Point`; axiom audit in its §9 (§7). | **Yes** — proofs |
| `HelioseleneCore/Spec/Helios/Prime25519.lean` | Kernel-only Pratt-certificate proof of `q_prime : Nat.Prime (2^255 − 19)`, the Helios coordinate prime (7 Lucas nodes; §7). | No — regenerate (`tools/gen_prime25519.py`) |
| `HelioseleneCore/Spec/Helios/Curve.lean` | Kernel-checkable Helios curve constants and number theory over `Fq = ZMod (2^255 − 19)`: `B_ok`/`G_Y_ok`/`G_X_ok`/`G_ok` constant agreement with the `point.rs` hex literals, `B_nonresidue`, `cubic_no_root`/no-2-torsion, `delta_ne_zero`, generator-on-curve (§7). | **Yes** — proofs |
| `HelioseleneCore/Spec/Helios/Ops.lean` | Coordinate-level contracts for every translated Helios point operation — all precondition-free: the coordinate type IS `Fq` (no limb layer, no `Reduced` invariant) and the dalek coordinate ops are concrete `ZMod` models, so the field-op specs are `rfl` lemmas (§7). | **Yes** — proofs |
| `HelioseleneCore/Spec/Helios/GroupLaw.lean` | The Helios group law over the idealized dalek boundary: `HClass` quotient with the descended translated operations, `AddCommGroup HClass`, deciders, non-degeneracy (`gen_ne_zero`, `Nontrivial HClass`), and the sorry-free headline `Helios.ΘAddEquiv : HClass ≃+ W.toAffine.Point`; axiom audit in its §9 (§7). | **Yes** — proofs |
| `helioselene-aeneas.patch` | The diff against `crypto/helioselene` that the translation was produced from (§4). The repository tree itself is untouched; the patch was applied to a scratch **copy**. | — |
| `MAPPING.md` | Machine-generated per-declaration Lean-to-Rust index with pinned links. | No — regenerate |
| `lakefile.lean` | Lake package; `require aeneas from` the Aeneas Lean support library **by absolute path** — adjust to your extraction of the Aeneas release. | Path only |
| `lean-toolchain` | `leanprover/lean4:v4.30.0-rc2`. | No |
| `lake-manifest.json` | Pinned Lake dependencies (the `aeneas` library and its transitive deps: mathlib, batteries, aesop, …). | No |
| `.lake/` | Build artifacts. | — |

## 3. Toolchain and provenance

| Component | Version / identity | How verified |
|---|---|---|
| monero-oxide source | based on commit `6313959f906fe754909754ac642134237dae42a9` (branch `fcmp++`), plus the 2026-07-10 production inversion carry-chain correction documented in §4 | `git log` / source diff |
| Aeneas | release `nightly-2026.07.06-45061fa` (prebuilt binaries: `aeneas`, `charon`, `charon-driver`, `backends/lean`) | `aeneas -version` |
| Charon | `0.1.218`, bundled with the Aeneas release | `charon version` |
| rustc | `nightly-2026-06-01` (pinned by the release's `rust-toolchain`) | toolchain file |
| Lean | `v4.30.0-rc2` | `lean-toolchain` |
| `crypto-bigint` | 0.5.5 | `Cargo.lock` of the translated copy |
| `subtle` | 2.6.1 | `Cargo.lock` of the translated copy |

Charon and Aeneas were run three scope-expansion times, then a fourth
source-refresh run and a fifth scalar-ladder widening run on 2026-07-10,
all on a patched copy of `crypto/helioselene` (§4).

**First run (2026-07-06, superseded)** — field scope only; kept here for
provenance of the original artifact:

```sh
charon cargo --preset aeneas --hide-marker-traits \
  --start-from 'helioselene::field::verified' \
  --exclude 'helioselene::field::verified::sqrt' \
  --exclude 'helioselene::field::verified::pow' \
  --opaque 'helioselene::field::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::field::{impl core::iter::traits::accum::Product<_> for _}' \
  --opaque 'helioselene::field::{impl ff::Field for _}::sqrt' \
  --dest-file helioselene_core.llbc -- --no-default-features --release
```

**Second run (2026-07-07, Selene widening, superseded)** — kept for
provenance. It added the `point::selene` root, dropped the `sqrt` exclusion
and the `ff::Field::sqrt` opacity (the §4 hunk-5/6 rewrites made `sqrt`
translatable), and marked the out-of-scope `SelenePoint` items opaque:

```sh
charon cargo --preset aeneas --hide-marker-traits \
  --start-from 'helioselene::field::verified' \
  --start-from 'helioselene::point::selene' \
  --exclude 'helioselene::field::verified::pow' \
  --opaque 'helioselene::field::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::field::{impl core::iter::traits::accum::Product<_> for _}' \
  --opaque 'helioselene::point::selene::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::point::selene::{impl core::ops::arith::Mul<_> for _}' \
  --opaque 'helioselene::point::selene::{impl core::ops::arith::MulAssign<_> for _}' \
  --opaque 'helioselene::point::selene::{impl group::Group for _}::random' \
  --opaque 'helioselene::point::selene::{impl zeroize::Zeroize for _}' \
  --dest-file helioselene_selene.llbc -- --no-default-features --release
```

**Third run (2026-07-08, Helios group-law core)** — the run that established
the checked-in translation scope (subsequently refreshed by the fourth run).
It
adds the `point::helios` root, duplicates the five `point::selene` opacity
patterns for `point::helios` (same blockers, same items), and adds one NEW
opacity on `HelioseleneField`'s `ff::Field::sqrt_ratio` (rationale in the
flag list below; unlike the other opacities it surfaces as a fresh
existence-only axiom — §5c):

```sh
charon cargo --preset aeneas --hide-marker-traits \
  --start-from 'helioselene::field::verified' \
  --start-from 'helioselene::point::selene' \
  --start-from 'helioselene::point::helios' \
  --exclude 'helioselene::field::verified::pow' \
  --opaque 'helioselene::field::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::field::{impl core::iter::traits::accum::Product<_> for _}' \
  --opaque 'helioselene::field::{impl ff::Field for _}::sqrt_ratio' \
  --opaque 'helioselene::point::selene::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::point::selene::{impl core::ops::arith::Mul<_> for _}' \
  --opaque 'helioselene::point::selene::{impl core::ops::arith::MulAssign<_> for _}' \
  --opaque 'helioselene::point::selene::{impl group::Group for _}::random' \
  --opaque 'helioselene::point::selene::{impl zeroize::Zeroize for _}' \
  --opaque 'helioselene::point::helios::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::point::helios::{impl core::ops::arith::Mul<_> for _}' \
  --opaque 'helioselene::point::helios::{impl core::ops::arith::MulAssign<_> for _}' \
  --opaque 'helioselene::point::helios::{impl group::Group for _}::random' \
  --opaque 'helioselene::point::helios::{impl zeroize::Zeroize for _}' \
  --dest-file helioselene_helios.llbc -- --no-default-features --release
```

```sh
aeneas -backend lean -split-files -gen-lib-entry -dest . helioselene_helios.llbc
```

**Fourth run (2026-07-10, inversion repair refresh)** — repeated the third
run with the identical roots, exclusions and opacity set after the production
carry-chain correction in §4. The regenerated `step_loop4` takes
`add_two_modulus` explicitly and the generated `step` has no trailing top-bit
OR. The external interface was unchanged, so the concrete external models
remain valid.

**Fifth run (2026-07-10, scalar multiplication)** — kept the same three
roots and the `pow` exclusion, but removed the four point `Mul`/`MulAssign`
opacity patterns after §4 hunk 8 made both macro instantiations translatable:

```sh
charon cargo --preset aeneas --hide-marker-traits \
  --start-from 'helioselene::field::verified' \
  --start-from 'helioselene::point::selene' \
  --start-from 'helioselene::point::helios' \
  --exclude 'helioselene::field::verified::pow' \
  --opaque 'helioselene::field::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::field::{impl core::iter::traits::accum::Product<_> for _}' \
  --opaque 'helioselene::field::{impl ff::Field for _}::sqrt_ratio' \
  --opaque 'helioselene::point::selene::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::point::selene::{impl group::Group for _}::random' \
  --opaque 'helioselene::point::selene::{impl zeroize::Zeroize for _}' \
  --opaque 'helioselene::point::helios::{impl core::iter::traits::accum::Sum<_> for _}' \
  --opaque 'helioselene::point::helios::{impl group::Group for _}::random' \
  --opaque 'helioselene::point::helios::{impl zeroize::Zeroize for _}' \
  --dest-file helioselene_core.llbc -- --no-default-features --release
```

```sh
aeneas -backend lean -split-files -gen-lib-entry -dest . helioselene_core.llbc
```

The fifth-run flag set is **verified against reality**: Charon serializes its full
option record into the `.llbc` output, and the `options` block of
`helioselene_core.llbc` records exactly
`start_from = [helioselene::field::verified, helioselene::point::selene,
helioselene::point::helios]` (three roots),
`exclude = [helioselene::field::verified::pow]`, the **nine** `--opaque`
patterns in the fifth-run command (in that order), `hide_marker_traits = true` and
`preset = Aeneas` (charon 0.1.218, target `x86_64-unknown-linux-gnu`). The
second run's flag set (two roots, seven opaque patterns,
`dest_file = helioselene_selene.llbc`) was verified against its own `.llbc`
options block the same way and is summarized in
`human_audit_assumptions.txt` §VIII (frozen at the 2026-07-07 stage); the
third run's is summarized in `human_audit_assumptions_helios.txt`.

Why each flag:

- `--preset aeneas` — the Charon option bundle required for Aeneas
  consumption (per Charon's source, the preset enables the option bundle
  Aeneas needs, including the mutable-reference monomorphization
  `--monomorphize-mut`; the CLI help does not document the preset's
  contents).
- `--hide-marker-traits` — hides `Sized`/`Sync`/`Send`-style marker-trait
  clauses wherever they show up (Charon's own description). Without it the
  generated signatures carry unusable marker-trait parameters. Note `Copy`
  and `Clone` are *not* hidden: they appear as explicit instance records in
  `Funs.lean`.
- `--start-from 'helioselene::field::verified'` /
  `--start-from 'helioselene::point::selene'` /
  `--start-from 'helioselene::point::helios'` (the third root is NEW with
  the third run) — restrict translation roots to the verified field module
  and the two group-law cores instead of the whole crate; only items
  reachable from them are extracted.
- `--exclude …::pow` — drop the one function Aeneas cannot handle even
  after patching (§1); nothing in the translated scope calls it. (The first
  run also excluded `…::sqrt`; the second run translates it, after the §4
  hunk-5/6 rewrites removed the bitvec iterator adapters.)
- `--opaque` on the `HelioseleneField` `Sum`/`Product` impls —
  `ff::Field` (needed for `Field::ZERO`/`is_zero`, which `Neg` and `invert`
  use) has `Sum`/`Product` supertrait bounds; translating their bodies
  drags in `Iterator::copied`/`sum`/`product` adapters whose signatures
  crash Aeneas' signature translation. Opacity keeps the trait resolvable
  while dropping the bodies. Since no translated function calls them, this
  is scope reduction, not an extra behavioural assumption
  ([§5g](#g-struct-flattening-and-trait-encoding)) — though since the
  third run the impls DO surface as four existence-only axioms (§5c),
  because the materialised `ff.Field HelioseleneField` record must state
  its `Sum`/`Product` parent clauses. (The first run's `--opaque` on
  `ff::Field::sqrt` is gone: `sqrt` is now translated.)
- `--opaque 'helioselene::field::{impl ff::Field for _}::sqrt_ratio'` —
  NEW with the third run, and the one opacity that adds a fresh trust
  item. `sqrt_ratio`'s body is the `ff::PrimeField`-generic
  `ff::helpers::sqrt_ratio_generic`, so translating it would make the
  `ff::Field` impl, this method and the `ff::PrimeField` impl for
  `HelioseleneField` a mixed-recursive declaration group, which Aeneas
  does not support — and the third run MUST materialise the
  `ff.Field HelioseleneField` record (it is `Group` *scalar* evidence for
  `HeliosPoint`). Unlike the field-layer `Sum`/`Product` case the method
  surfaces in the output: as the existence-only axiom
  `field.HelioseleneField.Insts.FfField.sqrt_ratio`
  ([§5c](#c-trusted-base-external-models-and-residual-axioms)), verified
  outside every proof cone — neither curve's translated group law calls
  `sqrt_ratio` (Selene's decompression uses the translated
  `verified::sqrt`; Helios' the axiomatised dalek `sqrt`).
- `--opaque` on the `SelenePoint` — and, third run, `HeliosPoint` —
  `Sum` impls, `Group::random`, and `Zeroize::zeroize` — iterator-adapter
  and `RngCore` blockers remain for these items. They
  are required by the `Group`/`GroupEncoding` trait bounds, so opacity
  keeps the traits resolvable. Unlike the field-layer case they DO surface
  in the output — as the existence-only axioms of
  [§5c](#c-trusted-base-external-models-and-residual-axioms) — because the
  trait-instance records must still be stated. The fifth run removed the
  four `Mul`/`MulAssign` opacity patterns: §4 hunk 8 replaces their mutable
  bitvec iterator and borrow-carrying fixed loops with directly equivalent,
  inspectable operations that stock Aeneas accepts. The resulting owned and
  shared methods are concrete in `Funs.lean`; their former eight axioms are
  absent from `FunsExternal.lean`.
- `-- --no-default-features --release` — cargo arguments; part of the baked
  build configuration ([§5b](#b-build-configuration-baked-into-the-model)).
- `-split-files -gen-lib-entry` — emit `Types`/`Funs`/`*External_Template`
  as separate files plus the library entry point.

## 4. Changes made to the Rust code

The translation input was a **copy** of `crypto/helioselene` with
`helioselene-aeneas.patch` applied. Unlike the translation-only rewrites,
the inversion correction below is also present in the production repository
source and is therefore not duplicated in the translation patch. The patch
additionally touches five files for two build-only `Cargo.toml` changes and
seven groups of semantics-preserving translation rewrites (hunks 2–8 below;
hunks 5–7 were added for the second run's `sqrt`/`point.selene` scope and
hunk 8 for the fifth run's scalar ladders).
Each change is argued below.
**Test evidence**: on the patched copy,
`cargo test --release` passes 11/11 tests (re-run and confirmed on
2026-07-10 after the scalar rewrite), including `field::test_helioselene_field` (the
`ff-group-tests` prime-field suite, incl. the bits tests),
`field::verified::red::tests_assuming_64_bits::test_reduction_of_each_bit`
(reduction of every one of the 512 bits, checked against `crypto-bigint`'s
`checked_rem`), `field::tests_assuming_64_bits::test_wide_reduction`
(1,000 random 512-bit reductions plus `U512::MAX`),
`field::verified::invert::invert_3_66`, and the point/group tests.

### Production correction — exact high-half addition in `invert::step`

The original fused coefficient update selected the low 128 bits of `0`, `p`
or `2p`, carried through the upper limbs using only the `p` contribution, and
then supplied the one remaining bit of `2p` with:

```rust
u.as_limbs_mut()[3] =
  u.as_limbs()[3] | (add_two_modulus << (Limb::BITS - 1));
```

That OR equals addition of `2^255` only when bit 255 of the pre-OR accumulator
is clear. If it is already set, OR leaves the limb unchanged while the intended
wrapping addition must clear the bit and carry out of the 256-bit word. The
sharp local safety condition was `|u - v_masked| ≤ 2p - 2^255`; it was not an
inductive consequence of the binary-GCD state invariant, which is why
`Invert.step_congruence` could not be proved for the original source.

The repaired high-half loop uses the same masked addend selection as the low
half:

```rust
let modulus_instances = (MODULUS.as_limbs()[l] & add_one_modulus) ^
  (MODULUS_XOR_TWO_MODULUS.as_limbs()[l] & add_two_modulus);

(u.as_limbs_mut()[l], carry) = add_with_bounded_overflow(
  u_sub_v.as_limbs()[l] ^ should_negate,
  modulus_instances,
  carry,
);
```

The final OR is deleted. `MODULUS_XOR_TWO_MODULUS = p XOR 2p`, and
`add_two_modulus` implies `add_one_modulus`, so each limb now selects exactly
`0`, `p`, or `2p`. The existing carry flows through all four limbs and its final
overflow is discarded exactly as a wrapping `U256` addition requires. This is
branch-free, valid for every machine state, and removes `UVWindow` entirely.
The regenerated Lean `step_loop4_value_spec` proves the high-half full-adder
identity for all mask combinations; `step_congruence`, all 510 loop steps and
`invert_ok` are consequently sorry-free.

### Hunk 1 — `Cargo.toml`: standalone workspace (build-only)

```diff
-[lints]
-workspace = true
+[workspace]
```

```diff
-ec-divisors = { path = "../divisors", default-features = false, optional = true }
+ec-divisors = { path = "/home/user/monero-oxide/crypto/divisors", default-features = false, optional = true }
```

The copy lives outside the monero-oxide workspace, so it cannot inherit
`[lints]` from the workspace and must be its own workspace root, and the
relative path dependency must become absolute. The recorded absolute path is
**machine-specific** — adjust it to your checkout when reproducing. Both
changes are build-only: `ec-divisors` is an *optional* dependency, not
enabled under `--no-default-features`, and nothing in `field::verified`
uses it.

### Hunks 2 and 3 — lift `bool | bool` to `Word` (`invert.rs`, `mod.rs`)

Aeneas does not support `|` on `bool`. Both carry/borrow helpers were
rewritten identically:

```rust
// before                                     // after
Limb(Word::from(borrow1 | borrow2))           Limb(Word::from(borrow1) | Word::from(borrow2))
Limb(Word::from(carry1 | carry2))             Limb(Word::from(carry1)  | Word::from(carry2))
```

(in `sub_with_bounded_overflow` in `src/field/verified/invert.rs` and
`add_with_bounded_overflow` in `src/field/verified/mod.rs` respectively).

**Semantics preservation.** For `a, b : bool`, `Word::from` maps `false ↦ 0`
and `true ↦ 1`. Rust's `|` on `bool` is non-short-circuiting logical or, so
`Word::from(a | b) = 1` iff `a ∨ b`. On the right, `Word::from(a)` and
`Word::from(b)` each lie in `{0, 1}`, and bitwise-or on `{0, 1}` equals
logical or: `Word::from(a) | Word::from(b) = 1` iff `a ∨ b`. The two
expressions are equal for all four input combinations — unconditionally, not
merely on reachable inputs. There is no observable side effect or timing
branch in either form. In the Lean model this appears in
`field.verified.invert.sub_with_bounded_overflow` as two
`core.convert.num.FromU64Bool.from` calls followed by `|||` on `U64`.

### Hunk 4 — `from_repr::reduced`: replace the limb iterator with indexing (`mod.rs`)

```rust
// before
let mut b_limbs = MODULUS_255_DISTANCE.as_limbs().iter();
let mut last = Limb::ZERO;
let mut carry = Limb::ZERO;
for a in a.as_limbs() {
  let b = b_limbs.next().unwrap_or(&Limb::ZERO);
  (last, carry) = add_with_bounded_overflow(*a, *b, carry);
}

// after
let mut last = Limb::ZERO;
let mut carry = Limb::ZERO;
for i in 0 .. U256::LIMBS {
  let b = if i < U128::LIMBS { MODULUS_255_DISTANCE.as_limbs()[i] } else { Limb::ZERO };
  (last, carry) = add_with_bounded_overflow(a.as_limbs()[i], b, carry);
}
```

Aeneas cannot translate the slice-iterator `iter()` / `next()` /
`unwrap_or(&…)` pattern (nested-borrow iterator signatures again).

**Semantics preservation.** The original iterates over `a.as_limbs()`, an
array of `U256::LIMBS` limbs in little-endian limb order, so the loop body
runs exactly `U256::LIMBS` times with `a`'s limbs `0, 1, …, U256::LIMBS-1`.
`b_limbs` iterates over `MODULUS_255_DISTANCE.as_limbs()`, an array of
`U128::LIMBS` limbs; `next()` yields `Some(&limb[i])` for
`i < U128::LIMBS` and `None` — hence `&Limb::ZERO` via `unwrap_or` —
afterwards. The rewrite produces the identical sequence of `(a_limb, b_limb)`
pairs: index `i` runs over `0 .. U256::LIMBS`, `b = limbs[i]` for
`i < U128::LIMBS` and `Limb::ZERO` otherwise. The fold over
`(last, carry)` is unchanged, as is the post-loop expression. All indexing is
trivially in bounds (`i < U256::LIMBS` for `a`, `i < U128::LIMBS` guarded
for `b`), so no new panic paths are introduced.

**Constant-time caveat.** The rewritten code branches on
`i < U128::LIMBS`. Both operands are public: `i` is the loop counter and
`U128::LIMBS` is a compile-time constant (2 on 64-bit targets). No
secret-dependent branch is introduced; the original's control flow was
likewise determined only by iterator position, never by limb values. (Note
that constant-time behaviour is in any case *not* preserved by this model —
see [§5f](#f-erased-properties) — this caveat only records that the source
rewrite itself does not degrade the constant-time discipline of the crate.)

### Hunk 5 — `sqrt.rs`: replace the bitvec iterator ladder walk with an explicit bit-index loop (plus a limb-array local copy)

```rust
// before
for bit in MODULUS_PLUS_ONE_DIV_FOUR.to_le_bits().iter().take(253).rev().skip(128) {
  bits <<= 1;
  let bit = u8::from(*bit);

// after
let modulus_plus_one_div_four_limbs = *MODULUS_PLUS_ONE_DIV_FOUR.0.as_limbs();
for k in 0 .. 125 {
  let i = 124 - k;
  bits <<= 1u32;
  let bit = ((modulus_plus_one_div_four_limbs[i / 64].0 >> ((i % 64) as u32)) & 1) as u8;
```

Aeneas cannot translate the `FieldBits`/`bitvec` iterator adapters
(nested-borrow signatures, as for `pow` — §1).

**Semantics preservation.** The original chain iterates the little-endian
bit view of the (public, compile-time constant) exponent `(p+1)/4`:
`.take(253)` yields bit indices `0 … 252`, `.rev()` reverses them to
`252 … 0`, `.skip(128)` drops the first 128 of those (`252 … 129`), leaving
**exactly the index sequence `124, 123, …, 0`** — the same sequence the
rewrite produces as `i = 124 - k` for `k = 0 .. 125`. Each bit is read as
`limbs[i / 64] >> (i % 64) & 1`, which is by definition bit `i` of the
little-endian limb array, i.e. the same value `to_le_bits()[i]` yields on
the modeled 64-bit target. The loop body's fold over `(bits, res)` is
unchanged. All indexing is trivially in bounds (`i ≤ 124` so
`i / 64 ≤ 1 < 4`), so no new panic paths are introduced. There is **no
borrow of a `const`**: the exponent's limb array is copied to a plain local
**once, before the loop** (`[Limb; 4]` is `Copy`; the copy is
value-identical and side-effect-free). The copy exists because borrowing a
`const` (or any loop-invariant local) *inside* the loop body creates shared
borrows that Aeneas' loop fixed-point computation cannot join, while
indexing a plain local array is supported.

**Constant-time caveat.** Loop bounds, bit positions, and the window-flush
branch (`bits & (1 << 3) != 0`) depend only on the public constant
exponent, exactly as in the original iterator form; no secret-dependent
branch is introduced.

### Hunk 6 — `sqrt.rs` + `point.rs`: `u32`-typed shift amounts

```rust
bits <<= 1u32;                        // was: bits <<= 1;
if (bits & (1u8 << 3u32)) != 0 {      // was: (bits & (1 << 3))
let sign = Choice::from(bytes[31] >> 7u32);   // was: >> 7
mut_ref[31] &= !(1u8 << 7u32);        // was: !(1 << 7)
mut_ref[31] |= y_sign << 7u32;        // was: << 7
```

Rust's untyped shift-amount literals default to `i32`; the Aeneas Lean
standard library types all shift amounts as `u32`, and the backend emits
the literal's inferred type verbatim, which the library then rejects.
Retyping the literals to `u32` (and, where needed, annotating the shifted
value's width, e.g. `1u8`) makes the output well-typed.

**Semantics preservation.** The shift **amounts are the identical values**
(1, 3, 7); Rust's `<<`/`>>` semantics do not depend on the integer type of
the right-hand operand (only on its value), and all amounts are far below
the shifted type's width, so no overflow-behaviour edge is touched. The
change is purely type-level — the same machine operation on the same
values. (The `point.rs` hunks sit in the `curve!` macro body, so they apply
to the Helios instantiation identically; since the third run both
instantiations are translated from the same patched macro body.)

### Hunk 7 — `point.rs` `from_bytes`: rename the local `point` to `candidate_point`

```rust
// before                                        // after
let point = y.map(|y| $Point { … });             let candidate_point = y.map(|y| $Point { … });
…, &point, …                                     …, &candidate_point, …
```

**Semantics preservation.** A pure alpha-rename of one local binding (both
occurrences); it has no semantic content whatsoever. The rename is needed
because a local named `point` shadows the generated `point.selene.*`
namespace in the Lean output, breaking name resolution in `Funs.lean`.

### Hunk 8 — `point.rs`: expose the scalar ladder without bitvec or loop-carried loans

This is the only fifth-run source rewrite. It is confined to the translation
copy; production `src/point.rs` remains the source of truth. The patch keeps
the original 4-bit fixed-window algorithm and precomputation table, but spells
four operations in forms accepted by stock Aeneas:

1. Replace the mutable bitvec iterator with direct indexing of the scalar's
   canonical little-endian `[u8; 32]` representation:

   ```rust
   // before
   for (i, mut bit) in other.to_le_bits().iter_mut().rev().enumerate() {
     bits <<= 1;
     let mut bit = u8_from_bool(bit.deref_mut());

   // translation copy
   let mut other_bytes = other.to_repr();
   for i in 0 .. 256usize {
     let bit_index = 255usize - i;
     let byte_index = bit_index / 8usize;
     let bit_offset = (bit_index % 8usize) as u32;
     bits <<= 1u32;
     let mut bit = (other_bytes[byte_index] >> bit_offset) & 1u8;
   ```

   Both scalar types used by the `curve!` macro have `PrimeField::Repr =
   [u8; 32]`, and both `to_le_bits()` implementations are the little-endian
   bit view of that canonical representation. The original reversed iterator
   yields bit indices `255, 254, ..., 0`; `bit_index = 255 - i` yields exactly
   the same sequence. `byte_index = bit_index / 8` and
   `bit_offset = bit_index % 8` select exactly that bit.

   The original `u8_from_bool` also clears each consumed bit in the owned
   `FieldBits` temporary. The translation copy preserves that cleanup with a
   tiny value-returning helper:

   ```rust
   fn clear_scalar_bit(mut bytes: [u8; 32], byte_index: usize, bit_offset: u32)
     -> [u8; 32]
   {
     bytes[byte_index] &= !(1u8 << bit_offset);
     bytes
   }
   ```

   The helper takes and returns the array by value solely to keep mutable
   index loans out of Aeneas' loop fixed point. The loop calls it after reading
   each bit, and `other_bytes.zeroize()` clears the complete temporary after
   traversal. The original `bit.zeroize()` and `other.zeroize()` remain.
   `black_box` is an optimization barrier with no functional result, so its
   removal changes no value computed by the functional model.

2. Put construction of the mutable 16-entry table in a block that returns an
   immutable table. This does not alter any table entry; it makes the final
   indexed-construction loan end before the scalar loop. Each candidate is
   then copied from the table into a loop-local before it is borrowed.
   `$Point: Copy`, so every candidate has exactly the same coordinates.

3. Unroll the two fixed inner loops: four `res = res.double()` statements and
   the 15 `conditional_select` calls for table indices `1` through `15`.
   Bounds and order are literal copies of `0 .. 4` and the original
   `table[1..].iter().enumerate()` sequence. Every candidate is still visited
   and selected with `usize::from(bits).ct_eq(&j)`; no secret-dependent branch
   replaces the constant-time selection.

4. Spell `res += term` as `res = res + term`. The point `AddAssign`
   implementation in the same macro is exactly `*self = *self + other`, so
   this is an unconditional definitional equivalence. It avoids a mutable
   `res` loan on only one branch of the outer loop.

The failed unchanged-source experiment and the intermediate rewrites were
diagnostic, not part of the recorded patch. Charon accepted the unchanged
ladder, but Aeneas first encountered recursive `bitvec::BitStore`
associated-type constraints and then could not join nested iterator/table
loans. After the four mechanical changes above, the pinned, unmodified stock
Charon and Aeneas binaries complete with zero translation errors. The patched
Rust copy passes all 11 library tests for both curves. The resulting Lean is
the concrete `point.clear_scalar_bit`, two `mul_loop.body`/`mul_loop` pairs,
and all owned/shared `Mul`/`MulAssign` methods and trait records.

#### Audit classification of hunk 8

The scalar proof does not make this translation-only rewrite disappear as an
audit obligation. Its status is deliberately split as follows:

1. **Human source-equivalence obligation.** Production `src/point.rs` is the
   source of truth. There is no machine-checked theorem relating its iterator
   spelling to the patched scratch copy. An auditor must confirm the four
   equivalence arguments above: identical canonical bit order and cleanup,
   identical table values despite shorter loans, identical fixed-loop
   unrolling, and `AddAssign`/`Add` equivalence. The 11 passing Rust tests are
   regression evidence only.
2. **Translator obligation.** `Spec/ScalarMulLaws.lean` proves the generated
   definitions produced from the patched copy. Correct extraction from the
   patched Rust MIR through LLBC to Lean still relies on rustc, Charon, and
   Aeneas as described in §5a.
3. **External-value-model obligation.** The proof consumes concrete models for
   canonical scalar `to_repr`, `usize::ct_eq`, point
   `conditional_select`, blanket/array/scalar zeroization, and the machine
   array/shift operations. Selene additionally relies on the dalek scalar
   model's canonical value; Helios relies on the idealized dalek coordinate
   field for every point addition/doubling/selection. These assumptions are
   enumerated, with their crate-level fidelity targets, in
   `human_audit_assumptions_selene.txt` §V and
   `human_audit_assumptions_helios.txt` §V.
4. **What the kernel closes.** Relative to those boundaries, the proof unfolds
   the exact generated table construction, bit consumption, unrolled scan,
   all 256 loop iterations, point operations, cleanup calls, and return path.
   It proves all modeled array bounds, absence of modeled panic/divergence,
   and equality with natural repeated group addition. The proof-only helper
   definitions in `ScalarMulLaws.lean` unfold to verbatim generated blocks;
   they are not an alternative ladder.
5. **Non-claims.** Neither hunk 8 nor the Lean theorem proves constant-time
   execution, side-channel resistance, compiler preservation of branch-free
   code, or physical memory erasure. It also does not prove correctness for
   arbitrary off-curve raw points; the public specifications start from the
   verified on-curve carriers `SPt` and `HPt`.

## 5. Assumptions required for equivalence

This is the section that matters. A Lean theorem about
`field.verified.red.red512` is a theorem about the compiled Rust function
`red512` **only modulo all of the following**.

### a. Tool trust

Charon (a rustc driver extracting MIR into LLBC) and Aeneas (symbolic
execution of LLBC under a borrow calculus, producing pure monadic functions)
are **research tools** run here as unverified translators, from nightly
builds (`charon 0.1.218`, `aeneas nightly-2026.07.06-45061fa`, rustc
`nightly-2026-06-01`). Neither the LLBC extraction nor the
functional translation carries a machine-checked correctness proof. Any bug
in either tool silently yields a Lean model of a *different* program. The
generated files should be reviewed against the Rust source (they carry
source-span comments to make this practical), and regeneration should be
expected to produce different output as the tools evolve.

### b. Build configuration baked into the model

The model is a snapshot of **one** build configuration:

- **64-bit target.** `Types.lean` literally defines
  `crypto_bigint.limb.Limb := Std.U64`, and all limb counts are fixed
  (`Uint 4#usize` for `U256`, `2#usize` for `U128`). On 32-bit targets
  `crypto-bigint` uses `u32` limbs and `U256::LIMBS = 8`; that configuration
  is **not modeled**. (Aeneas' `Usize` is `System.Platform.numBits` wide;
  proofs will in practice also fix this to 64.)
- **`--release`.** The `#[cfg(debug_assertions)]` block in `invert.rs`
  (the per-step `a.bits() + b.bits()` decrease check) is **not in the
  model** (confirmed: no trace of it in the generated `step`). Similarly,
  release-mode MIR compiles plain integer arithmetic to *wrapping*
  operations, and the model reflects that (see §5d).
- **`--no-default-features`.** No `std`/`alloc` features; matches the
  crate's `no_std` core but is a fixed choice.
- **Edition 2021, this exact rustc nightly.** The model is derived from the
  MIR this compiler produced; a different compiler version may produce
  different (even if equivalent) MIR and hence a different-looking model.

### c. Trusted base: external models and residual axioms

The external interface of the first run (3 types + 34 functions/constants
over `crypto-bigint` 0.5.5 and `subtle` 2.6.1) was emitted by Aeneas as
axiom templates. On 2026-07-07 those axioms were **eliminated by
instantiation**: `TypesExternal.lean` and `FunsExternal.lean` contain
concrete, computable **definitions** — `Uint LIMBS := Aeneas.Std.Array U64
LIMBS` (little-endian limb vector), `subtle.Choice := Bool`,
`subtle.CtOption T := T × Bool`, and 34 definitional models of the
`crypto-bigint`/`subtle` operations, each defined as the exact `Nat`-level
computation. Unlike axioms, `def`s cannot introduce logical inconsistency
(Lean checks them for well-formedness), and they make the whole model
executable — which is what enables the differential validation of §7.

The second run (§3) widened the external interface. Its additions come in
two very different kinds:

- **19 further concrete function/constant models and 3 further type models**
  (appended sections of `FunsExternal.lean` / `TypesExternal.lean`), same
  status as the original 37: `subtle` `CtOption::map`/`and_then`/
  `conditional_select`, `conditional_negate`, `Choice` bit-ops/`ct_eq`/
  `unwrap_u8`/conversions, `crypto-bigint` `Uint`
  `ct_eq`/`const_rem`/`from_u8`/`Default`, the `ff` 0.13.1
  `is_zero`/`sqrt` trait defaults, the derived-`Eq` marker functions, and
  the type models `crypto_bigint.ct_choice.CtChoice := Bool`,
  `dalek_ff_group.field.FieldElement := ZMod (2^255 − 19)`
  (cardinality-faithful for the second run's scope, where nothing
  constructed or consumed one; since the third run the **load-bearing**
  Helios coordinate type and since the fifth run Selene's actively consumed
  scalar type — see the run-specific blocks below) and
  `rand_core.error.Error` (nonzero `U32` code). Each is documented in place
  against the crate sources; inventory and review notes in
  `human_audit_assumptions.txt` §VIII.1/VIII.4.
- **Existence-only axioms** (`FunsExternal.lean`) for externals that
  appear chiefly as trait-instance evidence — records needed to state the
  `Group`/`GroupEncoding`/`PrimeField` trait bounds. The second run left
  **54** of these (45 `dalek_ff_group::FieldElement` items, 8
  `SelenePoint` items, 1 `crypto-bigint` `Debug::fmt`); the 2026-07-08
  third run **converted 21 of the 45 dalek axioms into concrete
  definitional models** (the Helios coordinate arithmetic — see the
  third-run block below) and added 15 new axioms, so the audited inventory
  stood at 48 existence-only axioms after that run. The fifth run converts
  dalek `to_repr` to a concrete canonical encoding and removes the eight
  point-scalar axioms, so the current inventory is **39 existence-only
  axioms**: 23 `dalek_ff_group::FieldElement` items (`sqrt`, `sqrt_ratio`,
  `invert`, `random`, `from_repr`/`is_odd`, the nine `PrimeField` constants,
  `Clone`/`PartialEq`/`Default`/`Debug`, 4 `Sum`/`Product`), 4
  deliberately-untranslated `SelenePoint` items and 4 `HeliosPoint` items
  (each curve's two `Sum`s, `Group::random`, and point
  `Zeroize::zeroize`), 4 `HelioseleneField`
  `Sum`/`Product` items, 1 `HelioseleneField` `sqrt_ratio` (the NEW
  third-run opacity, §3), 2 `Uint` items (derived `PartialEq::eq`,
  `From<u64>`), and 1 `crypto-bigint` `Debug::fmt`. Every axiom's type is
  inhabited (`fun _ => fail .panic`), so each is a conservative extension;
  none makes a behavioural claim.
  **Dependency-cone caveat (verified by kernel `#print axioms` on every
  exported theorem)**: no goal-scope function or theorem — Selene's and
  Helios' `add`/`neg`/`sub`/`double`/`identity`/`generator`/`is_identity`/
  `ct_eq`/`eq`/`conditional_select`/`from_xy`/`curve_equation`/`G`/`G_X`/
  `G_Y`/`B`, Selene's `from_bytes`/`to_bytes`/`recover_y`,
  both scalar ladders, `verified::sqrt`, the field-layer additions, or
  anything in `Spec/` —
  depends on ANY of the 39 (see `human_audit_assumptions.txt` §VIII.2 with
  its 2026-07-08 update note, `Spec/Selene/GroupLaw.lean` §9 and
  `Spec/Helios/GroupLaw.lean` §9). They sit outside every proof cone; they
  exist so the generated trait-instance records typecheck. (The only
  translated functions that consume one are the out-of-scope Helios
  encoding path — Helios `recover_y`/`from_bytes`/`to_bytes` go through
  the dalek `sqrt`/`invert`/`from_repr`/`is_odd` axioms — exactly as recorded in
  `Spec/Helios/GroupLaw.lean` §9.)

The **third run (2026-07-08, Helios)** changed the *kind* of the dalek
boundary. Helios' coordinate field is `Field25519 =
dalek_ff_group::FieldElement`, so the translated Helios group law *computes
through* the dalek surface. Accordingly, 26 dalek items became concrete
definitional models over the type model
`FieldElement := ZMod (2^255 − 19)`: 23 operational models
(owned/`&`/`*Assign` `Add`/`Sub`/`Mul`, both `Neg`s, `Field::{ZERO, ONE,
double, square, is_zero}`, `ct_eq`, `conditional_select`, `From<u64>`,
`from_u256`) plus the `toZMod`/`ofZMod` identity helpers and the
derived-`Eq` marker. Of the 23, the group law actually computes with 12;
the `*Assign`/`&`-RHS variants and `From<u64>` are trait-record evidence,
modeled concretely anyway for uniformity (see the FunsExternal.lean dalek
section header). This is the **idealized-boundary assumption** of the
Helios stage: the models are the mathematically obvious `ZMod` operations,
and their fidelity target is **dalek-ff-group 0.5.0's own field
implementation on crypto-bigint 0.5.5's constant-modulus Montgomery
`Residue`** — NOT curve25519-dalek, whose code (in particular the
formally-verified fiat backend) is on no Helios code path. Per-item review
obligations and the human verification checklist live in
`human_audit_assumptions_helios.txt`. `FunsExternal.lean`'s grand totals
after the third run: **87 top-level `def` declarations and 48 existence-only axioms**.

The **fifth run (2026-07-10, scalar ladders)** adds four newly required
foreign methods as concrete models: `usize::ct_eq`, blanket
`DefaultIsZeroes::zeroize`, array zeroization, and dalek `FieldElement`
zeroization. It also converts dalek `PrimeField::to_repr` from an axiom to
the concrete 32-byte little-endian encoding of the canonical `ZMod` value.
The value-level fidelity claims used by the proof are exact: `usize::ct_eq`
returns true iff the machine integers are equal; point
`conditional_select(A, B, c)` returns `B` iff `c`; canonical `to_repr` returns
the same bytes that `PrimeFieldBits::to_le_bits()` views; blanket zeroization
returns the type's zero value; array zeroization applies that operation to all
32 entries; and dalek scalar zeroization returns field zero. Consequently the
current totals are **92 top-level `def` declarations and 39 existence-only
axioms**. Both scalar ladders compute through these concrete representation,
selection, equality, and cleanup models. Model fidelity to the cited Rust
crate bodies remains a human assumption, and the cleanup models express only
functional values, not physical-memory or compiler guarantees. `AxCheck.lean`
confirms that the ladder axiom cones contain only Lean's standard logical
axioms and the already documented generated curve/field constant axioms, not
any `FunsExternal.lean` existence axiom.

What remains trusted:

1. **Tool trust** (§5a) — unchanged.
2. **Fidelity of the concrete external models** — now 92 top-level `def`s in
   `FunsExternal.lean` plus the 6 type models of `TypesExternal.lean` (the
   original 34 + 3, the second run's 19 + 3, and the third run's
   dalek-boundary/Helios additions, §5c third-run block) — to the actual
   `crypto-bigint` 0.5.5 / `subtle` 2.6.1 / `ff` 0.13.1 /
   `dalek-ff-group` 0.5.0 semantics. A subtly wrong model
   yields proofs about a different program. Mitigations: every model
   carries a doc comment citing the crate source it implements (the table
   below is the review checklist for the original 34; the appended
   `FunsExternal.lean` sections play the same role for the newer ones, and
   `human_audit_assumptions_helios.txt` is the per-item checklist for the
   28 dalek models); the 964-vector differential validation
   (`Validation.lean`, §7), the 100-vector Selene validation
   (`ValidationSelene.lean`, §7) and the 75-vector Helios validation
   (`ValidationHelios.lean`, §7 — a strictly weaker signal for field
   arithmetic, since the Helios coordinate field is ideal by construction)
   exercise the translated functions — and
   therefore the models under them — against independently generated
   vectors; and `Spec/Externals.lean` proves a value-level spec lemma for
   each original model. One known, benign divergence: `shl_vartime`/`shr_vartime`
   are modeled as `fail panic` for shift amounts ≥ 64·LIMBS, where
   `crypto-bigint` returns `ZERO` — unreachable at all call sites (every
   call shifts by the constant 1). Note also that the models live in
   `Result`, so they decide panic behaviour (e.g. `from_le_slice` fails
   unless the slice length is `8·LIMBS`, mirroring the Rust panic), and
   that `Uint.LIMBS_1` feeds the **loop bounds** of `is_zero`, `red1`,
   `sub`, `red256`, `red512`, `from_repr::reduced`, and the inversion path
   (`invert`, `invert.step`, `invert.step.select`): a wrong value would
   change iteration counts, not just values.
3. **Nine generated `native_decide` constant axioms** (plus three `Debug`
   bodies, below). The nine hex-string constants
   in `Funs.lean` — the original four (`field.MODULUS`,
   `field.verified.MODULUS_255_DISTANCE`,
   `field.verified.red.TWO_MODULUS_255_DISTANCE`,
   `field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS`), the three
   added with the second run's scope (`point.selene.B`, `point.selene.G_Y`,
   `field.verified.sqrt.MODULUS_PLUS_ONE_DIV_FOUR`) and the two added with
   the third run (`point.helios.B`, `point.helios.G_Y`; neither curve's
   `G_X` carries one — both are built by `from_u8`) — call
   `Aeneas.Std.toStr`, whose length side-condition autoParam is
   `by decide +native`. This bakes one `<const>._native.decide.ax_1` axiom
   into each generated *definition*, and every theorem that mentions those
   constants transitively inherits them (`GroupLaw.lean` §9 records the
   exact per-theorem sets for the group-law exports). Each axiom asserts
   only the trivially-true statement that a 32/64-character string literal
   is at most `U32.max` bytes — **not** the constant's value. The values
   themselves are independently re-proved kernel-only: in
   `Spec/Externals.lean` (the `toStr_val` rewrite plus plain kernel
   `decide`: `MODULUS = p`, `MODULUS_255_DISTANCE = 2^255 − p`,
   `TWO_MODULUS_255_DISTANCE = 2·(2^255 − p)`,
   `MODULUS_XOR_TWO_MODULUS = p XOR 2p`), in `Spec/Selene/Curve.lean`
   (`B_ok`/`G_Y_ok` against the `src/point.rs` hex literals),
   `Spec/Selene/Ops.lean` (the `(p+1)/4` value on the sqrt cone) and
   `Spec/Helios/Curve.lean` (`B_ok`/`G_Y_ok` for the Helios constants).
   Additionally, the three generated `Debug::fmt` bodies
   (`field.HelioseleneField…CoreFmtDebug.fmt`,
   `point.selene.SelenePoint…CoreFmtDebug.fmt`,
   `point.helios.HeliosPoint…CoreFmtDebug.fmt`) contain `toStr` string
   literals of the same shape; they are reachable from trait-evidence
   records only and sit in no proof cone. Eliminating these axioms
   entirely would require regenerating `Funs.lean` with explicit autoParam
   proofs, or patching the Aeneas Std library's `toStr` default tactic —
   both touch generated/vendored code, so they are recorded as trust
   instead (see §7, remaining work).
4. **The 39 existence-only axioms** (above): conservative extensions,
   behaviour-free, and — verified — outside the dependency cone of every
   exported theorem. Trust here consists only of the *claim* that nothing
   proof-relevant depends on them, which is machine-checkable at any time
   via `#print axioms`.

Aside from the nine constant axioms (+ the three `Debug` bodies), the 39
existence-only axioms (in no proof cone), and — in the never-imported
`Validation.lean`/`ValidationSelene.lean`/`ValidationHelios.lean` — one
per-theorem native-decide axiom per validation theorem, the development
uses no axioms beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`) — see the axiom audits at the bottom of
`Spec/Field.lean`, `Spec/Selene/GroupLaw.lean` (§9) and
`Spec/Helios/GroupLaw.lean` (§9).

Full model list **of the original 34** (the 19 second-run models and the
third run's dalek/Helios models are documented in place in
`FunsExternal.lean`'s appended sections and inventoried in
`human_audit_assumptions.txt` §VIII.1 resp.
`human_audit_assumptions_helios.txt`; `MAPPING.md` indexes all), grouped
by crate, with the modeled semantics checked
against the vendored sources (`crypto-bigint-0.5.5`, `subtle-2.6.1`). Lean
names are shown without the `crypto_bigint.` prefix; `Limb = Word = u64`.

**`crypto_bigint::limb` (15):**

| Model (`def`) | Rust item | Modeled semantics |
|---|---|---|
| `limb.add.Limb.wrapping_add` | `Limb::wrapping_add` | `(a + b) mod 2^64` |
| `limb.Limb.Insts.CoreOpsBitBitAndLimbLimb.bitand` | `BitAnd for Limb` | bitwise and |
| `limb.Limb.Insts.CoreOpsBitBitOrLimbLimb.bitor` | `BitOr for Limb` | bitwise or |
| `limb.Limb.Insts.CoreOpsBitBitXorLimbLimb.bitxor` | `BitXor for Limb` | bitwise xor |
| `limb.Limb.Insts.CoreOpsBitNotLimb.not` | `Not for Limb` | bitwise complement |
| `limb.Limb.Insts.SubtleConstantTimeEq.ct_eq` | `ConstantTimeEq for Limb` | `Choice(1)` iff equal, else `Choice(0)` |
| `limb.mul.Limb.mac` | `Limb::mac(a,b,c,carry)` | 128-bit `a + b·c + carry`, returned as `(low, high)` |
| `limb.neg.Limb.wrapping_neg` | `Limb::wrapping_neg` | two's-complement negation mod 2^64 |
| `limb.Limb.Insts.CoreOpsBitShlUsizeLimb.shl` | `Shl<usize> for Limb` | `a << s`; panics for `s ≥ 64` in debug builds (masked in the modeled `--release` build); call sites use `s = 63` |
| `limb.Limb.Insts.CoreOpsBitShrUsizeLimb.shr` | `Shr<usize> for Limb` | `a >> s`; same caveat (call sites use `s = 63` and `s = 1`) |
| `limb.Limb.Insts.CoreCloneClone.clone` | `Clone for Limb` | identity |
| `limb.Limb.ZERO` | `Limb::ZERO` | `0` |
| `limb.Limb.ONE` | `Limb::ONE` | `1` |
| `limb.Limb.MAX` | `Limb::MAX` | `2^64 − 1` |
| `limb.Limb.BITS` | `Limb::BITS` | `64 : usize` |

**`crypto_bigint::uint` (16):**

| Model (`def`) | Rust item | Modeled semantics |
|---|---|---|
| `uint.add.Uint.wrapping_add` | `Uint::wrapping_add` | `(a + b) mod 2^(64·LIMBS)` |
| `uint.sub.Uint.wrapping_sub` | `Uint::wrapping_sub` | `(a − b) mod 2^(64·LIMBS)` |
| `uint.sub.Uint.sbb` | `Uint::sbb(a, b, borrow)` | multi-limb subtract-with-borrow; borrow-in read from its **top bit**, borrow-out is `0` or `Limb::MAX` (all-ones mask) |
| `uint.mul.Uint.mul_wide` | `Uint::mul_wide` | full product, returned `(lo, hi)` |
| `uint.mul.Uint.square_wide` | `Uint::square_wide` | full square, returned `(lo, hi)` |
| `uint.shl.Uint.shl_vartime` | `Uint::shl_vartime` | `a << n` (vartime in `n` only; called with constant `n = 1`); modeled as `fail panic` for `n ≥ 64·LIMBS` where the crate returns `ZERO` — unreachable here (§5c.2) |
| `uint.shr.Uint.shr_vartime` | `Uint::shr_vartime` | `a >> n` (idem, same `n ≥ 64·LIMBS` caveat) |
| `uint.encoding.Uint.from_be_hex` | `Uint::from_be_hex` | parse big-endian hex; panics on wrong length / non-hex (all call sites are valid literals) |
| `uint.encoding.Uint.from_le_slice` | `Uint::from_le_slice` | parse little-endian bytes; panics unless `len = 8·LIMBS` (call sites pass 32 bytes) |
| `uint.Uint4.Insts.Crypto_bigintTraitsEncodingArrayU832.to_le_bytes` | `Encoding::to_le_bytes` for `U256` | 32 little-endian bytes |
| `uint.Uint.ZERO` | `Uint::ZERO` | `0` |
| `uint.Uint.ONE` | `Uint::ONE` | `1` |
| `uint.Uint.LIMBS_1` | `Uint::<LIMBS>::LIMBS` | the const generic itself (`4` for U256, `2` for U128) — **feeds loop bounds** |
| `uint.Uint.as_limbs` | `Uint::as_limbs` | the limb array, little-endian limb order |
| `uint.Uint.as_limbs_mut` | `Uint::as_limbs_mut` | same array **plus a backward function** (Aeneas' encoding of `&mut`: the returned closure writes the updated array back into the `Uint`) |
| `uint.Uint.Insts.SubtleConditionallySelectable.conditional_select` | `ConditionallySelectable for Uint` | `a` if `choice = 0`, `b` if `choice = 1` |

**`subtle` (3):**

| Model (`def`) | Rust item | Modeled semantics |
|---|---|---|
| `subtle.Choice.Insts.CoreOpsBitNotChoice.not` | `Not for Choice` | `1 & !u8` — flips 0↔1 |
| `subtle.Choice.Insts.CoreConvertFromU8.from` | `From<u8> for Choice` | wraps a `u8` **required to be 0 or 1** (debug-asserted in `subtle`; the `is_odd` call site masks with `& 1`) |
| `subtle.CtOption.new` | `CtOption::new(value, is_some)` | pairs a value with a presence flag; value retained either way |

### d. Panic and error modeling

The Aeneas `Result` monad (from `Aeneas/Std/Primitives.lean`) is:

```lean
inductive Error where
  | assertionFailure | integerOverflow | divisionByZero
  | arrayOutOfBounds | maximumSizeExceeded | panic | undef

inductive Result (α : Type u) where
  | ok (v : α)
  | fail (e : Error)
  | div
```

`fail` models any Rust panic/abort; `div` models divergence (§5e). A proved
`f x = ok y` therefore establishes, relative to the assumptions of this
section: *on input `x`, the Rust function terminates without panicking and
returns (the model of) `y`*.

Where failure can actually arise in **this** model:

- `Array.index_usize` / `Array.update` return `fail .arrayOutOfBounds` for
  out-of-range indices (Rust index panics). All limb indexing here is by
  loop counters bounded by the (now concrete, §5c) limb counts.
- `core.slice.Slice.copy_from_slice` returns `fail .panic` on length
  mismatch (mirrors the Rust panic), used in `red512`'s limb marshalling.
- `core.iter.range.IteratorRange.next` returns `fail .panic` if the `Step`
  invariant is violated (`forward_checked` returning `none`, i.e. counter
  at `usize::MAX`) — unreachable for these bounded ranges once the limb
  counts are instantiated.
- `core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next`
  (used by `invert`'s outer `2 ..= U256::LIMBS` loop) returns `fail .panic`
  under the same `Step`-invariant condition — equally unreachable here.
- The 34 external models, per their definitions (§5c) — e.g. `from_le_slice`
  fails on a wrong-length slice and `shl_vartime`/`shr_vartime` fail for
  shifts ≥ 64·LIMBS (both unreachable at the actual call sites).

**Overflow, precisely.** The Aeneas standard library models plain machine
arithmetic (`UScalar.add` etc.) as *checked* operations that
`fail .integerOverflow` when out of bounds — but **no such checked
operation occurs in this generated model**. Because the extraction ran on
`--release` MIR, all primitive arithmetic appears as total, pure
wrapping/overflowing operations lifted into the monad
(`core.num.U64.overflowing_add/sub`, `Std.Usize.wrapping_add/sub/mul` —
all total `UScalar` bit-vector operations, e.g. even `Limb::BITS - 1`
appears as `Usize.wrapping_sub`; the 64/256-bit wrapping arithmetic itself
is behind the `crypto-bigint` models of §5c). This matches release-mode
Rust semantics (silent two's-complement wrap) rather than debug semantics
(panic). The verified module itself only ever wraps through *explicit*
`wrapping_*`/`overflowing_*` calls, so no silent-wrap-vs-panic divergence
arises within the translated code — but be aware the model would *not*
flag an unintended overflow of plain `+`/`-` the way a debug build would.

### e. Loop and divergence modeling

Rust `for` loops are extracted as a `*_loop.body` function returning
`Result (ControlFlow state result)` (`cont` = continue with new state,
`done` = break with result) plus a `*_loop` wrapper applying the library
combinator:

```lean
def loop (body : α → Result (ControlFlow α β)) (x : α) : Result β := do
  match body x with
  | ok (ControlFlow.cont x) => loop body x
  | ok (ControlFlow.done x) => ok x
  | fail e => fail e
  | div => div
partial_fixpoint
```

`loop` is defined with Lean's `partial_fixpoint` over a flat CCPO order on
`Result` whose bottom element is `div`: a non-terminating loop *equals*
`div`. No termination proof is required to *define* the model; termination
is instead established per-proof — any theorem concluding `… = ok _`
implicitly proves the loop terminates on the given input. The loops here
iterate over `Range Usize` (and, for `invert`'s outer loop,
`RangeInclusive Usize`) values whose bounds come from the
`Uint.LIMBS_1` / `Limb.BITS` models — now instantiated, so all iteration
counts are small concrete constants (4, 2, 64, 128…) and the `Spec/` proofs
discharge termination by direct unrolling: every `_ok` contract of §7
concludes `… = ok _` and hence proves termination on its stated domain.

### f. Erased properties

The model captures functional behaviour **only**. The following properties
of the Rust code are *not represented at all* and no theorem about this
model can establish them:

- **Constant-time execution / side channels.** Timing, memory-access
  patterns, and compiler-introduced branches are invisible. `subtle`'s
  `black_box`-based hardening (volatile reads preventing the optimizer
  from exploiting `Choice ∈ {0,1}`) is doubly invisible: the `subtle`
  operations are replaced by pure definitional models (`Choice := Bool`).
  The crate's careful branch-free style (masks,
  `select_word`, `Choice`) translates to ordinary pure functions with no
  distinguished status.
- **Zeroization.** The scalar ladder's explicit `zeroize` calls now have pure
  value models: bytes/scalars are replaced by zero, and the proof establishes
  that these calls terminate without changing the returned point. Physical
  memory writes, volatile semantics, compiler preservation, copies of the
  secret, and `zeroize`-on-drop do not exist in the model. Thus the theorem is
  not evidence that compiled memory was scrubbed.
- **Memory layout.** `#[repr(transparent)]` on `HelioseleneField` — and
  layout generally — is erased (see §5g).
- **Attributes and codegen hints.** `#[inline(always)]`, `#[inline(never)]`,
  `black_box`, volatile semantics: all gone.

Statements of the form "the implementation is constant-time" remain
exactly as audited/asserted on the Rust side; this model neither supports
nor threatens them.

### g. Struct flattening and trait encoding

- `HelioseleneField` is a newtype over `U256`; the translation **erases the
  newtype**: `field.HelioseleneField := crypto_bigint.uint.Uint 4#usize`
  (a `@[reducible] def`, not a distinct type). Theorems about field
  elements are theorems about raw `Uint 4` values; any "is reduced mod p"
  invariant must be carried as an explicit hypothesis/refinement in
  specifications — the type system will not enforce it.
- Trait impls become **instance records**: e.g.
  `core.ops.arith.Add` is a structure with a single `add` field, and
  `field.HelioseleneField.Insts.CoreOpsArithAddHelioseleneFieldHelioseleneField`
  is the record whose `add` projection is the translated function. Proofs
  should target the underlying `….add` functions directly.
- `--hide-marker-traits` removed `Sized`/`Sync`/`Send`-style clauses.
  `Copy`/`Clone` for `Limb` still appear as (trivial) instance records.
- The field-layer `Sum`/`Product` impls were opaque and **entirely
  absent** from the generated files through the second run; since the
  third run they (and the new `sqrt_ratio` opacity) surface as
  existence-only axioms (§5c), referenced by the now-materialised
  `ff.Field HelioseleneField` instance record — required as `Group`
  *scalar* evidence for `HeliosPoint`. Nothing in the translated call
  graph *calls* them, so this remains scope reduction plus conservative
  axioms, not a behavioural assumption. (`ff::Field::sqrt`, opaque and
  absent in the first run, is translated since the second; through the
  second run `ff::Field` machinery appeared only via the standalone
  `FfField.ZERO` / `FfField.is_zero` definitions.)

### h. Scope

Modeled: `field::verified` **minus `pow`** (including, since the second
run, `verified::sqrt`), the field-layer items pulled in by the widened call
graph (`from_u256`, `ct_eq`/`PartialEq` on field elements, the
`ff::Field`/`ff::PrimeField` items of §1), the **Selene group-law
core** of `point.rs` (`add`/`sub`/`neg`/`double`/`identity`/`generator`/
`is_identity`/`ct_eq`/`eq`/`conditional_select`/`curve_equation`/
`recover_y`/`from_xy`/`from_bytes`/`to_bytes` and the curve constants),
and — since the third run — the **Helios group-law core** (the same item
list, `point.helios.*`, with coordinates in the idealized dalek field of
§5c), plus — since the fifth run — both curves' owned/shared scalar
`Mul`/`MulAssign` ladders. In particular:

- Statements about the Selene *curve group* are in scope — and proved:
  see §7 (`ΘAddEquiv`). Since the third run the same holds for the
  **Helios** curve group, over the idealized dalek coordinate boundary:
  see §7 (`Helios.ΘAddEquiv` and the 'Helios group law' block). Both
  scalar-multiplication ladders are mechanically translated and
  `Spec/ScalarMulLaws.lean` proves each exact generated ladder equals abstract
  natural group scalar multiplication on its verified point carrier. Still
  **not** modeled: `Sum`, `Group::random`,
  and point `zeroize` (kept opaque; §5c's existence-only axioms), the
  Helios point encodings as *theorems* (`recover_y`/
  `from_bytes`/`to_bytes` are translated but any contract for them would
  go through the existence-only dalek `sqrt`/`invert`/`from_repr`/`is_odd`
  axioms),
  `ciphersuite.rs`, and hash-to-curve — statements about those remain out
  of scope.
- `Field::random` and the `PrimeFieldBits` bit decompositions are not
  modeled; `sqrt_ratio` is opaque (since the third run an existence-only
  axiom, §3); the `From<u8/u16/u32>` conversions are not modeled
  (`HelioseleneField`'s `From<u64>` is translated since the third run, as
  `ff::PrimeField` trait evidence).
  (`from_u256` and `ct_eq` on field elements, unmodeled in the first run,
  now are — `from_u256` through the `const_rem` model of §5c.)
- `dalek_ff_group::FieldElement` (Selene's scalar type and — since the
  third run — Helios' coordinate type) is modeled as `ZMod (2^255 − 19)`.
  The identification is now load-bearing in two ways: Helios uses it as its
  coordinate field, and Selene scalar multiplication uses its concrete
  canonical `to_repr` and zeroization. In total 28 dalek items are concrete
  `ZMod` models (§5c; per-item Helios obligations in
  `human_audit_assumptions_helios.txt`), while its remaining 23 operations
  are existence-only axioms outside every proved theorem's cone.
- The Veridise Dafny verification and this Lean model overlap on the
  `verified` module but neither subsumes the other:
  the Dafny proofs verified a Dafny translation of this code (as the crate
  README notes) and still solely cover `pow`; this model is a mechanical
  translation carrying the machine-checked proofs of §7.

## 6. Regenerating

1. Copy `crypto/helioselene` to a scratch directory and apply the patch:

   ```sh
   cp -r crypto/helioselene /tmp/helioselene-scratch
   cd /tmp/helioselene-scratch
   # The patch headers carry absolute paths; -p6 strips the old-file prefix
   # /home/user/monero-oxide/crypto/helioselene/ (the leading slash counts as
   # one). Adjust -p to the prefix depth of your checkout as needed.
   patch -p6 < /path/to/monero-oxide/crypto/helioselene/aeneas/helioselene-aeneas.patch
   ```

   Adjust the machine-specific `ec-divisors` absolute path in the patched
   `Cargo.toml` to your checkout (see §4, hunk 1). Then confirm the tests
   still pass: `cargo test --release` (expect 11 passed).

2. With the Aeneas release binaries on `PATH` (they pin rustc
   `nightly-2026-06-01` via their `rust-toolchain`), run the **fifth-run**
   `charon cargo` command from §3 in the patched copy. This produces
   `helioselene_core.llbc`. (Sanity check: the `options` block serialized
   at the head of the `.llbc` file must record the same
   `start_from`/`exclude`/`opaque` set — §3.)

3. Run the `aeneas` command from §3. It emits `HelioseleneCore.lean`,
   `HelioseleneCore/{Types,Funs}.lean`, and
   `HelioseleneCore/{Types,Funs}External_Template.lean`.

4. Diff the new `*External_Template.lean` against the checked-in
   `TypesExternal.lean` / `FunsExternal.lean`. If the external interface
   (names and signatures) is unchanged, keep the existing files. Otherwise
   port the definitional models to the new interface. (The currently
   checked-in files are **not** the raw templates: proof-relevant foreign
   behavior has concrete documented `def` models, while the 39 deliberately
   residual items remain existence-only axioms — see §5c. Only the
   names/signatures come from the template.)

5. Point `lakefile.lean`'s `require aeneas from "…"` at the release's
   `backends/lean` directory, then `lake update && lake build`
   (the mathlib olean cache is fetched automatically; expect the first
   build to take a while).

## 7. Formalization status (2026-07-10)

The external axioms of the original translation have been eliminated (§5c)
and a proof tree (`HelioseleneCore/Spec/`) has been built on the resulting
computable model. Current state, in order of increasing strength:

### Differential validation (`Validation.lean`)

964 independently generated test vectors (edge cases plus random values;
`phase-b/test_vectors.json`, via `gen_validation.py`) are checked against
the *executable* generated functions by `native_decide`, one theorem per
class: `red256`, `red512`, `add`, `sub`, `mul`, `neg`, `double`, `square`,
`invert` (value **and** `is_some` flag) and `from_repr` (value **and**
flag) all match on every vector. This exercises the concrete external
models end-to-end through the translated code. Four contract-bearing
functions have no dedicated vectors — `red1`, `is_zero`, `is_odd`,
`to_repr` — and are covered only by the kernel-checked contracts below
(`red1` is also exercised indirectly through `add`/`double`/`red256`/
`invert`). `Validation.lean` is imported by nothing; its per-theorem
`native_decide` axioms stay out of every proof below. (The Selene scope has
its own 100-vector validation file, `ValidationSelene.lean`, with negative
controls — see the 'Selene group law' block below — and the Helios scope a
75-vector one, `ValidationHelios.lean`, with a deliberately-documented
weaker-signal caveat — see the 'Helios group law' block below.)

### Proved operation contracts (kernel-checked)

The 14 `_ok` contract lemmas, each of the shape
`∃ r, <generated function> … = ok r ∧ <value equation mod p>` (so each also
establishes panic-freedom and termination on its stated domain):

- `add_ok`, `sub_ok`, `neg_ok`, `double_ok`, `is_zero_ok`, `is_odd_ok`,
  `red1_ok` (`Spec/Linear.lean`), `from_repr_ok`, `to_repr_ok`
  (`Spec/Repr.lean`), `red256_ok`, `red512_ok`, `mul_ok`, `square_ok`
  (`Spec/Reduction.lean`) — proved outright;
- `invert_ok` (`Spec/Invert.lean`) — proved from the repaired four-limb
  carry chain, including `step_congruence` and all 510 fixed iterations.

The Selene scope adds its own layer of coordinate-level contracts in
`Spec/Selene/Ops.lean` (`add_coords_ok`, `sub_coords_ok`, `neg_coords_ok`,
`double_coords_ok`, `identity_coords`, `generator_coords`,
`is_identity_ok`, `ct_eq_ok`, `eq_ok`, `curve_equation_ok`, `from_xy_ok`,
`sqrt_ok`, `sqrt_complete`, `recover_y_ok`) — all proved.
The Helios scope adds the sibling layer in `Spec/Helios/Ops.lean` — all
proved, all precondition-free (the coordinate type IS `Fq` and the dalek
coordinate ops are concrete `ZMod` models, so the field-op specs collapse
to `rfl` lemmas; see the file header).

### Primality of `p`, kernel-only

`p_prime : Nat.Prime p` (root namespace, `Spec/Prime.lean`) is proved via
Pratt certificates (`lucas_primality` at the 7 tree nodes) with every
modular exponentiation computed by kernel reduction — no `native_decide`,
no axioms beyond the three standard ones. The certificate requires the
factorization

> p − 1 = 2 · 7451 · p36 · p37, with
> p36 = 534841956073462850512095405427775209 and
> p37 = 7264050700998174191624543895013716307,

which was **not previously published**: factordb held the 73-digit cofactor
p36·p37 as composite with no known factors. It was split with msieve (SIQS)
and double-verified independently; the certificate data in
`Spec/Prime.lean` was generated by `gen_prime.py`.

The Helios stage adds the sibling
`q_prime : Nat.Prime (2^255 − 19)` (`Spec/Helios/Prime25519.lean`,
generated by `tools/gen_prime25519.py`): a 7-node Pratt tree, kernel-only,
likewise no axioms beyond the three standard ones. Unlike p − 1, the
factorization of q − 1 is well known from the Curve25519 literature; it
was fully re-verified locally (one 27-digit interior cofactor split with
msieve) — see `tools/prime25519-certificate.md`.

### Headline theorems

- `HelioseleneSpec.φRing : HField ≃+* ZMod p` (`Spec/Field.lean`) — the
  translated field, on the reduced carrier
  `HField := { u : Uint4 // u.toNat < p }`, is ring-isomorphic to mathlib's
  `ZMod p`. **Sorry-free**; depends on the 3 standard Lean axioms plus the
  four field-layer `_native.decide` constant axioms of §5c (`MODULUS`,
  `MODULUS_255_DISTANCE`, `TWO_MODULUS_255_DISTANCE`,
  `MODULUS_XOR_TWO_MODULUS`) — none of the Selene-scope ones.
- `Fintype HField` with `card_hfield : Fintype.card HField = p`
  (`Spec/Phi.lean`) — 3 standard axioms only.
- `instFieldHField : Field HField` (`Spec/Field.lean`) — sorry-free. Its
  inversion laws consume the proved `HelioseleneSpec.Invert.step_congruence`
  and `invert_ok` contracts for the repaired Algorithm-1 binary-GCD chain
  ([eprint 2020/972](https://eprint.iacr.org/2020/972)).
- `HelioseleneSpec.Selene.ΘAddEquiv : SClass ≃+ W.toAffine.Point`
  (`Spec/Selene/GroupLaw.lean`) — the Selene group law; see the dedicated
  block below. **Sorry-free.**
- `HelioseleneSpec.Helios.ΘAddEquiv : HClass ≃+ W.toAffine.Point`
  (`Spec/Helios/GroupLaw.lean`) — the Helios group law, over the
  **idealized** dalek coordinate boundary; see the dedicated block below.
  **Sorry-free.**
- `SeleneLadder.mul_spec` / `HeliosLadder.mul_spec`
  (`Spec/ScalarMulLaws.lean`) — the complete generated scalar ladders return
  representatives of `scalar_value • point` in `SClass` / `HClass`, including
  totality of every fixed loop and array access. `SeleneAction` and
  `HeliosAction` descend those exact generated results to quotient-level
  `SMul` operations and prove the point-side distribution laws. **Sorry-free.**
- `q_prime : Nat.Prime (2^255 − 19)` (`Spec/Helios/Prime25519.lean`) —
  kernel-only Pratt certificate for the Helios coordinate prime; 3
  standard axioms only.

### What the `Field` instance operations are

- `+`, binary and unary `-`, `*`, `⁻¹` are the Aeneas-translated Rust
  functions (`…Insts.CoreOpsArith{Add,Sub,Mul}….{add,sub,mul}`,
  `…CoreOpsArithNegHelioseleneField.neg`, `field.verified.invert.invert`),
  wrapped total via the `_ok` witnesses; the wrappers were traced down to
  the generated functions by `rfl` during the audit.
- `/` is *defined* as `a * b⁻¹` — the Rust module exposes no division.
- `0` and `1` are the 4-limb literals `0`/`1`, equal in value to the Rust
  constants `Field::ZERO`/`Field::ONE` (the translated `FfField.ZERO`'s
  value is pinned by a spec lemma in `Spec/Linear.lean`; `ff::Field::ONE`,
  untranslated in the first run, is now translated as `FfField.ONE` by the
  second run).
- The auxiliary structure fields (`nsmul`, `zsmul`, `npow`, `zpow` — i.e.
  `^` — `natCast`, `intCast`, `nnqsmul`, `qsmul`, `nnratCast`, `ratCast`)
  are transported from `ZMod p` through the bijection and are **not** Rust
  code: in particular `x ^ n` is *not* the Rust `pow`, which was excluded
  from the translation (§1), and the casts do not go through the Rust
  `From<uN>` impls.

### Selene group law (2026-07-07)

The `Spec/Selene/` tree (`Curve.lean` → `Ops.lean` → `GroupLaw.lean`)
proves that the translated Selene point operations implement the elliptic
curve group `y² = x³ − 3x + B` over `ZMod p`:

- **`ΘAddEquiv : SClass ≃+ W.toAffine.Point` — sorry-free.** `SClass` is
  the quotient of on-curve reduced projective representatives by projective
  equivalence; `W` is mathlib's short-Weierstrass curve with
  `a₁ = a₂ = a₃ = 0`, `a₄ = −3`, `a₆ = B`. Kernel `#print axioms`: the 3
  standard axioms plus 4 of the §5c string-length constant axioms
  (`MODULUS`, `MODULUS_255_DISTANCE`, `point.selene.B`,
  `TWO_MODULUS_255_DISTANCE`); **no `sorryAx`**, none of the existence-only
  axioms (54 at this stage's snapshot, 48 after the third run, 39 now —
  §5c; the per-theorem sets are recorded in
  `Spec/Selene/GroupLaw.lean` §9).
- **`instAddCommGroupSClass : AddCommGroup SClass`** whose `0`, `+`, unary
  `-` and binary `-` are definitionally (`rfl`, via
  `SClass_zero/add/neg/sub_def`) the descended Rust operations
  `identity`/`add`/`neg`/`sub` — where "descended" bottoms out at the
  choice-extracted wrappers, which are tied to the generated functions by
  the propositional `*_ok` equations (`GroupLaw.lean` §5 header spells out
  this exact boundary). `SClass_double` additionally proves the dedicated
  dbl-2007-bl-2 doubling circuit computes `+` on classes, and
  `ct_eq_decides`/`eq_decides`/`is_identity_decides` prove the translated
  equality tests decide class equality/identity. The `ℕ`/`ℤ`-scalar
  actions of the group instance remain `ΘEquiv`-transported auxiliaries, but
  `Spec/ScalarMulLaws.lean` now proves the translated Rust ladder returns
  exactly the corresponding natural action (`SeleneAction.smul_eq_nsmul`) and
  ties its result-valued adapter to the descended representative
  (`result_smul_eq_generated_rep`).
- **Kernel-proved number theory** (`Curve.lean`, no `native_decide`): `B`
  is a quadratic non-residue mod `p` (Euler criterion; hence no affine
  point has `x = 0`, the soundness of `is_identity`), the curve has **no
  2-torsion** (`cubic_no_root`, via a kernel `X^p mod (X³−3X+B)`
  computation with a Bezout certificate), and the discriminant is nonzero
  (`delta_ne_zero` → `W.IsElliptic`). These feed the completeness of the
  RCB complete-addition formulas.
- **Sorry status (updated 2026-07-10 — ZERO remain tree-wide)**:
  `Invert.step_congruence` is proved after replacing the conditional top-bit
  OR with the exact high-half carry-chain addition documented in §4. The proof
  establishes the per-step machine ledger, invariant preservation and potential
  halving without `UVWindow`; `invert_ok`, `HField.inv`, `φ_inv`, `φ_div` and
  `instFieldHField` are no longer tainted. `Selene.sqrt_complete` is also proved
  kernel-only (16-entry table spec, addition-chain spec, a 125-iteration
  window-loop invariant over the concrete exponent bits, and Euler criterion).
- **Validation** (`ValidationSelene.lean`, imported by nothing): 100
  independent Selene vectors — sqrt 25, add 35, double 15, neg 5, ct_eq
  12, from_xy 8 — pass through the *executable* translated `point.selene.*`
  code by `native_decide`, plus ad-hoc structural checks (constants,
  generator) and per-class corrupted-vector **negative controls**
  (`validationSelene_negative_controls`) guarding the checkers against
  vacuous acceptance.

### Helios group law (2026-07-08)

The `Spec/Helios/` tree (`Prime25519.lean` → `Curve.lean` → `Ops.lean` →
`GroupLaw.lean`; sibling of the Selene tree, same section structure and
theorem names) proves that the translated Helios point operations implement
the elliptic curve group `y² = x³ − 3x + B_helios` over
`Fq = ZMod (2^255 − 19)` — **over the IDEALIZED dalek coordinate boundary**
(fourth bullet below):

- **`Helios.ΘAddEquiv : HClass ≃+ W.toAffine.Point` — sorry-free.**
  `HClass` is the quotient of on-curve projective representatives by
  projective equivalence; `W` is mathlib's short-Weierstrass curve with
  `a₁ = a₂ = a₃ = 0`, `a₄ = −3`, `a₆ = B_helios`. Kernel `#print axioms`:
  the 3 standard axioms plus `point.helios.B._native.decide.ax_1` (one of
  the §5c.3 string-length axioms); **no `sorryAx`**, **none of the 39
  existence-only axioms**, and — unlike Selene — no `field.MODULUS`-family
  axiom (the Helios coordinate field has no limb layer). The per-theorem
  sets are recorded in `Spec/Helios/GroupLaw.lean` §9.
- **`instAddCommGroupHClass : AddCommGroup HClass`** whose `0`, `+`, unary
  `-` and binary `-` are definitionally the descended translated Rust
  operations (same choice-extracted-wrapper boundary as Selene, spelled
  out in the file's §5 header). `HClass_double` proves the dedicated
  dbl-2007-bl-2 doubling circuit computes `+` on classes;
  `ct_eq_decides`/`eq_decides`/`is_identity_decides` prove the translated
  equality tests decide class equality/identity-ness; `gen_ne_zero` and
  the `Nontrivial HClass` instance pin non-degeneracy (the quotient
  provably does not trivialize). The `ℕ`/`ℤ`-scalar actions are
  `ΘEquiv`-transported auxiliaries; `Spec/ScalarMulLaws.lean` now connects the
  translated Rust ladder to that natural action through
  `HeliosAction.smul_eq_nsmul` and `result_smul_eq_generated_rep`.
- **Kernel-proved number theory** (`Prime25519.lean`/`Curve.lean`, no
  `native_decide`): `q_prime : Nat.Prime (2^255 − 19)` (7-node Pratt
  certificate), `B_helios` is a quadratic non-residue mod q (so no affine
  point has `x = 0` — the soundness of `is_identity`), the curve has **no
  2-torsion** (`cubic_no_root`, the polynomial Fermat/Bézout certificate
  technique instantiated at `(q, B_helios)` by `tools/gen_curve_helios.py`),
  and the discriminant is nonzero (`W.IsElliptic`). The constants are
  traced to the `point.rs` hex literals kernel-only (`B_ok`/`G_Y_ok`).
- **THE assumption specific to this stage — boundary fidelity.** The
  Helios coordinate type is the foreign `dalek_ff_group::FieldElement`,
  DEFINED in the model as `ZMod (2^255 − 19)` with 28 concrete `ZMod`
  operation models (§5c, third-run block). Everything above is therefore a
  theorem about the translated group-law formulas over an **ideal field**:
  it says nothing about dalek-ff-group's actual Montgomery arithmetic
  (crypto-bigint 0.5.5 `Residue` under dalek-ff-group 0.5.0 — NOT
  curve25519-dalek, and no fiat-crypto backend is involved). The per-item
  fidelity obligations, and the human verification checklist for them, are
  enumerated in **`human_audit_assumptions_helios.txt`** — the Helios
  counterpart of `human_audit_assumptions_selene.txt`.
- **Validation** (`ValidationHelios.lean`, imported by nothing): 75
  independent Helios vectors — add 35, double 15, neg 5, ct_eq 12,
  from_xy 8 (`tools/helios_vectors.json`, generated by
  `tools/gen_validation_helios.py`) — pass through the *executable*
  translated `point.helios.*` code by `native_decide`, plus structural
  checks and per-class corrupted-vector **negative controls**. **This is a
  strictly weaker signal than `ValidationSelene.lean`**: the field ops are
  ideal by construction (the coordinate type IS `ZMod`), so the vectors
  validate the translated group-law formulas and the model plumbing
  (constants via `from_u256`/`from_be_hex`, `Choice`/`CtOption`
  conventions, `conditional_select`, projective identity handling), not
  any field-arithmetic implementation — the caveat is spelled out in the
  file header.

### Scalar-multiplication correctness and laws (2026-07-10)

`Spec/ScalarMulLaws.lean` closes the functional-correctness gap left by the
result-valued adapters in `Spec/ScalarMul.lean`:

#### Rust-to-Lean boundary for the scalar theorem

The headline ladder theorems are about the exact Aeneas definitions generated
from the **patched translation copy**. They are connected propositionally all
the way back to those generated `mul` functions; no handwritten replacement
multiplier is used. Relating that model to production Rust nevertheless has
three explicit, independent human obligations:

- Review hunk 8 against production `src/point.rs`: the canonical bit iterator,
  consumed-bit clearing, table-loan block, copied candidates, two fixed-loop
  unrollings, and `AddAssign` rewrite must be value-equivalent. The patch lives
  only in the scratch translation copy and applies to both curves through the
  shared `curve!` macro.
- Trust the pinned rustc/Charon/Aeneas pipeline to preserve the patched Rust
  semantics, and review the concrete external models used in the generated
  call graph. In particular, scalar `to_repr` must be canonical
  little-endian; `usize::ct_eq` and point `conditional_select` must have the
  stated value semantics; and the zeroization and machine-array models must
  match their Rust operations. The complete per-curve checklists are
  `human_audit_assumptions_selene.txt` §V and
  `human_audit_assumptions_helios.txt` §V.
- For Helios, every precomputation addition, doubling, and selection inherits
  the idealized coordinate-field assumption
  `dalek_ff_group::FieldElement := ZMod (2^255 - 19)`. For Selene, the same
  dalek type is the scalar, so its canonical-value/byte model is load-bearing,
  while point coordinates use the verified helioselene field.

Within those boundaries, the proof covers every modeled failure point and
iteration. It does not claim constant-time execution, compiler preservation of
the unrolled scan, physical zeroization, or correctness for arbitrary raw
off-curve points. The generic loop lemmas cover every natural `< 2^256`; the
public theorems start from verified on-curve representatives and the actual
canonical scalar values.

#### Proven result and algebraic-law boundary

- `SeleneLadder.mul_spec` proves the generated Selene `mul` returns an
  on-curve representative of `scalar.toZMod.val • SClass.mk P`.
  `HeliosLadder.mul_spec` proves the generated Helios `mul` returns a
  representative of `scalar.toNat • HClass.mk P`. These proofs cover the
  translated 16-entry table construction, the bit-clearing mutation, the
  unrolled full table scan (the Rust constant-time structure at value level),
  all 256 loop iterations, all bounds and termination measures, and the
  dead-value zeroization calls. They do not use an alternative multiplication
  implementation and do not establish a timing theorem.
- `SeleneAction.mulP_generated` and `HeliosAction.mulP_generated` identify the
  carrier representatives extracted by the quotient actions with the exact
  generated Aeneas functions. `result_smul_eq_generated_rep` connects those
  representatives back to the original `Result Point` `SMul` adapters.
- The law-bearing Selene scalar type is
  `SeleneAction.Scalar = ZMod (2^255 - 19)`, exactly the value type used by the
  concrete `dalek_ff_group::FieldElement` model; the generated call is made
  through `FieldElement.ofZMod`. The Helios action uses the verified
  `HField = {u : Uint4 // u.toNat < p}` and calls the generated ladder on
  `scalar.val`.
- Without any curve-order premise, both actions prove `zero_smul`, `one_smul`,
  `smul_zero`, and `smul_add`, and install `DistribSMul`. These are genuine
  laws of the transpiled computation because each action first descends the
  successful generated result and is then proved equal to natural repeated
  addition.
- `add_smul` and `mul_smul` reduce scalar addition/multiplication modulo the
  scalar-field modulus. They therefore require exactly that the modulus
  annihilate the point group. The file names these propositions
  `SeleneExponent` (`(2^255 - 19) • P = 0`) and `HeliosExponent`
  (`p • P = 0`), proves both remaining laws from the corresponding proposition,
  and constructs `SeleneAction.moduleOfExponent` /
  `HeliosAction.moduleOfExponent`. Standard `Module` instances become
  available through `SeleneExponentCertificate` /
  `HeliosExponentCertificate`.

No exponent certificate instance is provided in this repository. Proving one
requires the external cycle/cardinality facts `#Selene = 2^255 - 19` and
`#Helios = p` (or another proof that those moduli annihilate every point).
Consequently the unconditional ladder theorem and `DistribSMul` instances are
closed and assumption-free, while the two scalar-ring laws are proved with
their exact mathematical premise visible in the theorem and type-class
signatures. No `axiom`, `sorry`, default point, or failure-erasing wrapper is
used to cross that boundary.

### Remaining work

1. Prove the two curve-cardinality/exponent certificates if unconditional
   `Module` instances are required. The ladder proofs themselves are complete;
   this is a curve-order theorem, not an implementation-correctness gap.
2. Optionally purge the nine `<const>._native.decide.ax_1` axioms by
   regenerating `Funs.lean` with explicit autoParam proofs, or by patching
   the Aeneas Std library's `toStr` default tactic (§5c).
3. Optionally report the p − 1 factors to factordb so the Pratt
   certificate is independently reproducible.
4. Add hand-written per-declaration review comments for the 229 new
   generated declarations (the second run's 130 plus the third run's 99,
   and the 20 + 4 new `Types.lean` ones; they currently carry only the
   generated Aeneas metadata comments; `MAPPING.md`'s appended sections
   track this).
