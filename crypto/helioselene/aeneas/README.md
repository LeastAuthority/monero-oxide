# Aeneas translation of the helioselene verified field arithmetic

This directory contains a Lean 4 model of `crypto/helioselene`'s
`field::verified` module — the code
[formally verified by Veridise in Dafny](https://github.com/VeridiseAuditing/helioselene-dafny-proofs)
per the header of `src/field/verified/mod.rs` — mechanically translated from
the Rust source with [Charon](https://github.com/AeneasVerif/charon) (MIR →
LLBC extraction) and [Aeneas](https://github.com/AeneasVerif/aeneas) (LLBC →
pure Lean functions).

The model is a **functional** model: it captures input/output behaviour
(including panics and non-termination) of the Rust functions under one fixed
build configuration, and nothing else. Section
[Assumptions required for equivalence](#assumptions-required-for-equivalence)
enumerates exactly what has to be trusted, assumed, or supplied before a Lean
theorem about this model says anything about the compiled Rust.

## 1. Overview

### What was translated

Translation root: `helioselene::field::verified`, i.e. everything reachable
from that module except the two explicit exclusions below. Concretely,
`HelioseleneCore/Funs.lean` contains definitions for:

- **Reduction** (`src/field/verified/red.rs`): `red256`, `red512`, and the
  constant `TWO_MODULUS_255_DISTANCE`.
- **Inversion** (`src/field/verified/invert.rs`): `invert`, its inner `step`
  (with inner `select` and the constant `MODULUS_XOR_TWO_MODULUS`), and
  `sub_with_bounded_overflow`.
- **Field operations** (`src/field/verified/mod.rs`): the `Add`, `Sub`,
  `Neg`, `Mul` trait impls for `HelioseleneField`, `double`, `square`,
  `is_zero`, `is_odd`, `from_repr` (with its inner `reduced`), `to_repr`,
  the helpers `add_with_bounded_overflow`, `select_word`, `sub_value`,
  `red1`, and the constant `MODULUS_255_DISTANCE`.
- **Items from `src/field/mod.rs` pulled in by the call graph**: the
  `MODULUS` constant, `HelioseleneField`'s
  `ConditionallySelectable::conditional_select`, and the `ff::Field`
  associated items `ZERO` and `is_zero` (used by `Neg` and `invert`).

All of this translated with **zero `sorry`s** in the generated model — the
hand-written proof tree under `HelioseleneCore/Spec/` adds exactly one
(`Invert.step_congruence`, see [§7](#7-formalization-status-2026-07-07)) —
and the resulting Lean package builds (`lake build`; `.olean` artifacts for
all modules are present in `.lake/build`). Rust `for` loops are extracted as
separate
`*_loop` / `*_loop.body` definitions per the Aeneas loop encoding (see
[§5e](#e-loop-and-divergence-modeling)).

### What was NOT translated, and why

- `verified::sqrt` and `verified::pow` (excluded via `--exclude`): both
  iterate over `FieldBits`/`bitvec` bit views using iterator adapters —
  `sqrt` uses `.to_le_bits().iter().take(253).rev().skip(128)`, `pow` uses
  `.to_le_bits().iter_mut().rev().enumerate()`. The signatures of these
  adapters involve nested borrows, which Aeneas cannot currently express;
  `pow` additionally calls `crate::u8_from_bool`, which is built on
  `core::hint::black_box` (an optimisation barrier with no functional
  meaning that the toolchain does not model).
- `point.rs` and `ciphersuite.rs` (Helios/Selene group logic,
  hash-to-curve): outside the translation root, and blocked by the same
  iterator-adapter limitation plus the `black_box`-based `u8_from_bool` used
  for bit handling in the scalar-multiplication ladder.
- The `Sum`/`Product` impls for `HelioseleneField` and `ff::Field::sqrt`
  were declared **opaque** (see [§3](#3-toolchain-and-provenance)) and do
  not appear in the output at all. No translated function depends on their
  bodies (verified by grep over `Funs.lean`; see
  [§5g](#g-struct-flattening-and-trait-encoding)).
- Foreign crates (`crypto-bigint`, `subtle`) are **not translated** —
  Charon's default treatment of foreign bodies leaves them as external
  declarations. They are instantiated here with concrete definitional
  models (`TypesExternal.lean` / `FunsExternal.lean`); the fidelity of
  those models to the Rust crates is the trusted base of the model; see
  [§5c](#c-trusted-base-external-models-and-residual-axioms).

## 2. Directory contents

| File | Role | Edit? |
|---|---|---|
| `HelioseleneCore.lean` | Library entry point: `import HelioseleneCore.Funs` (the `aeneas -gen-lib-entry` output) plus `import HelioseleneCore.Spec.Field` (the proof tree). | Import list only |
| `HelioseleneCore/Types.lean` | Generated type definitions: `Add`/`Sub`/`Mul`/`Neg` trait declaration records, `crypto_bigint.limb.Limb := Std.U64`, `field.HelioseleneField := crypto_bigint.uint.Uint 4#usize`. | No — regenerate |
| `HelioseleneCore/Funs.lean` | Generated function definitions (~2,900 lines including added documentation comments): the translated call graph listed in §1. | No — regenerate |
| `HelioseleneCore/TypesExternal.lean` | Concrete computable **definitions** (not axioms) modeling the 3 external types: `Uint LIMBS := Aeneas.Std.Array U64 LIMBS` (little-endian limb vector), `subtle.Choice := Bool`, `subtle.CtOption T := T × Bool`. Instantiated from the generated template; each `def` carries a doc comment citing the `crypto-bigint` 0.5.5 / `subtle` 2.6.1 source it models. | **Yes** — hand-written models (§5c) |
| `HelioseleneCore/FunsExternal.lean` | Concrete computable **definitions** modeling the 34 external functions/constants (27 functions + 7 constants) of `crypto-bigint`/`subtle`, each defined as the exact `Nat`-level computation on the limb vectors, documented against the crate sources. | **Yes** — hand-written models (§5c) |
| `HelioseleneCore/Validation.lean` | Generated differential validation of the (computable) model against 964 independent test vectors, checked by `native_decide` (§7). **Not imported by the library entry point** — built only via the lakefile's submodule glob, so its `native_decide` axioms stay out of every proof's dependency cone. | No — regenerate (`gen_validation.py`) |
| `HelioseleneCore/Spec/Externals.lean` | Spec lemmas for the external models, plus kernel-only re-derivation of the generated hex-string constants (`MODULUS_ok` etc.). | **Yes** — proofs |
| `HelioseleneCore/Spec/Phi.lean` | The abstraction layer: reduced carrier `HField`, bijection `φ`/`equivZMod` with `ZMod p`, `Fintype HField`, `card_hfield`. | **Yes** — proofs |
| `HelioseleneCore/Spec/Prime.lean` | Kernel-only Pratt-certificate proof of `p_prime` (§7). | No — regenerate (`gen_prime.py`) |
| `HelioseleneCore/Spec/Linear.lean` | Proved contracts for the linear ops: `red1_ok`, `add_ok`, `double_ok`, `sub_ok`, `neg_ok`, `is_zero_ok`, `is_odd_ok`. | **Yes** — proofs |
| `HelioseleneCore/Spec/Repr.lean` | Proved contracts for the byte encodings: `from_repr_ok`, `to_repr_ok`. | **Yes** — proofs |
| `HelioseleneCore/Spec/Reduction.lean` | Proved contracts for reduction and multiplication: `red256_ok`, `red512_ok`, `mul_ok`, `square_ok`. | **Yes** — proofs |
| `HelioseleneCore/Spec/Invert.lean` | Contract for constant-time inversion (`invert_ok`), assembled modulo the development's single `sorry` (`step_congruence`, §7). | **Yes** — proofs |
| `HelioseleneCore/Spec/Field.lean` | `Field HField` instance and the ring isomorphism `φRing : HField ≃+* ZMod p`; axiom audit (§7). | **Yes** — proofs |
| `helioselene-aeneas.patch` | The diff against `crypto/helioselene` that the translation was produced from (§4). The repository tree itself is untouched; the patch was applied to a scratch **copy**. | — |
| `MAPPING.md` | Machine-generated per-declaration Lean-to-Rust index with pinned links. | No — regenerate |
| `lakefile.lean` | Lake package; `require aeneas from` the Aeneas Lean support library **by absolute path** — adjust to your extraction of the Aeneas release. | Path only |
| `lean-toolchain` | `leanprover/lean4:v4.30.0-rc2`. | No |
| `lake-manifest.json` | Pinned Lake dependencies (the `aeneas` library and its transitive deps: mathlib, batteries, aesop, …). | No |
| `.lake/` | Build artifacts. | — |

## 3. Toolchain and provenance

| Component | Version / identity | How verified |
|---|---|---|
| monero-oxide source | commit `6313959f906fe754909754ac642134237dae42a9` (branch `fcmp++`); `crypto/helioselene/src` unmodified in the working tree | `git log` / `git status` |
| Aeneas | release `nightly-2026.07.06-45061fa` (prebuilt binaries: `aeneas`, `charon`, `charon-driver`, `backends/lean`) | `aeneas -version` |
| Charon | `0.1.218`, bundled with the Aeneas release | `charon version` |
| rustc | `nightly-2026-06-01` (pinned by the release's `rust-toolchain`) | toolchain file |
| Lean | `v4.30.0-rc2` | `lean-toolchain` |
| `crypto-bigint` | 0.5.5 | `Cargo.lock` of the translated copy |
| `subtle` | 2.6.1 | `Cargo.lock` of the translated copy |

Charon and Aeneas were run **once, on 2026-07-06**, on a patched copy of
`crypto/helioselene` (§4), with:

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

```sh
aeneas -backend lean -split-files -gen-lib-entry -dest . helioselene_core.llbc
```

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
- `--start-from 'helioselene::field::verified'` — restrict translation
  roots to the verified module instead of the whole crate; only items
  reachable from it are extracted.
- `--exclude …::sqrt / …::pow` — drop the two functions Aeneas cannot
  handle (§1); the rest of the module does not call them.
- `--opaque` on the `Sum`/`Product` impls and `ff::Field::sqrt` —
  `ff::Field` (needed for `Field::ZERO`/`is_zero`, which `Neg` and `invert`
  use) has `Sum`/`Product` supertrait bounds, and its `sqrt` is required by
  the trait; translating their bodies drags in
  `Iterator::copied`/`sum`/`product` adapters whose signatures crash
  Aeneas' signature translation. Opacity keeps the trait resolvable while
  dropping the bodies. Since no translated function calls them, this is
  scope reduction, not an extra assumption ([§5g](#g-struct-flattening-and-trait-encoding)).
- `-- --no-default-features --release` — cargo arguments; part of the baked
  build configuration ([§5b](#b-build-configuration-baked-into-the-model)).
- `-split-files -gen-lib-entry` — emit `Types`/`Funs`/`*External_Template`
  as separate files plus the library entry point.

## 4. Changes made to the Rust code

The translation input was a **copy** of `crypto/helioselene` with
`helioselene-aeneas.patch` applied. The repository tree is untouched. The
patch makes two build-only `Cargo.toml` changes and three
semantics-preserving source rewrites; each is argued below. **Test evidence**: on the patched copy,
`cargo test --release` passes 11/11 tests (re-run and confirmed on
2026-07-06), including `field::test_helioselene_field` (the
`ff-group-tests` prime-field suite, incl. the bits tests),
`field::verified::red::tests_assuming_64_bits::test_reduction_of_each_bit`
(reduction of every one of the 512 bits, checked against `crypto-bigint`'s
`checked_rem`), `field::tests_assuming_64_bits::test_wide_reduction`
(1,000 random 512-bit reductions plus `U512::MAX`),
`field::verified::invert::invert_3_66`, and the point/group tests.

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

The external interface (3 types + 34 functions/constants over
`crypto-bigint` 0.5.5 and `subtle` 2.6.1) was emitted by Aeneas as axiom
templates. On 2026-07-07 those axioms were **eliminated by instantiation**:
`TypesExternal.lean` and `FunsExternal.lean` now contain concrete,
computable **definitions** — `Uint LIMBS := Aeneas.Std.Array U64 LIMBS`
(little-endian limb vector), `subtle.Choice := Bool`,
`subtle.CtOption T := T × Bool`, and 34 definitional models of the
`crypto-bigint`/`subtle` operations, each defined as the exact `Nat`-level
computation. Unlike axioms, `def`s cannot introduce logical inconsistency
(Lean checks them for well-formedness), and they make the whole model
executable — which is what enables the differential validation of §7.

What remains trusted:

1. **Tool trust** (§5a) — unchanged.
2. **Fidelity of the 37 concrete external models** to the actual
   `crypto-bigint` 0.5.5 / `subtle` 2.6.1 semantics. A subtly wrong model
   yields proofs about a different program. Mitigations: every model
   carries a doc comment citing the crate source it implements (the table
   below is the review checklist); the 964-vector differential validation
   (`Validation.lean`, §7) exercises the translated functions — and
   therefore the models under them — against independently generated
   vectors; and `Spec/Externals.lean` proves a value-level spec lemma for
   each model. One known, benign divergence: `shl_vartime`/`shr_vartime`
   are modeled as `fail panic` for shift amounts ≥ 64·LIMBS, where
   `crypto-bigint` returns `ZERO` — unreachable at all call sites (every
   call shifts by the constant 1). Note also that the models live in
   `Result`, so they decide panic behaviour (e.g. `from_le_slice` fails
   unless the slice length is `8·LIMBS`, mirroring the Rust panic), and
   that `Uint.LIMBS_1` feeds the **loop bounds** of `is_zero`, `red1`,
   `sub`, `red256`, `red512`, `from_repr::reduced`, and the inversion path
   (`invert`, `invert.step`, `invert.step.select`): a wrong value would
   change iteration counts, not just values.
3. **Four generated `native_decide` axioms.** The four hex-string constants
   in `Funs.lean` (`field.MODULUS`, `field.verified.MODULUS_255_DISTANCE`,
   `field.verified.red.TWO_MODULUS_255_DISTANCE`,
   `field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS`) call
   `Aeneas.Std.toStr`, whose length side-condition autoParam is
   `by decide +native`. This bakes one `<const>._native.decide.ax_1` axiom
   into each generated *definition*, and every theorem that mentions those
   constants transitively inherits them. Each axiom asserts only the
   trivially-true statement that a 32/64-character string literal is at
   most `U32.max` bytes — **not** the constant's value. The values
   themselves are independently re-proved kernel-only in
   `Spec/Externals.lean` (the `toStr_val` rewrite plus plain kernel
   `decide`: `MODULUS = p`, `MODULUS_255_DISTANCE = 2^255 − p`,
   `TWO_MODULUS_255_DISTANCE = 2·(2^255 − p)`,
   `MODULUS_XOR_TWO_MODULUS = p XOR 2p`). Eliminating these four axioms
   entirely would require regenerating `Funs.lean` with explicit autoParam
   proofs, or patching the Aeneas Std library's `toStr` default tactic —
   both touch generated/vendored code, so they are recorded as trust
   instead (see §7, remaining work).

Aside from those four (and, in the never-imported `Validation.lean`, one
per-theorem native-decide axiom per validation theorem), the development
uses no axioms beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`) — see the axiom audit at the bottom of
`Spec/Field.lean`.

Full model list, grouped by crate, with the modeled semantics checked
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
- **Zeroization.** `zeroize`-on-drop of secrets does not exist in a pure
  model.
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
- The `Sum`/`Product` impls and `ff::Field::sqrt` were opaque and are
  **entirely absent** from the generated files (no declaration, no axiom).
  This is sound for the verified-core functions because nothing in the
  translated call graph references them — `ff::Field` machinery appears
  only via the standalone `FfField.ZERO` / `FfField.is_zero` definitions,
  whose bodies are fully translated.

### h. Scope

Only `field::verified` **minus `sqrt` and `pow`** is modeled. In
particular:

- Nothing about `point.rs` (Helios/Selene group law, decompression,
  doubling), `ciphersuite.rs`, or hash-to-curve is modeled; statements
  about the *curves* are entirely out of scope.
- `HelioseleneField::from_u256` (`const_rem`-based), `Field::random`,
  `sqrt_ratio`, the `From<u8/u16/u32/u64>` conversions, `ct_eq` on field
  elements, and the `PrimeFieldBits` bit decompositions are not modeled.
- The Veridise Dafny verification and this Lean model share the same
  *intended* scope (the `verified` module) but neither subsumes the other:
  the Dafny proofs verified a Dafny translation of this code (as the crate
  README notes), and this model is an unverified mechanical translation
  awaiting proofs.

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
   `nightly-2026-06-01` via their `rust-toolchain`), run the `charon cargo`
   command from §3 in the patched copy. This produces
   `helioselene_core.llbc`.

3. Run the `aeneas` command from §3. It emits `HelioseleneCore.lean`,
   `HelioseleneCore/{Types,Funs}.lean`, and
   `HelioseleneCore/{Types,Funs}External_Template.lean`.

4. Diff the new `*External_Template.lean` against the checked-in
   `TypesExternal.lean` / `FunsExternal.lean`. If the external interface
   (names and signatures) is unchanged, keep the existing files. Otherwise
   port the definitional models to the new interface. (The currently
   checked-in files are **not** the raw templates: every template axiom has
   been replaced by a concrete `def` model with documentation — see §5c.
   Only the names/signatures come from the template.)

5. Point `lakefile.lean`'s `require aeneas from "…"` at the release's
   `backends/lean` directory, then `lake update && lake build`
   (the mathlib olean cache is fetched automatically; expect the first
   build to take a while).

## 7. Formalization status (2026-07-07)

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
`native_decide` axioms stay out of every proof below.

### Proved operation contracts (kernel-checked)

The 14 `_ok` contract lemmas, each of the shape
`∃ r, <generated function> … = ok r ∧ <value equation mod p>` (so each also
establishes panic-freedom and termination on its stated domain):

- `add_ok`, `sub_ok`, `neg_ok`, `double_ok`, `is_zero_ok`, `is_odd_ok`,
  `red1_ok` (`Spec/Linear.lean`), `from_repr_ok`, `to_repr_ok`
  (`Spec/Repr.lean`), `red256_ok`, `red512_ok`, `mul_ok`, `square_ok`
  (`Spec/Reduction.lean`) — proved outright;
- `invert_ok` (`Spec/Invert.lean`) — fully assembled modulo the
  development's single `sorry` (below).

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

### Headline theorems

- `HelioseleneSpec.φRing : HField ≃+* ZMod p` (`Spec/Field.lean`) — the
  translated field, on the reduced carrier
  `HField := { u : Uint4 // u.toNat < p }`, is ring-isomorphic to mathlib's
  `ZMod p`. **Sorry-free**; depends on the 3 standard Lean axioms plus the
  four `_native.decide` constant axioms of §5c.
- `Fintype HField` with `card_hfield : Fintype.card HField = p`
  (`Spec/Phi.lean`) — 3 standard axioms only.
- `instFieldHField : Field HField` (`Spec/Field.lean`) — complete modulo
  exactly **one** `sorry`: `HelioseleneSpec.Invert.step_congruence`
  (`Spec/Invert.lean`), the per-step preservation of the Algorithm-1
  binary-GCD invariant
  ([eprint 2020/972](https://eprint.iacr.org/2020/972)). Its *statement*
  was adversarially reviewed; discharging it makes the `Field` instance
  sorry-free.

### What the `Field` instance operations are

- `+`, binary and unary `-`, `*`, `⁻¹` are the Aeneas-translated Rust
  functions (`…Insts.CoreOpsArith{Add,Sub,Mul}….{add,sub,mul}`,
  `…CoreOpsArithNegHelioseleneField.neg`, `field.verified.invert.invert`),
  wrapped total via the `_ok` witnesses; the wrappers were traced down to
  the generated functions by `rfl` during the audit.
- `/` is *defined* as `a * b⁻¹` — the Rust module exposes no division.
- `0` and `1` are the 4-limb literals `0`/`1`, equal in value to the Rust
  constants `Field::ZERO`/`Field::ONE` (the translated `FfField.ZERO`'s
  value is pinned by a spec lemma in `Spec/Linear.lean`; `ff::Field::ONE`
  has no translated counterpart).
- The auxiliary structure fields (`nsmul`, `zsmul`, `npow`, `zpow` — i.e.
  `^` — `natCast`, `intCast`, `nnqsmul`, `qsmul`, `nnratCast`, `ratCast`)
  are transported from `ZMod p` through the bijection and are **not** Rust
  code: in particular `x ^ n` is *not* the Rust `pow`, which was excluded
  from the translation (§1), and the casts do not go through the Rust
  `From<uN>` impls.

### Remaining work

1. Discharge `Invert.step_congruence` (the per-step lemmas of the
   [Veridise Dafny proofs](https://github.com/VeridiseAuditing/helioselene-dafny-proofs)
   cover the same invariant and are the natural cross-reference).
2. Optionally purge the four `<const>._native.decide.ax_1` axioms by
   regenerating `Funs.lean` with explicit autoParam proofs, or by patching
   the Aeneas Std library's `toStr` default tactic (§5c).
3. Optionally report the p − 1 factors to factordb so the Pratt
   certificate is independently reproducible.
