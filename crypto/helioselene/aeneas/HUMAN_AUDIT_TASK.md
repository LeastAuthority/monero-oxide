# Human audit task for the complete Helios/Selene Lean proof boundary

Status: audit brief for the 2026-07-10 Aeneas/Lean artifact.

This is the single entry point for a human audit of all trust boundaries left
after the field, Selene group, Helios group, and scalar-multiplication proofs.
It consolidates the three historical assumption ledgers:

- `human_audit_assumptions.txt`
- `human_audit_assumptions_selene.txt`
- `human_audit_assumptions_helios.txt`

Those files remain useful evidence and preserve historical findings. This task
is the current combined checklist. If a statement here conflicts with a
historical entry, check the current source/generated artifact and record the
discrepancy; do not silently choose either statement.

## 1. Objective

Determine whether the proved Lean statements faithfully describe the relevant
compiled Rust behavior, and identify every claim that remains outside that
connection.

The audit is complete only when humans have reviewed:

1. the one semantic production Rust correction;
2. every translation-only Rust rewrite;
3. the rustc -> MIR -> Charon LLBC -> Aeneas Lean correspondence;
4. all 6 external type models and all 92 concrete external function models;
5. every explicit or compiler-generated axiom in the package;
6. the proof-domain refinements, especially reduced field values and on-curve
   points;
7. the idealized Helios coordinate field;
8. the unproved curve-exponent/cardinality statements;
9. all excluded, opaque, translated-but-unspecified, and otherwise out-of-scope
   Rust behavior; and
10. constant-time, zeroization, layout, compiler, and side-channel properties
    erased by the functional model.

Do not spend audit time re-proving algebra that Lean already checks. Review the
boundaries where a kernel theorem is connected to Rust, a foreign crate, a
build configuration, or an intended protocol claim.

## 2. Claims whose boundaries are being audited

| ID | Kernel-checked result | Rust-facing interpretation | Boundary that remains human-audited |
|---|---|---|---|
| F | `HField ≃+* ZMod p`, `Field HField`, `card HField = p`, `p_prime` | The translated helioselene field operations implement the prime field of order `p` on reduced Rust values | Translation/tool fidelity, external `crypto-bigint`/`subtle` models, 64-bit release configuration, and the Rust reducedness invariant |
| S | `Selene.ΘAddEquiv : SClass ≃+ W.toAffine.Point`, `AddCommGroup SClass` | The translated Selene identity/add/double/neg/sub and equality tests implement the curve group on valid projective representatives | Generated-code correspondence, field boundary F, constants, point input refinement, and excluded encoding/security properties |
| H | `Helios.ΘAddEquiv : HClass ≃+ W.toAffine.Point`, `AddCommGroup HClass` | The translated Helios point formulas implement the curve group on valid projective representatives | All ordinary translation boundaries plus the load-bearing idealization `dalek FieldElement := ZMod (2^255-19)` |
| MS | `SeleneLadder.mul_spec`, `SeleneAction.smul_eq_nsmul`, `DistribSMul` | The exact generated Selene ladder computes repeated addition by the canonical dalek scalar value | Hunk 8 equivalence, dalek scalar representation, selection/zeroize models, and on-curve input refinement |
| MH | `HeliosLadder.mul_spec`, `HeliosAction.smul_eq_nsmul`, `DistribSMul` | The exact generated Helios ladder computes repeated addition by the helioselene scalar value | Hunk 8 equivalence, translated scalar serialization, Helios ideal coordinate field, and on-curve input refinement |
| MOD | `moduleOfExponent` for both curves | Full field-scalar `Module` laws follow if the scalar modulus annihilates every point | `SeleneExponent` and `HeliosExponent` are explicit premises; no certificate is supplied or assumed |
| ENC | Partial Selene encoding/recovery contracts; translated Helios encoding functions | Some encoding components execute in the model | No complete Selene round-trip/canonicality theorem; Helios encoding contracts cross opaque dalek operations |

The phrase "everything proven" in this artifact means the implementation
contracts and conditional algebraic laws above are sorry-free. It does not turn
the human boundaries in the final column into theorems.

## 3. Auditor output requirements

Produce one report with a row for every task ID in sections 5-17 and every
entry in Appendices A-C. Each row must be one of:

- **PASS**: include source file/version, reviewed lines or declaration, method,
  and evidence;
- **FAIL**: include the first mismatching input/state or semantic difference,
  affected theorem(s), reachability, and remediation; or
- **OUT-OF-SCOPE ACCEPTED**: name the claim that must not be inferred from the
  artifact and identify the separate audit owner.

The final report must also contain:

- exact repository commit plus a diff of all uncommitted source changes;
- hashes/versions of rustc, Charon, Aeneas, Lean, mathlib, and relevant Rust
  dependencies;
- the regenerated LLBC and Lean diff, or a precise explanation for any drift;
- the complete `lake build HelioseleneCore.AxCheck` output;
- counts and names of all external `def` and `axiom` declarations;
- results of Rust tests and any differential test harnesses;
- a statement for each scope exclusion saying whether production relies on it;
  and
- a final list of unresolved assumptions. An empty unresolved list is allowed
  only if the curve-exponent and erased-property scope decisions are explicitly
  accepted or separately discharged.

"The axiom list is clean" is not sufficient evidence for a concrete external
model: Lean `def`s never appear in `#print axioms`.

## 4. Pinned baseline

### 4.1 Source and tools

| Component | Audited baseline |
|---|---|
| monero-oxide | base commit `6313959f906fe754909754ac642134237dae42a9` plus the production inversion correction in task B |
| target | `x86_64-unknown-linux-gnu` |
| rustc | `nightly-2026-06-01` |
| Charon | `0.1.218` |
| Aeneas | `nightly-2026.07.06-45061fa` |
| Lean | `v4.30.0-rc2` |
| crypto-bigint | `0.5.5` |
| subtle | `2.6.1` |
| ff | `0.13.1` |
| group | `0.13.0` |
| dalek-ff-group | `0.5.0` for the proof-relevant `FieldElement` boundary |
| rand_core | `0.6.4` |
| zeroize | `1.8.2` |

Verify these from the actual binaries, `Cargo.lock`, `lean-toolchain`,
`lake-manifest.json`, and the `.llbc` options block. Do not infer versions from
this table alone.

### 4.2 Content hashes at task creation

These hashes pin the uncommitted production correction and generated/model
files independently of Git metadata:

| Artifact | SHA-256 |
|---|---|
| `src/field/verified/invert.rs` | `1165d521cafaae87905863c82019895d5e97974de3d629241918abdd0e5fdd7f` |
| `aeneas/helioselene-aeneas.patch` | `c7da6ec037b9ad171bb47f3ac5ea9c9572af0d693ed5d86239c067385b7942ec` |
| `HelioseleneCore/Types.lean` | `404e69e813091b2ae90b42deaffa6a8bf77297ba073ba7798a6749f2abf65df2` |
| `HelioseleneCore/Funs.lean` | `20e4974e2dee9da77f805bde0885eb3d89153d371d384d61e3a8f8bb50cbd4cf` |
| `HelioseleneCore/TypesExternal.lean` | `7221f580c41f738e98bf5b989c9facb397b979521ec2419cfccc5caa8eb0dd0a` |
| `HelioseleneCore/FunsExternal.lean` | `832100acfff33287d706aca70e63b270c9dec493f7358daff33658c8356706e0` |
| aggregate of sorted `HelioseleneCore/Spec/*.lean` hashes | `191ab8c7006ecaa5067cf485658399242edf6cf64132cc377899bcba7bf4ea0a` |

Recompute hashes before review. A difference is not automatically a failure,
but the auditor must inspect and re-baseline it before relying on this task.
The LLBC is intentionally regenerated rather than pinned in this repository.
The aggregate proof hash above was computed from the repository root with:

```sh
find crypto/helioselene/aeneas/HelioseleneCore/Spec -type f -name '*.lean' -print0 \
  | sort -z | xargs -0 sha256sum | sha256sum
```

## 5. Task A: reproduce the translation and proof artifact

### A.1 Build configuration

Confirm the fifth-run Charon command in README section 3 exactly records:

- roots `field::verified`, `point::selene`, and `point::helios`;
- exclusion of `field::verified::pow`;
- the nine current opacity patterns;
- `--preset aeneas` and `--hide-marker-traits`;
- Cargo `--no-default-features --release`;
- target `x86_64-unknown-linux-gnu`; and
- Aeneas `-backend lean -split-files -gen-lib-entry`.

Inspect the serialized option record in the regenerated LLBC. A command line
copied from documentation is not proof that those options produced the checked
artifact.

### A.2 Reproduction

1. Copy current `crypto/helioselene` to a scratch directory.
2. Apply `helioselene-aeneas.patch` and confirm the resulting diff contains
   exactly task C.
3. Run `cargo test --release` in the patched copy; expect 11 library tests.
4. Run the pinned Charon and Aeneas commands.
5. Compare regenerated `Types.lean` and `Funs.lean` byte-for-byte.
6. Compare generated external templates by name and type against the checked-in
   concrete external files.
7. Build the Lean package with the pinned Lean/Lake dependencies.

**Acceptance A:** no unexplained declaration, signature, source-span, option,
or generated-body drift. If tool nondeterminism changes formatting/order only,
record a semantic diff demonstrating that fact.

## 6. Task B: audit the production inversion correction

This is the only proof-driven semantic change in production Rust. It is not a
translation-only rewrite.

### B.1 Change to review

In `src/field/verified/invert.rs`, the old high-half update added the top bit of
`2p` with a final bitwise OR. The corrected code:

- includes `(MODULUS_XOR_TWO_MODULUS[l] & add_two_modulus)` in every high limb;
- combines it with the `p` limb selected by `add_one_modulus`;
- carries through `add_with_bounded_overflow` for all four limbs; and
- removes the final top-limb OR.

### B.2 Required checks

- Prove by a four-mask truth table that the selected addend is exactly `0`,
  `p`, or `2p` and that impossible mask combinations are unreachable.
- Check the low- and high-half loops together implement wrapping 256-bit
  addition, including when bit 255 is already set.
- Confirm final overflow is intentionally discarded and no carry is dropped
  between limbs 1 and 2.
- Reproduce the former sharp failure at the first state beyond the old
  `UVWindow` boundary and show the corrected code matches exact arithmetic.
- Compare regenerated `step_loop4` and `step` to the corrected Rust source.
- Review branch-freeness and compiled code separately from the Lean value proof.
- Run inversion edge/random tests and all crate tests.

**Failure impact:** `invert_ok`, the Rust `Field` inversion/division
interpretation, and every production path using inversion become untrusted.

**Acceptance B:** exact value equivalence to wrapping addition for every mask
and every 256-bit state, faithful regeneration, and no newly introduced
secret-dependent branch.

## 7. Task C: audit every translation-only Rust change

These changes exist only in the scratch translation input. Production Rust is
the source of truth, so each row is an explicit human equivalence obligation.

| ID | File/change | Proposition to audit |
|---|---|---|
| C.1 | `Cargo.toml`: standalone `[workspace]` | Build metadata only; no source semantics |
| C.2 | `Cargo.toml`: absolute `ec-divisors` path | Optional dependency remains disabled under `--no-default-features`; path is machine-specific only |
| C.3 | `invert.rs`: `Word::from(borrow1 | borrow2)` -> bitwise OR of two converted words | Equal for all four Boolean inputs; evaluation has no side effects |
| C.4 | `verified/mod.rs`: analogous carry rewrite | Same four-case equality; no changed overflow or timing branch |
| C.5 | `from_repr::reduced`: iterator/`unwrap_or` -> indexed limb loop | Identical little-endian `(a_limb,b_limb)` sequence, loop count, carry fold, and panic behavior |
| C.6 | `sqrt.rs`: public exponent bitvec chain -> explicit indices `124..0` with a copied limb array | Exact original bit sequence after `take(253).rev().skip(128)`; 64-bit target assumption explicit; no secret-dependent branch |
| C.7 | `sqrt.rs`/`point.rs`: shift literals retyped to `u32` | Identical shift values 1, 3, and 7; no width/overflow edge |
| C.8 | `point.rs`: local `point` -> `candidate_point` | Pure alpha-renaming of both uses |
| C.9 | scalar ladder: reversed mutable bitvec -> canonical byte indices 255..0 | Both scalar `to_le_bits()` implementations are exactly views of canonical `[u8;32]::to_repr`; bit order and value identical |
| C.10 | scalar ladder: `clear_scalar_bit` and final byte-array zeroize | Same consumed-bit values/cleanup at the functional level; by-value array does not alter results |
| C.11 | scalar ladder: scoped immutable table and copied candidates | All 16 coordinates and assignment order identical because points are `Copy` |
| C.12 | scalar ladder: four doubles and 15 selections unrolled | Same counts, indices, order, full scan, and source-level constant-time structure |
| C.13 | scalar ladder: `res += term` -> `res = res + term` | Exact body of the point `AddAssign` implementation |

For C.6 and C.9-C.12, removal of iterator plumbing also removes some
`black_box`-based optimization barriers. Treat value equivalence and
constant-time/codegen equivalence as separate decisions.

**Acceptance C:** a reviewer signs every row with before/after source lines and
either a total semantic argument or exhaustive finite truth table where
appropriate. Passing tests alone is insufficient.

## 8. Task D: audit generated-code correspondence

Charon and Aeneas are unverified research translators. Review source-span
comments and `MAPPING.md` for every proof-relevant generated declaration.

### D.1 Field call graph

Review Rust against generated Lean for:

- `red1`, add, double, sub, neg, is_zero, and is_odd;
- `from_repr`/`reduced` and `to_repr`;
- `red256`, `red512`, mul, and square;
- inversion helpers, all five generated step loops, the 510-step driver, and
  final validity flag; and
- translated `sqrt`, its table construction, addition chain, window loop, root
  normalization, and self-check.

For every total handwritten wrapper used to define `HField` operations, follow
the corresponding `*_ok` theorem to the exact generated `Result` function and
confirm no default value or unproved failure-elimination branch was inserted.

### D.2 Selene call graph

Review constants and generated identity/add/double/neg/sub, equality tests,
conditional select, curve equation, generator, recovery/construction, and all
functions imported by the Selene group proof. Follow the choice-extracted
`idP`/`addP`/`doubleP`/`negP`/`subP` wrappers through their `*_ok` equations;
the quotient operations must remain propositionally tied to generated outputs.

### D.3 Helios call graph

Perform the same review for `point.helios.*`. Do not treat coordinate
arithmetic as reviewed here; its foreign value models are task I.

### D.4 Scalar call graph

Review both concrete `mul`, `mul_loop`, and `mul_loop.body` pairs,
`point.clear_scalar_bit`, table construction, all 256 iterations, cleanup, and
owned/shared `Mul`/`MulAssign` wrappers. Confirm proof-only folds in
`ScalarMulLaws.lean` unfold to generated blocks rather than replacing them.
Then inspect `generated_mul_exists -> mulP -> classSmul -> SMul` for each curve:
`Classical.choice` may only name the already-proved successful on-curve output,
`mulP_generated` must pin that choice to the exact `.ok` result, and no default
point or failure-erasing fallback may occur.

### D.5 Aeneas semantic conventions

Audit the interpretation used by all generated code:

- `Result.ok/fail/div` as return/panic-or-abort/divergence;
- release-MIR wrapping arithmetic versus Aeneas machine operations;
- array indexing/update failure behavior;
- `partial_fixpoint` loops and the meaning of a proved `.ok` postcondition;
- mutable-reference backward functions and struct/newtype flattening; and
- trait records, hidden marker traits, and selected impl resolution.

**Acceptance D:** complete sign-off for every proof-relevant generated
declaration and no unexplained mismatch between Rust evaluation order,
failure behavior, wrapping behavior, or returned value and generated Lean.

## 9. Task E: audit all six external type models

| ID | Lean model | Required human check |
|---|---|---|
| E.1 | `subtle.Choice := Bool` | Rust `Choice` values are restricted to 0/1 at every modeled boundary; value semantics only, not volatile/timing behavior |
| E.2 | `crypto_bigint.uint.Uint LIMBS := Array U64 LIMBS` | Proof target is the 64-bit little-endian limb representation; lengths and limb order match crypto-bigint 0.5.5 |
| E.3 | `subtle.CtOption T := T × Bool` | Payload/flag and combinator evaluation order match subtle 2.6.1; invalid payload remains observable only where Rust would evaluate it |
| E.4 | `crypto_bigint.ct_choice.CtChoice := Bool` | Value-level mask choice matches the crate; timing/layout erased |
| E.5 | `dalek_ff_group.field.FieldElement := ZMod (2^255-19)` | This is an idealized value type, not a translation of the Rust Montgomery representation; audit task I in full |
| E.6 | `rand_core.error.Error := {code : U32 // code != 0}` | Value/error-code contract is adequate at every generated use; layout and platform error behavior are not claimed |

Also record that generated `field.HelioseleneField` is a reducible alias for
raw `Uint 4`, not a distinct Rust newtype. The reduced carrier exists only in
the handwritten `HField` subtype.

**Acceptance E:** all six models match required value semantics and every
erased representation/property is listed as a non-claim.

## 10. Task F: audit all 92 concrete external function models

Appendix B is the mandatory declaration checklist. For each declaration:

1. locate the exact Rust body in the pinned crate version;
2. compare success, failure, value, argument order, mutability/backward update,
   wrapping, and endianness;
3. identify every generated call site and whether it is proof-relevant;
4. run edge and differential tests where the domain is nontrivial; and
5. record any intentional divergence.

Highest-risk items are `Uint::sbb`, `Limb::mac`, `mul_wide`, `square_wide`,
canonical byte conversion, `const_rem`, `CtOption` combinators,
`conditional_select`, `usize::ct_eq`, and all 28 dalek value models.

Known deliberate divergence to verify as unreachable: modeled
`shl_vartime`/`shr_vartime` fail for shifts at least `64*LIMBS`, while
crypto-bigint returns zero. Every current proof-relevant call shifts by one.

Pure zeroization models only return zeroed values. They do not model physical
writes or optimizer guarantees; those are task L.

**Acceptance F:** 92 PASS rows, or an explicit theorem impact analysis for
every non-PASS row. Model-helper declarations count: they are part of the
trusted implementation of the Rust-facing models.

## 11. Task G: audit the reducedness boundary

Lean field laws are proved on:

```text
HField = {u : Uint4 // u.toNat < p}
```

Rust's inner `U256` is `pub(crate)`, and generated Lean erases the newtype. A
human must establish that every production construction consumed as a field
value is reduced.

Audit all of the following:

- translated verified arithmetic and reductions preserve `< p`;
- `from_repr` accepts exactly canonical values and invalid `CtOption` payloads
  cannot escape as valid values;
- raw curve/sqrt constants constructed from hex are `< p` and equal their
  intended values;
- `TWO_INV`, multiplicative generator, roots of unity, `DELTA`, `S`,
  `NUM_BITS`, and `CAPACITY` are correct and reduced;
- `from_u256`/`const_rem` reduce every input as claimed;
- `From<u8/u16/u32/u64>` values are reduced;
- `random`, wide reduction, and any untranslated or unspecified constructor
  used in production preserves reducedness; and
- no crate-internal unsafe/raw constructor bypasses these paths.

This review must use a complete constructor/call-site search, not only the list
known when the first ledger was written.

**Failure impact:** raw equality, canonical encoding, all `HField`-to-Rust
interpretations, and any theorem applied to the non-reduced value are invalid.

**Acceptance G:** complete production constructor inventory with a `< p` proof
or test argument for each entry.

## 12. Task H: audit every axiom and sorry boundary

Appendix A gives the exact explicit inventory. Classify each item into one of
the following trust classes and verify that classification mechanically.

### H.1 Standard Lean foundations

Headline proofs use `propext`, `Classical.choice`, and `Quot.sound`. Acceptance
of the Lean kernel and these foundations is an explicit audit assumption.

### H.2 Thirty-nine existence-only external axioms

These typecheck opaque trait evidence or out-of-scope operations. Their types
are inhabited, so they are conservative extensions, but that fact does not
permit a headline theorem to depend on their behavior. Confirm all 39 names
from Appendix A and verify none enters any headline proof cone.

### H.3 Nine generated string-length axioms

The following generated constants use `Aeneas.Std.toStr` with a
`by decide +native` length side condition:

1. `field.MODULUS._native.decide.ax_1`
2. `field.verified.MODULUS_255_DISTANCE._native.decide.ax_1`
3. `field.verified.red.TWO_MODULUS_255_DISTANCE._native.decide.ax_1`
4. `field.verified.invert.invert.step.MODULUS_XOR_TWO_MODULUS._native.decide.ax_1`
5. `field.verified.sqrt.MODULUS_PLUS_ONE_DIV_FOUR._native.decide.ax_1`
6. `point.selene.B._native.decide.ax_1`
7. `point.selene.G_Y._native.decide.ax_1`
8. `point.helios.B._native.decide.ax_1`
9. `point.helios.G_Y._native.decide.ax_1`

Confirm each axiom states only the trivial string-length bound. Independently
confirm the parsed constant value through the kernel proofs in `Spec`.

### H.4 Three generated Debug bodies

The generated Debug methods for `HelioseleneField`, `SelenePoint`, and
`HeliosPoint` contain analogous compiler-generated string-length facts. Their
exact additional axiom surface is:

- `Aeneas.Std.core.fmt.Formatter` (the opaque Aeneas formatter type);
- `field.HelioseleneField.Insts.CoreFmtDebug.fmt._native.decide.ax_1`;
- `point.selene.SelenePoint.Insts.CoreFmtDebug.fmt._native.decide.ax_1`;
- `point.selene.SelenePoint.Insts.CoreFmtDebug.fmt._native.decide.ax_2`;
- `point.selene.SelenePoint.Insts.CoreFmtDebug.fmt._native.decide.ax_3`;
- `point.selene.SelenePoint.Insts.CoreFmtDebug.fmt._native.decide.ax_4`; and
- `point.helios.HeliosPoint.Insts.CoreFmtDebug.fmt._native.decide.ax_1`.

The Helios Debug body reuses the generated Selene-named `ax_2` through `ax_4`
facts for shared macro-emitted formatting strings. Recheck this exact naming
after regeneration. The two external Debug function axioms reached by these
bodies are already listed in Appendix A. All of this surface must remain
outside proof cones. The three bodies are:

- `field.HelioseleneField.Insts.CoreFmtDebug.fmt`
- `point.selene.SelenePoint.Insts.CoreFmtDebug.fmt`
- `point.helios.HeliosPoint.Insts.CoreFmtDebug.fmt`

### H.5 Twenty-five quarantined validation axioms

Each theorem listed in Appendix C uses one `native_decide` axiom. The three
Validation modules are imported by nothing in the library/proof tree. Confirm
the quarantine from imports and `#print axioms`; treat validation as compiler-
trusted test evidence, never as a kernel proof premise.

### H.6 Three upstream Aeneas Standard Library sorries

The pinned Aeneas Lean library contains:

- `core.slice.Slice.get_unchecked` (`Aeneas/Std/Slice.lean:363`);
- `core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec`
  (`Aeneas/Std/Slice.lean:586`); and
- `core.str.iter.IteratorChars.collect`
  (`Aeneas/Std/StringIter.lean:13`).

The full build warns about these. Confirm no headline proof depends on their
`sorryAx`. If a regenerated call graph begins using one, it becomes a blocking
assumption.

### H.7 Exponent certificates are not axioms

Confirm there is no instance of `SeleneExponentCertificate` or
`HeliosExponentCertificate`. `moduleOfExponent` must consume an ordinary proof
argument. Do not report the conditional theorem as an unconditional module
instance.

**Acceptance H:** exact counts (6 type defs, 92 function defs, 39 explicit
axioms), expected compiler-generated axioms only, no `sorryAx` or existence-
only axiom in a headline cone, and no exponent certificate in scope.

## 13. Task I: audit the idealized Helios coordinate field

This is the largest semantic assumption in the Helios group and Helios scalar
proofs.

The Lean model defines:

```text
dalek_ff_group::FieldElement := ZMod (2^255 - 19)
```

The Rust fidelity target is dalek-ff-group 0.5.0's own `FieldElement` wrapper
over crypto-bigint 0.5.5 constant-modulus Montgomery `Residue`. It is not
curve25519-dalek's field backend, and no fiat-crypto proof is on this path.

Required review:

- inspect every one of the 28 concrete dalek declarations in Appendix B;
- verify Montgomery `new`, add/sub/mul/neg, assign/shared variants, retrieve,
  equality, conditional selection, zero/one, double/square/is_zero,
  `From<u64>`, `from_u256`, canonical `to_repr`, and zeroize;
- establish `ct_eq` is true exactly for equal field values after canonical
  retrieval;
- establish `from_u256` reduces all 256-bit inputs, including inputs `>= q`;
- establish `to_repr` is the canonical little-endian encoding consumed by the
  Selene scalar ladder;
- check conditional-select argument order against subtle; and
- build a differential Rust harness over edge values and random values against
  independent big-integer arithmetic. Cover each operation, not only composed
  point tests.

The existing `ValidationHelios.lean` cannot detect a mismatch here because it
executes the ideal field by definition.

**Failure impact:** every Helios group/ladder theorem describes a different
coordinate computation from Rust; Selene scalar interpretation may also be
wrong for `to_repr`/zeroize discrepancies.

**Acceptance I:** source-level sign-off for all 28 definitions plus passing
differential tests that exercise reduction and canonical representation edges.

## 14. Task J: audit mathematical design premises not supplied by Lean

### J.1 Curve exponents/cardinalities

The repository does not prove:

- `SeleneExponent : forall P, (2^255 - 19) • P = 0`; or
- `HeliosExponent : forall P, p • P = 0`.

Audit the original curve-search/order computation and independently reproduce
the claimed cycle:

```text
#Selene(F_p) = 2^255 - 19
#Helios(F_(2^255-19)) = p
```

Alternatively provide a direct all-points exponent proof. Checking only the
generator is insufficient unless cyclicity/cardinality arguments cover every
point.

These premises affect scalar addition/multiplication laws and unconditional
`Module` instances. They do not affect the proved ladder equality with natural
repeated addition or `DistribSMul`.

### J.2 Handwritten specification correspondence

Review the theorem statements and abstractions themselves against the intended
Rust/protocol objects. In particular, confirm:

- `p` is the exact helioselene scalar/base modulus used by Rust and
  `q = 2^255-19` is the exact dalek field modulus;
- Selene and Helios `B`, `G_X`, and `G_Y` values are traced through the
  generated parsers to the exact source literals;
- each handwritten `W` is precisely `y^2 = x^3 - 3x + B` over the intended
  field, with no coefficient/sign/curve swap;
- the projective equation and `Theta` map use the coordinate convention Rust
  actually computes (`x/z`, `y/z`, and the intended `z = 0` identity), rather
  than a Jacobian or differently scaled convention;
- projective equivalence is exactly the relation needed to identify all valid
  Rust representatives and no invalid representative is admitted;
- descended zero/add/neg/sub/double and generator theorems refer to the exact
  generated wrappers;
- Selene's scalar value is the canonical dalek value modulo `q`, while Helios'
  scalar value is the reduced `HField` value modulo `p`; and
- `nsmul`, `DistribSMul`, and conditional `Module` theorem statements match the
  API/protocol claim downstream users intend to rely on.

A mismatch here is a specification bug even if every proof and translation
step is internally correct.

### J.3 Kernel-closed facts

Primality, constants, nonsingularity, nonresidue facts, no 2-torsion, RCB case
certificates, generator-on-curve, and the repaired inversion/sqrt obligations
are kernel-checked. Human review should verify source/generated correspondence
and certificate reproducibility, not treat the Python generators, msieve, or
published factorization as logical axioms: Lean checks the certificates.

**Acceptance J:** the handwritten specifications match the intended curves and
Rust value conventions, and both exponent propositions are either independently
discharged or marked as accepted external design premises in every downstream
claim of unconditional field-scalar module laws.

## 15. Task K: audit proof domains and scope exclusions

For each row, determine production reachability and ensure no documentation or
downstream use claims coverage beyond the theorem.

| ID | Boundary | Current status |
|---|---|---|
| K.1 | Raw/non-reduced `HelioseleneField` | Field theorems apply to `HField`, not arbitrary `Uint4`; task G connects production constructors |
| K.2 | Raw/off-curve points | Group and ladder theorems start from `SPt`/`HPt`; Rust point types do not enforce this invariant |
| K.3 | `verified::pow` | Excluded from translation; Lean `^` is transported mathlib behavior, not this Rust function; rely on separate Dafny/manual review |
| K.4 | `HelioseleneField::random` and wide/random paths | Generated where reachable but no headline Spec contract covering distribution/security; audit separately if used |
| K.5 | `HelioseleneField` `Sum`/`Product` | Opaque existence-only axioms; no headline proof behavior |
| K.6 | `HelioseleneField::sqrt_ratio` | Opaque existence-only axiom; no headline proof behavior |
| K.7 | point `Sum`, `Group::random`, point `Zeroize` | Opaque for both curves; explicit axioms outside proof cones |
| K.8 | Selene encoding | Components translated/proved, but no complete class-level encode/decode round-trip and canonicality theorem |
| K.9 | Helios encoding | Generated functions cross opaque dalek `sqrt`, `invert`, `from_repr`, and `is_odd`; no behavioral theorem |
| K.10 | `PrimeFieldBits::to_le_bits` | Not translated; hunk-8 equivalence relies on source-level equality with canonical `to_repr` |
| K.11 | `ciphersuite.rs`, hash-to-curve, domain separation | Outside translation roots and all Lean theorems |
| K.12 | 32-bit target | Not modeled: `Limb := U64`, four limbs, and hunk-5 `/64` indexing are baked in |
| K.13 | Debug build | Not modeled: translation uses release MIR; debug assertions and panic-on-overflow behavior differ |
| K.14 | Default/other Cargo features | Not modeled: translation uses `--no-default-features` |
| K.15 | Layout/FFI/serialization of in-memory structs | Erased by newtype/struct modeling; only explicit byte functions can have value contracts |

**Acceptance K:** every production use is either within a proved/refined domain
or assigned to a separate audit with no Lean-backed claim attached.

## 16. Task L: audit properties erased by the functional model

### L.1 Constant-time and side channels

Lean proves values, bounds, and termination, not timing. Audit source and
compiled artifacts for:

- secret-dependent branches and memory addresses;
- preservation of subtle `Choice`/`conditional_select` behavior;
- `black_box`/volatile barriers removed by translation-only rewrites;
- fixed scalar table scans and loop counts after optimization;
- inversion, sqrt, and scalar-multiplication timing; and
- target-specific compiler transformations.

Use suitable compiled-code inspection and statistical/dynamic tools. A proof
that `conditional_select` returns the correct value is not constant-time
evidence.

### L.2 Zeroization

Lean's explicit zeroize models replace values with zero. Audit whether compiled
Rust actually overwrites all intended scalar/bit/point temporaries, whether
writes survive optimization, and whether copies remain. Point zeroization is
opaque and outside the proof entirely.

### L.3 Compiler and platform

LLVM optimization, code generation, ABI/layout, CPU behavior, faults, and the
soundness of rustc itself are outside the theorem. Record the deployment
platform/toolchain assurance decision.

**Acceptance L:** separate constant-time/zeroization/codegen report, or an
explicit risk acceptance that states these properties are not Lean-verified.

## 17. Task M: final mechanical checks and acceptance gate

Run from `crypto/helioselene/aeneas` unless noted:

```sh
lake env lean HelioseleneCore/Spec/ScalarMulLaws.lean
lake build HelioseleneCore.AxCheck
lake build
rg -c '^def( |$)' HelioseleneCore/FunsExternal.lean
rg -c '^axiom( |$)' HelioseleneCore/FunsExternal.lean
rg -c '^def ' HelioseleneCore/TypesExternal.lean
```

Expected declaration counts are 92, 39, and 6. The full build currently emits
the three upstream Aeneas `sorry` warnings from H.6; no project-local Spec
declaration may use `sorry`.

Review all `#print axioms` output at the bottoms of `Spec/Field.lean`, both
`Spec/*/GroupLaw.lean` files, `Spec/ScalarMulLaws.lean`, and `AxCheck.lean`.
The key expected cones are:

| Theorem | Expected non-foundational named axioms |
|---|---|
| `instFieldHField` | field `MODULUS`, `MODULUS_255_DISTANCE`, `TWO_MODULUS_255_DISTANCE`, `MODULUS_XOR_TWO_MODULUS` string-length facts |
| `φRing` | field `MODULUS`, `MODULUS_255_DISTANCE`, `TWO_MODULUS_255_DISTANCE` string-length facts |
| `p_prime`, `q_prime`, cardinality lemmas | none beyond standard Lean foundations |
| `Selene.ΘAddEquiv` | field `MODULUS`, `MODULUS_255_DISTANCE`, `TWO_MODULUS_255_DISTANCE`, and Selene `B` string-length facts |
| `Helios.ΘAddEquiv` | Helios `B` string-length fact |
| `SeleneLadder.mul_spec` and exact-result action theorem | same set as `Selene.ΘAddEquiv` |
| `HeliosLadder.mul_spec` and exact-result action theorem | Helios `B` string-length fact |
| `SeleneAction.moduleOfExponent` | same set as the Selene ladder; exponent is a theorem argument |
| `HeliosAction.moduleOfExponent` | field inversion set plus Helios `B`; exponent is a theorem argument |

Any `sorryAx`, any Appendix-A existence axiom, any Validation axiom, or any
exponent certificate in these cones is a blocking failure.

### Final acceptance gate

All of the following must be checked:

- [ ] A: artifact reproduced and generated drift explained
- [ ] B: production inversion correction audited
- [ ] C: all 13 translation-only equivalence items audited
- [ ] D: all proof-relevant generated declarations matched to Rust
- [ ] E: all 6 type models audited
- [ ] F: all 92 concrete function models audited
- [ ] G: all production field constructors preserve reducedness
- [ ] H: complete axiom/sorry inventory and clean headline cones
- [ ] I: all 28 dalek ideal-field models audited and differentially tested
- [ ] J: curve exponent premises proved or explicitly accepted as external
- [ ] K: all scope/domain exclusions assigned and accurately communicated
- [ ] L: timing, zeroization, and codegen separately reviewed or accepted
- [ ] M: Rust tests, Lean builds, validation, and negative controls pass

The human audit may call the Lean-backed implementation claims closed only
after every box is checked and every non-PASS item is reflected in the final
claim language.

## Appendix A: exact 39 existence-only axioms

The source of truth is `HelioseleneCore/FunsExternal.lean`. Check both count and
types against the newly generated external template.

### A.1 crypto-bigint Debug (1)

- [ ] `crypto_bigint.uint.Uint.Insts.CoreFmtDebug.fmt`

### A.2 dalek `FieldElement` residual surface (23)

- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreCloneClone.clone`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreCmpPartialEqFieldElement.eq`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreDefaultDefault.default`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreFmtDebug.fmt`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreIterTraitsAccumProductSharedAFieldElement.product`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreIterTraitsAccumProductFieldElement.product`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreIterTraitsAccumSumSharedAFieldElement.sum`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreIterTraitsAccumSumFieldElement.sum`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.sqrt_ratio`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.sqrt`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.invert`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.random`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.is_odd`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.from_repr`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.DELTA`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.ROOT_OF_UNITY_INV`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.ROOT_OF_UNITY`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.S`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.MULTIPLICATIVE_GENERATOR`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.TWO_INV`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.CAPACITY`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.NUM_BITS`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.MODULUS`

### A.3 Selene point opaque items (4)

- [ ] `point.selene.SelenePoint.Insts.ZeroizeZeroize.zeroize`
- [ ] `point.selene.SelenePoint.Insts.CoreIterTraitsAccumSumSharedASelenePoint.sum`
- [ ] `point.selene.SelenePoint.Insts.CoreIterTraitsAccumSumSelenePoint.sum`
- [ ] `point.selene.SelenePoint.Insts.GroupGroupFieldElementArrayU832.random`

### A.4 remaining crypto-bigint Uint items (2)

- [ ] `crypto_bigint.uint.Uint.Insts.CoreCmpPartialEqUint.eq`
- [ ] `crypto_bigint.uint.Uint.Insts.CoreConvertFromU64.from`

### A.5 helioselene scalar-field opaque items (5)

- [ ] `field.HelioseleneField.Insts.CoreIterTraitsAccumSumHelioseleneField.sum`
- [ ] `field.HelioseleneField.Insts.CoreIterTraitsAccumSumSharedAHelioseleneField.sum`
- [ ] `field.HelioseleneField.Insts.CoreIterTraitsAccumProductHelioseleneField.product`
- [ ] `field.HelioseleneField.Insts.CoreIterTraitsAccumProductSharedAHelioseleneField.product`
- [ ] `field.HelioseleneField.Insts.FfField.sqrt_ratio`

### A.6 Helios point opaque items (4)

- [ ] `point.helios.HeliosPoint.Insts.ZeroizeZeroize.zeroize`
- [ ] `point.helios.HeliosPoint.Insts.CoreIterTraitsAccumSumSharedAHeliosPoint.sum`
- [ ] `point.helios.HeliosPoint.Insts.CoreIterTraitsAccumSumHeliosPoint.sum`
- [ ] `point.helios.HeliosPoint.Insts.GroupGroupHelioseleneFieldArrayU832.random`

For every item, record why it is opaque, whether production reaches it, and the
`#print axioms` evidence that it is absent from each headline theorem.

## Appendix B: exact 92 concrete external function definitions

These are logical definitions, not axioms. Their Rust fidelity is therefore a
human assumption even when every axiom cone is clean.

### B.1 model implementation helpers (8)

- [ ] `limbOfNat`
- [ ] `byteOfNat`
- [ ] `limbAllOnes`
- [ ] `hexDigit?`
- [ ] `parseBeHex?`
- [ ] `leBytesToNat`
- [ ] `crypto_bigint.uint.Uint.toNat`
- [ ] `crypto_bigint.uint.Uint.ofNat`

### B.2 crypto-bigint limb models (15)

- [ ] `crypto_bigint.limb.add.Limb.wrapping_add`
- [ ] `crypto_bigint.limb.Limb.Insts.CoreOpsBitBitAndLimbLimb.bitand`
- [ ] `crypto_bigint.limb.Limb.Insts.CoreOpsBitNotLimb.not`
- [ ] `crypto_bigint.limb.Limb.Insts.CoreOpsBitBitOrLimbLimb.bitor`
- [ ] `crypto_bigint.limb.Limb.Insts.CoreOpsBitBitXorLimbLimb.bitxor`
- [ ] `crypto_bigint.limb.Limb.Insts.SubtleConstantTimeEq.ct_eq`
- [ ] `crypto_bigint.limb.mul.Limb.mac`
- [ ] `crypto_bigint.limb.neg.Limb.wrapping_neg`
- [ ] `crypto_bigint.limb.Limb.Insts.CoreOpsBitShlUsizeLimb.shl`
- [ ] `crypto_bigint.limb.Limb.Insts.CoreOpsBitShrUsizeLimb.shr`
- [ ] `crypto_bigint.limb.Limb.Insts.CoreCloneClone.clone`
- [ ] `crypto_bigint.limb.Limb.ZERO`
- [ ] `crypto_bigint.limb.Limb.ONE`
- [ ] `crypto_bigint.limb.Limb.MAX`
- [ ] `crypto_bigint.limb.Limb.BITS`

### B.3 crypto-bigint Uint models from the original field scope (16)

- [ ] `crypto_bigint.uint.add.Uint.wrapping_add`
- [ ] `crypto_bigint.uint.encoding.Uint.from_be_hex`
- [ ] `crypto_bigint.uint.encoding.Uint.from_le_slice`
- [ ] `crypto_bigint.uint.Uint4.Insts.Crypto_bigintTraitsEncodingArrayU832.to_le_bytes`
- [ ] `crypto_bigint.uint.mul.Uint.mul_wide`
- [ ] `crypto_bigint.uint.mul.Uint.square_wide`
- [ ] `crypto_bigint.uint.shl.Uint.shl_vartime`
- [ ] `crypto_bigint.uint.shr.Uint.shr_vartime`
- [ ] `crypto_bigint.uint.sub.Uint.sbb`
- [ ] `crypto_bigint.uint.sub.Uint.wrapping_sub`
- [ ] `crypto_bigint.uint.Uint.ZERO`
- [ ] `crypto_bigint.uint.Uint.ONE`
- [ ] `crypto_bigint.uint.Uint.LIMBS_1`
- [ ] `crypto_bigint.uint.Uint.as_limbs`
- [ ] `crypto_bigint.uint.Uint.as_limbs_mut`
- [ ] `crypto_bigint.uint.Uint.Insts.SubtleConditionallySelectable.conditional_select`

### B.4 subtle models from the original field scope (3)

- [ ] `subtle.Choice.Insts.CoreOpsBitNotChoice.not`
- [ ] `subtle.Choice.Insts.CoreConvertFromU8.from`
- [ ] `subtle.CtOption.new`

### B.5 widened crypto-bigint Uint models (4)

- [ ] `crypto_bigint.uint.Uint.Insts.SubtleConstantTimeEq.ct_eq`
- [ ] `crypto_bigint.uint.div.Uint.const_rem`
- [ ] `crypto_bigint.uint.from.Uint.from_u8`
- [ ] `crypto_bigint.uint.Uint.Insts.CoreDefaultDefault.default`

### B.6 concrete dalek `FieldElement` value models (28)

- [ ] `dalek_ff_group.field.FieldElement.toZMod`
- [ ] `dalek_ff_group.field.FieldElement.ofZMod`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreCmpEq.assert_fields_are_eq`
- [ ] `dalek_ff_group.field.FieldElement.Insts.ZeroizeZeroize.zeroize`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreConvertFromU64.from`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithNegFieldElement.neg`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithMulAssignSharedAFieldElement.mul_assign`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithSubAssignSharedAFieldElement.sub_assign`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithAddAssignSharedAFieldElement.add_assign`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithMulSharedAFieldElementFieldElement.mul`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithSubSharedAFieldElementFieldElement.sub`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithAddSharedAFieldElementFieldElement.add`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithMulAssignFieldElement.mul_assign`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithSubAssignFieldElement.sub_assign`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithAddAssignFieldElement.add_assign`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithMulFieldElementFieldElement.mul`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithSubFieldElementFieldElement.sub`
- [ ] `dalek_ff_group.field.FieldElement.Insts.CoreOpsArithAddFieldElementFieldElement.add`
- [ ] `dalek_ff_group.field.FieldElement.Insts.SubtleConditionallySelectable.conditional_select`
- [ ] `dalek_ff_group.field.FieldElement.Insts.SubtleConstantTimeEq.ct_eq`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.double`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.square`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.ONE`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.ZERO`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfField.is_zero`
- [ ] `dalek_ff_group.field.FieldElement.Insts.FfPrimeFieldArrayU832.to_repr`
- [ ] `Shared0FieldElement.Insts.CoreOpsArithNegFieldElement.neg`
- [ ] `dalek_ff_group.field.FieldElement.from_u256`

### B.7 ff/subtle/CtOption/zeroize and marker models (18)

- [ ] `ff.Field.is_zero.default`
- [ ] `ff.Field.sqrt.default`
- [ ] `subtle.Choice.unwrap_u8`
- [ ] `Bool.Insts.CoreConvertFromChoice.from`
- [ ] `subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand`
- [ ] `subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor`
- [ ] `subtle.Choice.Insts.SubtleConstantTimeEq.ct_eq`
- [ ] `Usize.Insts.SubtleConstantTimeEq.ct_eq`
- [ ] `U8.Insts.SubtleConditionallySelectable.conditional_select`
- [ ] `subtle.ConditionallyNegatable.Blanket.conditional_negate`
- [ ] `core.option.Option.Insts.CoreConvertFromCtOption.from`
- [ ] `subtle.CtOption.map`
- [ ] `subtle.CtOption.and_then`
- [ ] `subtle.CtOption.Insts.SubtleConditionallySelectable.conditional_select`
- [ ] `zeroize.Zeroize.Blanket.zeroize`
- [ ] `Array.Insts.ZeroizeZeroize.zeroize`
- [ ] `point.selene.SelenePoint.Insts.CoreCmpEq.assert_fields_are_eq`
- [ ] `point.helios.HeliosPoint.Insts.CoreCmpEq.assert_fields_are_eq`

For the Rust-facing entries, the doc comment immediately above each definition
in `FunsExternal.lean` identifies the intended source body and modeled
semantics. Verify those comments too; a correct Lean definition paired with the
wrong Rust source/version is still a failed boundary.

## Appendix C: exact 25 quarantined validation theorems

Each declaration below carries one compiler-trusted `native_decide` axiom and
must remain outside all Spec imports and theorem cones.

### C.1 field validation (10)

- [ ] `validation_red256`
- [ ] `validation_red512`
- [ ] `validation_add`
- [ ] `validation_sub`
- [ ] `validation_mul`
- [ ] `validation_neg`
- [ ] `validation_double`
- [ ] `validation_square`
- [ ] `validation_invert`
- [ ] `validation_from_repr`

### C.2 Selene validation (8)

- [ ] `validationSelene_sqrt`
- [ ] `validationSelene_add`
- [ ] `validationSelene_double`
- [ ] `validationSelene_neg`
- [ ] `validationSelene_ct_eq`
- [ ] `validationSelene_from_xy`
- [ ] `validationSelene_adhoc`
- [ ] `validationSelene_negative_controls`

### C.3 Helios validation (7)

- [ ] `validationHelios_add`
- [ ] `validationHelios_double`
- [ ] `validationHelios_neg`
- [ ] `validationHelios_ct_eq`
- [ ] `validationHelios_from_xy`
- [ ] `validationHelios_adhoc`
- [ ] `validationHelios_negative_controls`

Record the vector provenance, independently recompute a sample from each
class, and verify every negative control actually corrupts the intended field
and is rejected by a non-vacuous checker.

## Appendix D: authoritative evidence map

Use these files as evidence, not as substitutes for performing the task:

| Boundary | Primary evidence |
|---|---|
| Tool versions/options/regeneration | `README.md` sections 3 and 6; regenerated LLBC options block |
| Production and translation Rust changes | `README.md` section 4; `helioselene-aeneas.patch`; production Git diff |
| Lean-to-Rust declaration map | `MAPPING.md`; generated source-span comments in `Types.lean`/`Funs.lean` |
| Field assumptions | `human_audit_assumptions.txt`; `Spec/Externals.lean` through `Spec/Field.lean` |
| Selene assumptions | `human_audit_assumptions_selene.txt`; `Spec/Selene/*` |
| Helios assumptions | `human_audit_assumptions_helios.txt`; `Spec/Helios/*` |
| Scalar assumptions and exact generated connection | both curve ledgers section V; `Spec/ScalarMul.lean`; `Spec/ScalarMulLaws.lean` |
| Explicit externals | `TypesExternal.lean`; `FunsExternal.lean` |
| Axiom cones | `AxCheck.lean`; bottom sections of `Field.lean`, both `GroupLaw.lean` files, and `ScalarMulLaws.lean` |
| Differential evidence | `Validation*.lean`; vector generators/data under `tools/` and `phase-b/` |
| Existing adversarial review | `human_audit_findings_15_agents.txt`; repository-level audit finding logs |

The final human report should link its PASS/FAIL evidence back to this task by
task and appendix ID so future source or toolchain changes can invalidate only
the affected approvals.
