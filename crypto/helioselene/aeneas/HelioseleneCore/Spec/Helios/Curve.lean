/- Kernel-checkable curve constants and number-theoretic facts for the Helios curve

     y^2 = x^3 - 3x + B   over   ZMod q,
     q = 2^255 - 19,
     B = 0x26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60,

   with generator (1, gY), gY = 0x611dffc62fe02c759e5ac10f40e009b8e3b147387068aaf810dbdf2d817c67ba.

   Helios is the sibling of Selene (`Spec/Selene/Curve.lean`, the template for this
   file) over the Curve25519 field prime. Unlike Selene, whose field elements are
   4-limb `Uint`s with a value map `ψ`, the translated Helios field type
   `dalek_ff_group.field.FieldElement` (TypesExternal.lean) IS `ZMod (2^255 - 19)`
   definitionally, so there is no limb layer here: the curve constants evaluate to
   `ok` of literal `ZMod` values.

   Contents (everything PROVED — no `sorry`, and no axioms/`native_decide` beyond
   the `<const>._native.decide.ax_1` string-length axioms already baked into the
   generated `Funs.lean` constants, inherited by the `_ok` constant-agreement
   lemmas as detailed at the end of this header):
   1. `Bcurve`/`gY` literals, `_lt_q` bounds, and agreement of the TRANSLATED constants
      `point.helios.B` / `point.helios.G_Y` / `point.helios.G_X` (and the full generator
      `point.helios.G`) with them: the hex strings are kernel-parsed via the same
      `toStr_val + decide` route as `MODULUS_ok` in `Spec/Externals.lean`, and
      `dalek_ff_group.field.FieldElement.from_u256` (concrete model
      `ok (.ofZMod u.toNat)`, FunsExternal.lean) reduces them into `Fq`;
   2. `generator_on_curve` : the generator satisfies the curve equation (ℕ- and ZMod-level);
   3. `B_nonresidue` : `B` is a quadratic non-residue mod `q` (kernel `powMod` computation of
      `B^((q-1)/2) ≡ -1` + mathlib's Euler criterion), with corollary `no_affine_x_zero`
      (no curve point has x = 0 — the soundness fact behind `is_identity`'s `x = 0` check);
   4. `delta_ne_zero` : the short-Weierstrass discriminant `-16(4·(-3)^3 + 27B^2)` is
      nonzero in `Fq` (plus the raw ℕ-level ingredients for the mathlib-facing file);
   5. `no_two_torsion` : no point of the curve has y = 0, via `cubic_no_root`: the cubic
      `X^3 - 3X + B` has no root in `Fq`. Certificate: a fuel-based kernel computation
      of `g = X^q mod (f, q)` in `(ZMod q)[X]/(f)` (`polyPowMod`, evaluated by `rfl` like
      `powMod` in `Spec/Helios/Prime25519.lean`), Fermat (`ZMod.pow_card`), and a concrete
      Bezout identity `u·f + v·(g - X) = 1` checked by a single `ring` call over ℕ.

   The numeric certificates were generated and cross-checked by
   `tools/gen_curve_helios.py` (the Helios port of `tools/gen_curve.py`).

   Depends only on `Spec/Externals.lean` (hence the generated model) and
   `Spec/Helios/Prime25519.lean` (the kernel Pratt certificate for `2^255 - 19`);
   a follow-up file connects these facts to mathlib's `WeierstrassCurve`.

   Exported lemmas that mention the generated hex-string constants (`B_ok`, `G_Y_ok`,
   `G_ok` and their primed variants) transitively inherit the
   `<const>._native.decide.ax_1` axioms baked into Funs.lean for `point.helios.B` and
   `point.helios.G_Y` (see README §5c.3; each asserts only that a hex string literal
   is at most `U32.max` bytes, and the parsed values are re-proved kernel-only here).
   The purely number-theoretic facts (`B_nonresidue`, `cubic_no_root`, `no_two_torsion`,
   `delta_ne_zero`, `generator_on_curve_zmod`, `q_prime'`) depend on no axioms beyond
   `propext`, `Classical.choice`, `Quot.sound`. -/
import HelioseleneCore.Spec.Externals
import HelioseleneCore.Spec.Helios.Prime25519

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

namespace Helios

open crypto_bigint.uint HelioseleneModel

/-! ## 0. The base field `Fq`

`dalek_ff_group.field.FieldElement` (TypesExternal.lean) is a plain — non-reducible —
`def` to `ZMod (2 ^ 255 - 19)`, so typeclass search does not see through it. We work in
the reducible spelling `Fq` and move between the two with the definitional coercions
`FieldElement.toZMod` / `FieldElement.ofZMod` from FunsExternal.lean. -/

/-- The Helios base-field prime `q = 2^255 - 19` (the Curve25519 field prime).
Reducible, so that `q`-spelled and `2 ^ 255 - 19`-spelled statements unify. -/
abbrev q : ℕ := 2 ^ 255 - 19

/-- The Helios base field, in the `ZMod (2 ^ 255 - 19)` spelling that
`dalek_ff_group.field.FieldElement` definitionally unfolds to. -/
abbrev Fq : Type := ZMod (2 ^ 255 - 19)

/-- Read a translated Helios field element as its `Fq` model value (the identity, by
definitional unfolding of `dalek_ff_group.field.FieldElement`). -/
abbrev asFq (a : dalek_ff_group.field.FieldElement) : Fq :=
  dalek_ff_group.field.FieldElement.toZMod a

@[simp] theorem toZMod_ofZMod (x : Fq) :
    (dalek_ff_group.field.FieldElement.ofZMod x).toZMod = x := rfl

@[simp] theorem ofZMod_toZMod (a : dalek_ff_group.field.FieldElement) :
    dalek_ff_group.field.FieldElement.ofZMod a.toZMod = a := rfl

theorem q_eq :
    q = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  norm_num

theorem q_pos : 0 < q := by norm_num
theorem one_lt_q : 1 < q := by norm_num
theorem two_lt_q : 2 < q := by norm_num
theorem three_lt_q : 3 < q := by norm_num
theorem q_lt : q < 2 ^ 256 := by norm_num

/-- `q` is prime, in the `2^255 - 19` spelling (kernel Pratt certificate,
`Spec/Helios/Prime25519.lean`). -/
theorem q_prime' : Nat.Prime q := by rw [q_eq]; exact _root_.q_prime

/-- The `Fact` instance in the spelling every `Fq` typeclass problem needs
(the literal spelling is `_root_.fact_q_prime`, Prime25519.lean). -/
instance fact_q_prime' : Fact (Nat.Prime (2 ^ 255 - 19)) := ⟨q_prime'⟩

instance fact_two_lt_q : Fact (2 < 2 ^ 255 - 19) := ⟨two_lt_q⟩

example : Field Fq := inferInstance

/-! ## 1. The curve constants as ℕ literals -/

/-- The Helios curve constant `B`
(= `0x26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60`). -/
def Bcurve : ℕ := 17523451383230374900436292617863907649717438939964238673872692863501483215968

/-- The y-coordinate of the Helios generator
(= `0x611dffc62fe02c759e5ac10f40e009b8e3b147387068aaf810dbdf2d817c67ba`). -/
def gY : ℕ := 43927350165885181914572701368652294970994947138804342515295004363921039321018

theorem Bcurve_pos : 0 < Bcurve := by unfold Bcurve; norm_num

theorem Bcurve_lt_q : Bcurve < q := by unfold Bcurve; norm_num

theorem gY_pos : 0 < gY := by unfold gY; norm_num

theorem gY_lt_q : gY < q := by unfold gY; norm_num

theorem Bcurve_lt_2_256 : Bcurve < 2 ^ 256 := lt_trans Bcurve_lt_q q_lt

theorem gY_lt_2_256 : gY < 2 ^ 256 := lt_trans gY_lt_q q_lt

/-! ## 1b. Agreement with the translated constants

`point.helios.B` and `point.helios.G_Y` are `from_be_hex` literals piped through
`dalek_ff_group.field.FieldElement.from_u256` (concrete model: `ok` of the `Uint`
value cast into `Fq`, FunsExternal.lean): kernel-parse the hex strings exactly as for
`MODULUS_ok`. `point.helios.G_X` is `from_u256 (U256::from_u8 1)`, and the generator's
`z` is the dalek `ff::Field::ONE` (concrete model `ok (.ofZMod 1)`). -/

section TranslatedConstants

private theorem parse_B
    (h : ("26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60" h).val)
      = some 17523451383230374900436292617863907649717438939964238673872692863501483215968 := by
  rw [toStr_val]; decide

private theorem len_B
    (h : ("26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60" : String).toByteArray.size ≤ U32.max) :
    ((toStr "26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60" h).val).length
      = 16 * (4#usize).val := by
  rw [toStr_val, usize4_val]; decide

/-- The translated curve constant `point.helios.B` is `ok` of the `Fq` cast of
`Bcurve`. -/
theorem B_ok :
    point.helios.B = ok (dalek_ff_group.field.FieldElement.ofZMod (Bcurve : Fq)) := by
  unfold point.helios.B
  rw [Uint.from_be_hex_ok _ _ Bcurve (len_B _) (parse_B _)]
  simp only [bind_tc_ok]
  unfold dalek_ff_group.field.FieldElement.from_u256
  rw [Uint4.toNat_ofNat Bcurve_lt_2_256]

/-- `B_ok`, in the existential shape of the Selene template. -/
theorem B_ok' : ∃ b, point.helios.B = ok b ∧ b.toZMod = (Bcurve : Fq) :=
  ⟨_, B_ok, rfl⟩

private theorem parse_GY
    (h : ("611dffc62fe02c759e5ac10f40e009b8e3b147387068aaf810dbdf2d817c67ba" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "611dffc62fe02c759e5ac10f40e009b8e3b147387068aaf810dbdf2d817c67ba" h).val)
      = some 43927350165885181914572701368652294970994947138804342515295004363921039321018 := by
  rw [toStr_val]; decide

private theorem len_GY
    (h : ("611dffc62fe02c759e5ac10f40e009b8e3b147387068aaf810dbdf2d817c67ba" : String).toByteArray.size ≤ U32.max) :
    ((toStr "611dffc62fe02c759e5ac10f40e009b8e3b147387068aaf810dbdf2d817c67ba" h).val).length
      = 16 * (4#usize).val := by
  rw [toStr_val, usize4_val]; decide

/-- The translated generator y-coordinate `point.helios.G_Y` is `ok` of the `Fq` cast
of `gY`. -/
theorem G_Y_ok :
    point.helios.G_Y = ok (dalek_ff_group.field.FieldElement.ofZMod (gY : Fq)) := by
  unfold point.helios.G_Y
  rw [Uint.from_be_hex_ok _ _ gY (len_GY _) (parse_GY _)]
  simp only [bind_tc_ok]
  unfold dalek_ff_group.field.FieldElement.from_u256
  rw [Uint4.toNat_ofNat gY_lt_2_256]

/-- `G_Y_ok`, in the existential shape of the Selene template. -/
theorem G_Y_ok' : ∃ g, point.helios.G_Y = ok g ∧ g.toZMod = (gY : Fq) :=
  ⟨_, G_Y_ok, rfl⟩

private theorem one_lt_2_256 : (1 : ℕ) < 2 ^ 256 := by norm_num

/-- The translated generator x-coordinate `point.helios.G_X`
(= `from_u256 (U256::from_u8 1)`) is `ok` of `(1 : Fq)`. -/
theorem G_X_ok :
    point.helios.G_X = ok (dalek_ff_group.field.FieldElement.ofZMod 1) := by
  have hu8 : crypto_bigint.uint.from.Uint.from_u8 4#usize 1#u8
      = ok (Uint.ofNat 4#usize 1) := by
    unfold crypto_bigint.uint.from.Uint.from_u8
    rw [if_neg (by simp), show (1#u8).val = 1 from by simp]
  unfold point.helios.G_X
  rw [hu8]
  simp only [bind_tc_ok]
  unfold dalek_ff_group.field.FieldElement.from_u256
  rw [Uint4.toNat_ofNat one_lt_2_256, Nat.cast_one]

/-- `G_X_ok`, in the existential shape of the Selene template. -/
theorem G_X_ok' : ∃ g, point.helios.G_X = ok g ∧ g.toZMod = (1 : Fq) :=
  ⟨_, G_X_ok, rfl⟩

/-- The translated generator `point.helios.G` is `ok` of the (projective) point with
coordinates `(1, gY, 1)` in `Fq` (its `z` is the dalek `ff::Field::ONE`). -/
theorem G_ok :
    point.helios.G
      = ok { x := dalek_ff_group.field.FieldElement.ofZMod 1,
             y := dalek_ff_group.field.FieldElement.ofZMod (gY : Fq),
             z := dalek_ff_group.field.FieldElement.ofZMod 1 } := by
  unfold point.helios.G
  rw [G_X_ok]
  simp only [bind_tc_ok]
  rw [G_Y_ok]
  simp only [bind_tc_ok]
  rfl

/-- `G_ok`, in the existential shape of the Selene template. -/
theorem G_ok' : ∃ P, point.helios.G = ok P
    ∧ P.x.toZMod = (1 : Fq) ∧ P.y.toZMod = (gY : Fq) ∧ P.z.toZMod = (1 : Fq) :=
  ⟨_, G_ok, rfl, rfl, rfl⟩

end TranslatedConstants

/-! ## 2. The generator satisfies the curve equation -/

/-- ℕ-level curve equation at the generator: `gY^2 ≡ 1^3 - 3·1 + B [MOD q]`, with
`x^3 - 3x` at `x = 1` spelled `1 + (q-3)·1` to stay in ℕ. -/
theorem generator_on_curve : (gY ^ 2) % q = (1 + (q - 3) * 1 + Bcurve) % q := by
  unfold gY Bcurve; norm_num

/-! ## Cast helpers (`(q - k : ℕ)` casts, small nonzero elements) -/

theorem q_cast_zero : ((q : ℕ) : Fq) = 0 := ZMod.natCast_self _

/-- `q = 0` in `Fq`, decimal-literal spelling (the form the polynomial certificates
below and `push_cast` residues need). -/
theorem qLit_cast_zero :
    ((57896044618658097711785492504343953926634992332820282019728792003956564819949 : ℕ)
      : Fq) = 0 :=
  ZMod.natCast_self _

/-- Generic `(q - k : ℕ)`-cast lemma: `((q - k : ℕ) : Fq) = -k`. -/
theorem cast_q_sub (k : ℕ) (hk : k ≤ q) : ((q - k : ℕ) : Fq) = -(k : Fq) := by
  have h : ((q - k : ℕ) : Fq) + (k : Fq) = 0 := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hk]
    exact q_cast_zero
  linear_combination h

theorem qm1_cast : ((q - 1 : ℕ) : Fq) = -1 := by
  rw [cast_q_sub 1 (le_of_lt one_lt_q)]; norm_num

theorem qm2_cast : ((q - 2 : ℕ) : Fq) = -2 := by
  rw [cast_q_sub 2 (le_of_lt two_lt_q)]; norm_num

theorem qm3_cast : ((q - 3 : ℕ) : Fq) = -3 := by
  rw [cast_q_sub 3 (le_of_lt three_lt_q)]; norm_num

theorem two_ne_zero : (2 : Fq) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : Fq) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hle := Nat.le_of_dvd (by norm_num) h2
  norm_num at hle

theorem three_ne_zero : (3 : Fq) ≠ 0 := by
  intro h
  have h3 : ((3 : ℕ) : Fq) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h3
  have hle := Nat.le_of_dvd (by norm_num) h3
  norm_num at hle

/-- `ZMod`-level curve equation at the generator: `gY^2 = 1^3 - 3·1 + B` in `Fq`. -/
theorem generator_on_curve_zmod :
    (gY : Fq) ^ 2 = 1 ^ 3 - 3 * 1 + (Bcurve : Fq) := by
  have hcast := congrArg (Nat.cast : ℕ → Fq) generator_on_curve
  rw [ZMod.natCast_mod, ZMod.natCast_mod] at hcast
  push_cast at hcast
  rw [qm3_cast] at hcast
  linear_combination hcast

/-! ## 3. `B` is a quadratic non-residue mod `q` -/

theorem q_div_two_eq :
    q / 2 = 28948022309329048855892746252171976963317496166410141009864396001978282409974 := by
  norm_num

/-- Kernel computation: `B^((q-1)/2) ≡ q - 1 [MOD q]` (fuel-based `powMod`, evaluated by
kernel reduction exactly as in `Spec/Helios/Prime25519.lean`). -/
theorem B_pow_half_nat :
    Bcurve ^ (28948022309329048855892746252171976963317496166410141009864396001978282409974 : ℕ) % q
      = 57896044618658097711785492504343953926634992332820282019728792003956564819948 :=
  Helios25519Pratt.pow_mod_eq_of_powMod 256 Bcurve _ q
    57896044618658097711785492504343953926634992332820282019728792003956564819948
    (by norm_num) rfl

/-- Euler exponentiation in `Fq`: `B^(q/2) = -1`. -/
theorem B_pow_half : (Bcurve : Fq) ^ (q / 2) = -1 := by
  rw [q_div_two_eq]
  have h := Helios25519Pratt.zmod_pow_eq q Bcurve
    28948022309329048855892746252171976963317496166410141009864396001978282409974
    57896044618658097711785492504343953926634992332820282019728792003956564819948
    B_pow_half_nat
  rw [h, show
    (57896044618658097711785492504343953926634992332820282019728792003956564819948 : ℕ)
      = q - 1 from by norm_num, qm1_cast]

theorem B_cast_ne_zero : (Bcurve : Fq) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hle := Nat.le_of_dvd Bcurve_pos h
  have hlt : Bcurve < 2 ^ 255 - 19 := Bcurve_lt_q
  omega

/-- **`B` is not a square in `Fq`.** (Euler's criterion + the kernel computation
`B^((q-1)/2) = -1`.) This is what makes the `x = 0` check of `is_identity` sound: no
affine point of the curve has `x = 0`. -/
theorem B_nonresidue : ¬ IsSquare (Bcurve : Fq) := by
  intro hsq
  have h1 := (ZMod.euler_criterion _ B_cast_ne_zero).mp hsq
  rw [B_pow_half] at h1
  exact ZMod.neg_one_ne_one h1

/-- No affine point of Helios has `x = 0`: `y^2 = 0^3 - 3·0 + B` has no solution. -/
theorem no_affine_x_zero (y : Fq) : y ^ 2 ≠ (Bcurve : Fq) := by
  intro h
  exact B_nonresidue ⟨y, by rw [← h]; ring⟩

/-! ## 4. The discriminant is nonzero

For `y^2 = x^3 + ax + b` with `a = -3`, `b = B`:
`Δ = -16(4a^3 + 27b^2) = 1728 - 432·B^2 (mod q)`; `deltaNat` is its reduced value. -/

/-- `(-16·(4·(-3)^3 + 27·B^2)) mod q`, as a ℕ literal. -/
def deltaNat : ℕ := 6313752204669021745303155113349697875245831996239856149851921913633624410496

/-- The multiple-of-`q` slack in `deltaNat + 432·B^2 = 1728 + kDelta·q`. -/
def kDelta : ℕ := 2291258813518305846505340014468418082273714950132076201769768485274704443913664

theorem deltaNat_pos : 0 < deltaNat := by unfold deltaNat; norm_num

theorem deltaNat_lt_q : deltaNat < q := by unfold deltaNat; norm_num

/-- ℕ-level discriminant identity (raw ingredient: everything else about `Δ` follows by
casting this). -/
theorem delta_slack : deltaNat + 432 * Bcurve ^ 2 = 1728 + kDelta * q := by
  unfold deltaNat Bcurve kDelta; norm_num

/-- `deltaNat` is the discriminant in `Fq`, `1728 - 432·B^2` form. -/
theorem delta_cast : ((deltaNat : ℕ) : Fq) = 1728 - 432 * (Bcurve : Fq) ^ 2 := by
  have h := congrArg (Nat.cast : ℕ → Fq) delta_slack
  have h0 := qLit_cast_zero
  push_cast at h h0
  linear_combination h + (kDelta : Fq) * h0

/-- `deltaNat` is the discriminant in `Fq`, `-16(4a^3 + 27b^2)` form (`a = -3`, `b = B`). -/
theorem delta_cast' :
    ((deltaNat : ℕ) : Fq) = -16 * (4 * (-3 : Fq) ^ 3 + 27 * (Bcurve : Fq) ^ 2) := by
  rw [delta_cast]; ring

theorem deltaNat_cast_ne_zero : ((deltaNat : ℕ) : Fq) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hle := Nat.le_of_dvd deltaNat_pos h
  have hlt : deltaNat < 2 ^ 255 - 19 := deltaNat_lt_q
  omega

/-- **The short-Weierstrass discriminant of Helios is nonzero**:
`-16(4·(-3)^3 + 27·B^2) ≠ 0` in `Fq`. -/
theorem delta_ne_zero :
    (-16 * (4 * (-3 : Fq) ^ 3 + 27 * (Bcurve : Fq) ^ 2)) ≠ 0 := by
  rw [← delta_cast']
  exact deltaNat_cast_ne_zero

/-! ## 5. No 2-torsion: the cubic `X^3 - 3X + B` has no root in `Fq`

Strategy (all kernel-friendly, identical to the Selene certificate):
* `polyPowMod` computes `g = X^q mod (f, q)` in `(ZMod q)[X]/(f)` on ℕ coefficient
  triples, by fuel-based binary powering with per-step reduction (kernel-evaluates by
  `rfl`, like `powMod` in `Spec/Helios/Prime25519.lean`);
* `evalQ_polyPowMod` (a generic, symbolic lemma) says: at any root `x` of `f`,
  `evalQ g x = x^q`;
* Fermat (`ZMod.pow_card`) gives `x^q = x`, so `h = g - X` also vanishes at `x`;
* a concrete Bezout certificate `u·f + v·h = 1 + q·s` **over ℕ** (one `ring` call)
  evaluates at `x` to `0 = 1` — contradiction. -/

/-- Product of two quadratics reduced modulo the cubic `X^3 - 3X + BB` over `ZMod pp`,
on ℕ coefficient triples kept reduced mod `pp`. Reduction rules:
`X^3 ≡ 3X + (pp - BB)`, `X^4 ≡ 3X^2 + (pp - BB)·X`. -/
def polyMulMod (pp BB : ℕ) (u v : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  ((u.1 * v.1 + (pp - BB) * (u.2.1 * v.2.2 + u.2.2 * v.2.1)) % pp,
   (u.1 * v.2.1 + u.2.1 * v.1 + 3 * (u.2.1 * v.2.2 + u.2.2 * v.2.1)
      + (pp - BB) * (u.2.2 * v.2.2)) % pp,
   (u.1 * v.2.2 + u.2.1 * v.2.1 + u.2.2 * v.1 + 3 * (u.2.2 * v.2.2)) % pp)

/-- Fuel-based binary powering in `(ZMod pp)[X] / (X^3 - 3X + BB)`: computes
`u^e mod (f, pp)` whenever `e < 2^fuel`. Structurally recursive on `fuel` so the kernel
evaluates it by plain recursor reduction (mirrors `Helios25519Pratt.powMod`). -/
def polyPowMod (pp BB : ℕ) : ℕ → ℕ × ℕ × ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, _ => (1 % pp, 0, 0)
  | fuel + 1, a, e =>
    if e % 2 = 0 then
      if e = 0 then (1 % pp, 0, 0)
      else polyPowMod pp BB fuel (polyMulMod pp BB a a) (e / 2)
    else polyMulMod pp BB (polyPowMod pp BB fuel (polyMulMod pp BB a a) (e / 2)) a

/-- Evaluation of a coefficient triple as a quadratic at `x : ZMod pp`. -/
def evalQ (pp : ℕ) (t : ℕ × ℕ × ℕ) (x : ZMod pp) : ZMod pp :=
  (t.1 : ZMod pp) + (t.2.1 : ZMod pp) * x + (t.2.2 : ZMod pp) * x ^ 2

theorem evalQ_one (pp : ℕ) (x : ZMod pp) : evalQ pp (1 % pp, 0, 0) x = 1 := by
  simp [evalQ, ZMod.natCast_mod]

/-- At any root of the cubic (`x^3 = 3x - BB`), `polyMulMod` evaluates to the product. -/
theorem evalQ_polyMulMod (pp BB : ℕ) (hB : BB ≤ pp) (u v : ℕ × ℕ × ℕ) (x : ZMod pp)
    (hx : x ^ 3 = 3 * x - (BB : ZMod pp)) :
    evalQ pp (polyMulMod pp BB u v) x = evalQ pp u x * evalQ pp v x := by
  obtain ⟨u0, u1, u2⟩ := u
  obtain ⟨v0, v1, v2⟩ := v
  simp only [polyMulMod, evalQ, ZMod.natCast_mod]
  push_cast [Nat.cast_sub hB]
  rw [ZMod.natCast_self]
  linear_combination (-(u1 : ZMod pp) * v2 - (u2 : ZMod pp) * v1
    - ((u2 : ZMod pp) * v2) * x) * hx

/-- At any root of the cubic, `polyPowMod` evaluates to the `e`-th power. -/
theorem evalQ_polyPowMod (pp BB : ℕ) (hB : BB ≤ pp) :
    ∀ (fuel : ℕ) (u : ℕ × ℕ × ℕ) (e : ℕ) (x : ZMod pp), e < 2 ^ fuel →
      x ^ 3 = 3 * x - (BB : ZMod pp) →
      evalQ pp (polyPowMod pp BB fuel u e) x = (evalQ pp u x) ^ e := by
  intro fuel
  induction fuel with
  | zero =>
    intro u e x he _
    have he0 : e = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using he)
    subst he0
    simp [polyPowMod, evalQ_one]
  | succ fuel ih =>
    intro u e x he hx
    have h2 : e / 2 < 2 ^ fuel := by
      have hp : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := pow_succ 2 fuel
      omega
    rw [polyPowMod]
    by_cases hpar : e % 2 = 0
    · rw [if_pos hpar]
      by_cases he0 : e = 0
      · subst he0; simp [evalQ_one]
      · rw [if_neg he0, ih _ _ x h2 hx, evalQ_polyMulMod pp BB hB u u x hx,
          ← pow_two, ← pow_mul]
        have hee : 2 * (e / 2) = e := by omega
        rw [hee]
    · rw [if_neg hpar, evalQ_polyMulMod pp BB hB _ u x hx, ih _ _ x h2 hx,
        evalQ_polyMulMod pp BB hB u u x hx, ← pow_two, ← pow_mul, ← pow_succ]
      have hee : 2 * (e / 2) + 1 = e := by omega
      rw [hee]

/-- Kernel computation of the certificate quadratic `g = X^q mod (X^3 - 3X + B, q)`
(the analogue of the `rfl`-evaluated `powMod` calls in `Spec/Helios/Prime25519.lean`). -/
theorem xp_mod_cubic :
    polyPowMod q Bcurve 256 (0, 1, 0) q
      = (25126635539119995324611147167851544524523912665903294945196329538904533211291,
         32421083227964297191278865183246409586299016642261747849303034941370369047512,
         16384704539769051193587172668246204701055539833458493537266231232526015804329) := by
  rfl

/-- The Bezout certificate `u·f + v·(g - X) = 1 + q·s` for
`f = X^3 + (q-3)X + B` and the concrete `g` above, as a single polynomial identity over
ℕ (coefficient-wise equal, hence provable by `ring`). -/
theorem bezout_certificate (n : ℕ) :
    (3558147758186278436816686028891465063580136843669602722265478650510278419867 * n
      + 32440963309528561033763387703639567998770431968873316263874173958162180735042)
    * (n ^ 3
      + 57896044618658097711785492504343953926634992332820282019728792003956564819946 * n
      + 17523451383230374900436292617863907649717438939964238673872692863501483215968)
    + (12267301818471461061938258208176410103362722991003337857104922427122756259091 * n ^ 2
      + 19314898318593084967533161390934288377106521063811411760691542666528901257711 * n
      + 47198554341344857760641749366690383461769363850600869133006467406854568640307)
    * (16384704539769051193587172668246204701055539833458493537266231232526015804329 * n ^ 2
      + 32421083227964297191278865183246409586299016642261747849303034941370369047511 * n
      + 25126635539119995324611147167851544524523912665903294945196329538904533211291)
    = 1 + 57896044618658097711785492504343953926634992332820282019728792003956564819949
      * (3471672669864076989318747759377714226643255244887806691341445872533722730494 * n ^ 4
        + 12335697889366523082064361029527488496773920800092876197779299976918854339638 * n ^ 3
        + 33055505075143561669342576450072133180055030222650687662985378267981046356863 * n ^ 2
        + 68331112835426790812045137284336071253662189587164274173656528895712898228534 * n
        + 30302908045683858863525510914301401778849681117200757676140969540096705272608) := by
  ring

/-- **The cubic `X^3 - 3X + B` has no root in `Fq`** — equivalently, Helios has no
point with `y = 0` (no 2-torsion on the affine curve). -/
theorem cubic_no_root (x : Fq) : x ^ 3 - 3 * x + (Bcurve : Fq) ≠ 0 := by
  intro hf
  have hx : x ^ 3 = 3 * x - (Bcurve : Fq) := by linear_combination hf
  -- the certificate: g(x) = x^q for the concrete quadratic g
  have hgx := evalQ_polyPowMod q Bcurve Bcurve_lt_q.le 256 (0, 1, 0) q x q_lt hx
  rw [xp_mod_cubic] at hgx
  have hbase : evalQ q (0, 1, 0) x = x := by
    simp [evalQ]
  rw [hbase, ZMod.pow_card] at hgx
  simp only [evalQ] at hgx
  push_cast at hgx
  -- numeral forms of the special constants
  have hBeq : (Bcurve : Fq)
      = (17523451383230374900436292617863907649717438939964238673872692863501483215968
          : Fq) := by
    unfold Bcurve; push_cast; ring
  have hqL0 : (57896044618658097711785492504343953926634992332820282019728792003956564819949
      : Fq) = 0 := by
    rw [← qLit_cast_zero]; push_cast; ring
  -- lift x to a ℕ cast and specialize the Bezout certificate
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  have hcast := congrArg (Nat.cast : ℕ → Fq) (bezout_certificate n)
  push_cast at hcast
  rw [hqL0, zero_mul, add_zero] at hcast
  -- the two vanishing factors
  have hFf : (↑n : Fq) ^ 3
      + (57896044618658097711785492504343953926634992332820282019728792003956564819946
          : Fq) * ↑n
      + (17523451383230374900436292617863907649717438939964238673872692863501483215968
          : Fq) = 0 := by
    linear_combination hf - hBeq + (↑n : Fq) * hqL0
  have hHf : (16384704539769051193587172668246204701055539833458493537266231232526015804329
        : Fq) * (↑n : Fq) ^ 2
      + (32421083227964297191278865183246409586299016642261747849303034941370369047511
        : Fq) * ↑n
      + (25126635539119995324611147167851544524523912665903294945196329538904533211291
        : Fq) = 0 := by
    linear_combination hgx
  -- combine: 1 = 0 in Fq, contradiction
  have hone : (1 : Fq) = 0 := by
    linear_combination
      ((3558147758186278436816686028891465063580136843669602722265478650510278419867
          : Fq) * ↑n
        + (32440963309528561033763387703639567998770431968873316263874173958162180735042
          : Fq)) * hFf
      + ((12267301818471461061938258208176410103362722991003337857104922427122756259091
          : Fq) * (↑n : Fq) ^ 2
        + (19314898318593084967533161390934288377106521063811411760691542666528901257711
          : Fq) * ↑n
        + (47198554341344857760641749366690383461769363850600869133006467406854568640307
          : Fq)) * hHf
      - hcast
  exact one_ne_zero hone

/-- **Helios has no 2-torsion**: no `(x, y)` with `y^2 = x^3 - 3x + B` has `y = 0`. -/
theorem no_two_torsion (x y : Fq) (h : y ^ 2 = x ^ 3 - 3 * x + (Bcurve : Fq)) :
    y ≠ 0 := by
  rintro rfl
  exact cubic_no_root x (by linear_combination -h)

end Helios

end HelioseleneSpec
