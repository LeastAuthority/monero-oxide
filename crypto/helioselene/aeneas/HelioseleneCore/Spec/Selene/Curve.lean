/- Kernel-checkable curve constants and number-theoretic facts for the Selene curve

     y^2 = x^3 - 3x + B   over   ZMod p,
     p = 2^255 - 0x8cab7e2e6960ce8067af49720ee20ad,
     B = 0x38c40d10c226ef3bc597c2e1e25bc748e3401c3d031d14ca2265f309ba81efe4,

   with generator (1, gY), gY = 0x39098c0a54bd9d2781c7d734720d5ca639ee79deeefcd74517fced93ad6635c0.

   Contents (everything PROVED — no `sorry`, and no axioms/`native_decide` beyond
   the `<const>._native.decide.ax_1` string-length axioms already baked into the
   generated `Funs.lean` constants, inherited by the `_ok` constant-agreement
   lemmas as detailed at the end of this header):
   1. `Bcurve`/`gY` literals, `_lt_p` bounds, and agreement of the TRANSLATED constants
      `point.selene.B` / `point.selene.G_Y` / `point.selene.G_X` (and the full generator
      `point.selene.G`) with them, via the same kernel `toStr_val + decide` route as
      `MODULUS_ok` in `Spec/Externals.lean`;
   2. `generator_on_curve` : the generator satisfies the curve equation (ℕ- and ZMod-level);
   3. `B_nonresidue` : `B` is a quadratic non-residue mod `p` (kernel `powMod` computation of
      `B^((p-1)/2) ≡ -1` + mathlib's Euler criterion), with corollary `no_affine_x_zero`
      (no curve point has x = 0 — the soundness fact behind `is_identity`'s `x = 0` check);
   4. `delta_ne_zero` : the short-Weierstrass discriminant `-16(4·(-3)^3 + 27B^2)` is
      nonzero in `ZMod p` (plus the raw ℕ-level ingredients for the mathlib-facing file);
   5. `no_two_torsion` : no point of the curve has y = 0, via `cubic_no_root`: the cubic
      `X^3 - 3X + B` has no root in `ZMod p`. Certificate: a fuel-based kernel computation
      of `g = X^p mod (f, p)` in `(ZMod p)[X]/(f)` (`polyPowMod`, evaluated by `rfl` like
      `powMod` in `Spec/Prime.lean`), Fermat (`ZMod.pow_card`), and a concrete Bezout
      identity `u·f + v·(g - X) = 1` checked by a single `ring` call over ℕ.

   The numeric certificates were generated and cross-checked by
   `phase-c2/gen_curve.py` (scratchpad).

   Depends only on `Spec/Phi.lean` (hence `Spec/Externals.lean` + the generated model) and
   `Spec/Prime.lean`; a follow-up file connects these facts to mathlib's `WeierstrassCurve`.

   Exported lemmas that mention the generated hex-string constants (`B_ok`, `G_Y_ok`, …)
   — and therefore every `Spec/Selene/Ops.lean` `_ok` contract that touches a translated
   hex constant — transitively inherit the `<const>._native.decide.ax_1` axioms baked
   into Funs.lean: the field-layer ones (`field.MODULUS`, `MODULUS_255_DISTANCE`,
   `TWO_MODULUS_255_DISTANCE`) plus, new with the Selene scope, `point.selene.B`,
   `point.selene.G_Y` and (on the sqrt cone) `field.verified.sqrt.MODULUS_PLUS_ONE_DIV_FOUR`
   (see README §5c.3 / human_audit_assumptions.txt VIII.3; each asserts only that a hex
   string literal is at most `U32.max` bytes, and the parsed values are re-proved
   kernel-only here). The purely number-theoretic facts (`B_nonresidue`, `cubic_no_root`,
   `no_two_torsion`, `delta_ne_zero`, `generator_on_curve_zmod`, `p_prime'`) depend on no
   axioms beyond `propext`, `Classical.choice`, `Quot.sound`. -/
import HelioseleneCore.Spec.Phi
import HelioseleneCore.Spec.Prime

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

namespace Selene

open crypto_bigint.uint HelioseleneModel

/-! ## 1. The curve constants as ℕ literals -/

/-- The Selene curve constant `B` (= `0x38c40d10c226ef3bc597c2e1e25bc748e3401c3d031d14ca2265f309ba81efe4`). -/
def Bcurve : ℕ := 25675911719867737339625140396204798989996478324626569376465022644547366285284

/-- The y-coordinate of the Selene generator
(= `0x39098c0a54bd9d2781c7d734720d5ca639ee79deeefcd74517fced93ad6635c0`). -/
def gY : ℕ := 25798700515841442074436724357845010259191889815205036617843407906692357567936

theorem Bcurve_pos : 0 < Bcurve := by unfold Bcurve; norm_num

theorem Bcurve_lt_p : Bcurve < p := by unfold Bcurve p; norm_num

theorem gY_pos : 0 < gY := by unfold gY; norm_num

theorem gY_lt_p : gY < p := by unfold gY p; norm_num

theorem two_lt_p : 2 < p := by unfold p; norm_num

theorem three_lt_p : 3 < p := by unfold p; norm_num

/-- `p` is prime, stated for the `HelioseleneSpec.p` spelling (kernel Pratt certificate,
`Spec/Prime.lean`). -/
theorem p_prime' : Nat.Prime p := p_prime

instance fact_p_prime' : Fact (Nat.Prime p) := ⟨p_prime'⟩

instance fact_two_lt_p : Fact (2 < p) := ⟨two_lt_p⟩

/-! ## 1b. Agreement with the translated constants

`point.selene.B` and `point.selene.G_Y` are `from_be_hex` literals: kernel-parse the hex
strings exactly as for `MODULUS_ok`. `point.selene.G_X` is
`from_u256 (U256::from_u8 1)`, i.e. `1 % p` through the concrete `const_rem` model. -/

section TranslatedConstants

private theorem parse_B
    (h : ("38c40d10c226ef3bc597c2e1e25bc748e3401c3d031d14ca2265f309ba81efe4" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "38c40d10c226ef3bc597c2e1e25bc748e3401c3d031d14ca2265f309ba81efe4" h).val)
      = some 25675911719867737339625140396204798989996478324626569376465022644547366285284 := by
  rw [toStr_val]; decide

private theorem len_B
    (h : ("38c40d10c226ef3bc597c2e1e25bc748e3401c3d031d14ca2265f309ba81efe4" : String).toByteArray.size ≤ U32.max) :
    ((toStr "38c40d10c226ef3bc597c2e1e25bc748e3401c3d031d14ca2265f309ba81efe4" h).val).length
      = 16 * (4#usize).val := by
  rw [toStr_val, usize4_val]; decide

/-- The translated curve constant `point.selene.B` is `ok` with value `Bcurve`. -/
theorem B_ok : ∃ b, point.selene.B = ok b ∧ b.toNat = Bcurve := by
  refine ⟨Uint.ofNat 4#usize Bcurve, ?_, Uint4.toNat_ofNat (lt_trans Bcurve_lt_p p_lt)⟩
  unfold point.selene.B
  rw [Uint.from_be_hex_ok _ _ Bcurve (len_B _) (parse_B _)]
  rfl

private theorem parse_GY
    (h : ("39098c0a54bd9d2781c7d734720d5ca639ee79deeefcd74517fced93ad6635c0" : String).toByteArray.size ≤ U32.max) :
    parseBeHex? ((toStr "39098c0a54bd9d2781c7d734720d5ca639ee79deeefcd74517fced93ad6635c0" h).val)
      = some 25798700515841442074436724357845010259191889815205036617843407906692357567936 := by
  rw [toStr_val]; decide

private theorem len_GY
    (h : ("39098c0a54bd9d2781c7d734720d5ca639ee79deeefcd74517fced93ad6635c0" : String).toByteArray.size ≤ U32.max) :
    ((toStr "39098c0a54bd9d2781c7d734720d5ca639ee79deeefcd74517fced93ad6635c0" h).val).length
      = 16 * (4#usize).val := by
  rw [toStr_val, usize4_val]; decide

/-- The translated generator y-coordinate `point.selene.G_Y` is `ok` with value `gY`. -/
theorem G_Y_ok : ∃ g, point.selene.G_Y = ok g ∧ g.toNat = gY := by
  refine ⟨Uint.ofNat 4#usize gY, ?_, Uint4.toNat_ofNat (lt_trans gY_lt_p p_lt)⟩
  unfold point.selene.G_Y
  rw [Uint.from_be_hex_ok _ _ gY (len_GY _) (parse_GY _)]
  rfl

private theorem one_lt_2_256 : (1 : ℕ) < 2 ^ 256 := by norm_num

/-- The translated generator x-coordinate `point.selene.G_X`
(= `from_u256 (U256::from_u8 1)` = `1 % p` through `const_rem`) is `ok` with value `1`. -/
theorem G_X_ok : ∃ g, point.selene.G_X = ok g ∧ g.toNat = 1 := by
  obtain ⟨m, hm, hmval⟩ := MODULUS_ok
  have hu8 : crypto_bigint.uint.from.Uint.from_u8 4#usize 1#u8
      = ok (Uint.ofNat 4#usize 1) := by
    unfold crypto_bigint.uint.from.Uint.from_u8
    rw [if_neg (by simp), show (1#u8).val = 1 from by simp]
  have hrem : crypto_bigint.uint.div.Uint.const_rem (Uint.ofNat 4#usize 1) m
      = ok (Uint.ofNat 4#usize 1, (m.toNat != 0)) := by
    unfold crypto_bigint.uint.div.Uint.const_rem
    have hv : (Uint.ofNat 4#usize 1).toNat % m.toNat = 1 := by
      rw [Uint4.toNat_ofNat one_lt_2_256, hmval]
      exact Nat.mod_eq_of_lt one_lt_p
    rw [hv]
  refine ⟨Uint.ofNat 4#usize 1, ?_, Uint4.toNat_ofNat one_lt_2_256⟩
  unfold point.selene.G_X field.HelioseleneField.from_u256
  rw [hu8]
  simp only [bind_tc_ok]
  rw [hm]
  simp only [bind_tc_ok]
  rw [hrem]
  rfl

/-- The translated generator `point.selene.G` is `ok` with (projective) coordinates of
values `(1, gY, 1)`. -/
theorem G_ok : ∃ P, point.selene.G = ok P
    ∧ P.x.toNat = 1 ∧ P.y.toNat = gY ∧ P.z.toNat = 1 := by
  obtain ⟨gx, hgx, hgxv⟩ := G_X_ok
  obtain ⟨gy, hgy, hgyv⟩ := G_Y_ok
  obtain ⟨o, ho, hov⟩ := Uint.ONE_ok 4#usize (by simp)
  refine ⟨⟨gx, gy, o⟩, ?_, hgxv, hgyv, hov⟩
  unfold point.selene.G field.HelioseleneField.Insts.FfField.ONE
  rw [hgx]
  simp only [bind_tc_ok]
  rw [hgy]
  simp only [bind_tc_ok]
  rw [ho]
  simp only [bind_tc_ok]

end TranslatedConstants

/-! ## 2. The generator satisfies the curve equation -/

/-- ℕ-level curve equation at the generator: `gY^2 ≡ 1^3 - 3·1 + B [MOD p]`, with
`x^3 - 3x` at `x = 1` spelled `1 + (p-3)·1` to stay in ℕ. -/
theorem generator_on_curve : (gY ^ 2) % p = (1 + (p - 3) * 1 + Bcurve) % p := by
  unfold gY Bcurve p; norm_num

/-! ## Cast helpers (`(p - k : ℕ)` casts, small nonzero elements) -/

/-- Generic `(p - k : ℕ)`-cast lemma: `((p - k : ℕ) : ZMod p) = -k`. -/
theorem cast_p_sub (k : ℕ) (hk : k ≤ p) : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
  have h : ((p - k : ℕ) : ZMod p) + (k : ZMod p) = 0 := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hk, ZMod.natCast_self]
  linear_combination h

theorem pm1_cast : ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [cast_p_sub 1 (le_of_lt one_lt_p)]; norm_num

theorem pm2_cast : ((p - 2 : ℕ) : ZMod p) = -2 := by
  rw [cast_p_sub 2 (le_of_lt two_lt_p)]; norm_num

theorem pm3_cast : ((p - 3 : ℕ) : ZMod p) = -3 := by
  rw [cast_p_sub 3 (le_of_lt three_lt_p)]; norm_num

theorem two_ne_zero : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hle := Nat.le_of_dvd (by norm_num) h2
  have := two_lt_p
  omega

theorem three_ne_zero : (3 : ZMod p) ≠ 0 := by
  intro h
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h3
  have hle := Nat.le_of_dvd (by norm_num) h3
  have := three_lt_p
  omega

/-- `ZMod`-level curve equation at the generator: `gY^2 = 1^3 - 3·1 + B` in `ZMod p`. -/
theorem generator_on_curve_zmod :
    (gY : ZMod p) ^ 2 = 1 ^ 3 - 3 * 1 + (Bcurve : ZMod p) := by
  have hcast := congrArg (Nat.cast : ℕ → ZMod p) generator_on_curve
  rw [ZMod.natCast_mod, ZMod.natCast_mod] at hcast
  push_cast at hcast
  rw [pm3_cast] at hcast
  linear_combination hcast

/-! ## 3. `B` is a quadratic non-residue mod `p` -/

theorem p_div_two_eq :
    p / 2 = 28948022309329048855892746252171976963311652967615346754502404787283660697513 := by
  unfold p; norm_num

/-- Kernel computation: `B^((p-1)/2) ≡ p - 1 [MOD p]` (fuel-based `powMod`, evaluated by
kernel reduction exactly as in `Spec/Prime.lean`). -/
theorem B_pow_half_nat :
    Bcurve ^ (28948022309329048855892746252171976963311652967615346754502404787283660697513 : ℕ) % p
      = 57896044618658097711785492504343953926623305935230693509004809574567321395026 :=
  HelioselenePratt.pow_mod_eq_of_powMod 256 Bcurve _ p
    57896044618658097711785492504343953926623305935230693509004809574567321395026
    (by norm_num) rfl

/-- Euler exponentiation in `ZMod p`: `B^(p/2) = -1`. -/
theorem B_pow_half : (Bcurve : ZMod p) ^ (p / 2) = -1 := by
  rw [p_div_two_eq]
  have h := HelioselenePratt.zmod_pow_eq p Bcurve
    28948022309329048855892746252171976963311652967615346754502404787283660697513
    57896044618658097711785492504343953926623305935230693509004809574567321395026
    B_pow_half_nat
  rw [h, show
    (57896044618658097711785492504343953926623305935230693509004809574567321395026 : ℕ)
      = p - 1 from by unfold p; norm_num, pm1_cast]

theorem B_cast_ne_zero : (Bcurve : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hle := Nat.le_of_dvd Bcurve_pos h
  have := Bcurve_lt_p
  omega

/-- **`B` is not a square in `ZMod p`.** (Euler's criterion + the kernel computation
`B^((p-1)/2) = -1`.) This is what makes the `x = 0` check of `is_identity` sound: no
affine point of the curve has `x = 0`. -/
theorem B_nonresidue : ¬ IsSquare (Bcurve : ZMod p) := by
  intro hsq
  have h1 := (ZMod.euler_criterion p B_cast_ne_zero).mp hsq
  rw [B_pow_half] at h1
  exact ZMod.neg_one_ne_one h1

/-- No affine point of Selene has `x = 0`: `y^2 = 0^3 - 3·0 + B` has no solution. -/
theorem no_affine_x_zero (y : ZMod p) : y ^ 2 ≠ (Bcurve : ZMod p) := by
  intro h
  exact B_nonresidue ⟨y, by rw [← h]; ring⟩

/-! ## 4. The discriminant is nonzero

For `y^2 = x^3 + ax + b` with `a = -3`, `b = B`:
`Δ = -16(4a^3 + 27b^2) = 1728 - 432·B^2 (mod p)`; `deltaNat` is its reduced value. -/

/-- `(-16·(4·(-3)^3 + 27·B^2)) mod p`, as a ℕ literal. -/
def deltaNat : ℕ := 8051352843288349213529073407567262099065294335604333620539967640177047609333

/-- The multiple-of-`p` slack in `deltaNat + 432·B^2 = 1728 + kDelta·p`. -/
def kDelta : ℕ := 4919110745805274729322426980331806734559842176089038734953250142053415940769111

theorem deltaNat_pos : 0 < deltaNat := by unfold deltaNat; norm_num

theorem deltaNat_lt_p : deltaNat < p := by unfold deltaNat p; norm_num

/-- ℕ-level discriminant identity (raw ingredient: everything else about `Δ` follows by
casting this). -/
theorem delta_slack : deltaNat + 432 * Bcurve ^ 2 = 1728 + kDelta * p := by
  unfold deltaNat Bcurve kDelta p; norm_num

/-- `deltaNat` is the discriminant in `ZMod p`, `1728 - 432·B^2` form. -/
theorem delta_cast : ((deltaNat : ℕ) : ZMod p) = 1728 - 432 * (Bcurve : ZMod p) ^ 2 := by
  have h := congrArg (Nat.cast : ℕ → ZMod p) delta_slack
  push_cast at h
  rw [ZMod.natCast_self] at h
  linear_combination h

/-- `deltaNat` is the discriminant in `ZMod p`, `-16(4a^3 + 27b^2)` form (`a = -3`, `b = B`). -/
theorem delta_cast' :
    ((deltaNat : ℕ) : ZMod p) = -16 * (4 * (-3 : ZMod p) ^ 3 + 27 * (Bcurve : ZMod p) ^ 2) := by
  rw [delta_cast]; ring

theorem deltaNat_cast_ne_zero : ((deltaNat : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hle := Nat.le_of_dvd deltaNat_pos h
  have := deltaNat_lt_p
  omega

/-- **The short-Weierstrass discriminant of Selene is nonzero**:
`-16(4·(-3)^3 + 27·B^2) ≠ 0` in `ZMod p`. -/
theorem delta_ne_zero :
    (-16 * (4 * (-3 : ZMod p) ^ 3 + 27 * (Bcurve : ZMod p) ^ 2)) ≠ 0 := by
  rw [← delta_cast']
  exact deltaNat_cast_ne_zero

/-! ## 5. No 2-torsion: the cubic `X^3 - 3X + B` has no root in `ZMod p`

Strategy (all kernel-friendly):
* `polyPowMod` computes `g = X^p mod (f, p)` in `(ZMod p)[X]/(f)` on ℕ coefficient
  triples, by fuel-based binary powering with per-step reduction (kernel-evaluates by
  `rfl`, like `powMod` in `Spec/Prime.lean`);
* `evalQ_polyPowMod` (a generic, symbolic lemma) says: at any root `x` of `f`,
  `evalQ g x = x^p`;
* Fermat (`ZMod.pow_card`) gives `x^p = x`, so `h = g - X` also vanishes at `x`;
* a concrete Bezout certificate `u·f + v·h = 1 + p·s` **over ℕ** (one `ring` call)
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
evaluates it by plain recursor reduction (mirrors `HelioselenePratt.powMod`). -/
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

/-- Kernel computation of the certificate quadratic `g = X^p mod (X^3 - 3X + B, p)`
(the analogue of the `rfl`-evaluated `powMod` calls in `Spec/Prime.lean`). -/
theorem xp_mod_cubic :
    polyPowMod p Bcurve 256 (0, 1, 0) p
      = (26894631634706989992115336946156599071555735384089111478534775845557834998994,
         16135888693817877337947852316789387065624841778930314169633432304437854951731,
         44448728801304602715727824031265654390845438243186137769737421651788403895530) := by
  rfl

/-- The Bezout certificate `u·f + v·(g - X) = 1 + p·s` for
`f = X^3 + (p-3)X + B` and the concrete `g` above, as a single polynomial identity over
ℕ (coefficient-wise equal, hence provable by `ring`). -/
theorem bezout_certificate (n : ℕ) :
    (10714705466783398919153788324387207784993784905826990448772425602556871707829 * n
      + 57235417221613563794669871010566018951260221108442596502766824992869568682169)
    * (n ^ 3
      + 57896044618658097711785492504343953926623305935230693509004809574567321395024 * n
      + 25675911719867737339625140396204798989996478324626569376465022644547366285284)
    + (33876748068821087438090232889582374565686159768566685920920121567467009425787 * n ^ 2
      + 50650572635476552433305898559462997992770685948553974631914612199262475541230 * n
      + 13923668626353120404886080384319955949384710940522404749921965605415382174961)
    * (44448728801304602715727824031265654390845438243186137769737421651788403895530 * n ^ 2
      + 16135888693817877337947852316789387065624841778930314169633432304437854951730 * n
      + 26894631634706989992115336946156599071555735384089111478534775845557834998994)
    = 1 + 57896044618658097711785492504343953926623305935230693509004809574567321395027
      * (26008311923538250203700418133422982193049239582192843993325621386184502934257 * n ^ 4
        + 48327740198514019191353356660977225244638612520796145873268942824749032545577 * n ^ 3
        + 51257786583458652525999338829453308040235773246619194196473389657557987156052 * n ^ 2
        + 89396665960046326473385747307727929009668387856332585775348343602468075422246 * n
        + 31850940261766402747469868386671411356021288699675523998173288336399208693527) := by
  ring

theorem pLit_cast_zero :
    ((57896044618658097711785492504343953926623305935230693509004809574567321395027 : ℕ)
      : ZMod p) = 0 :=
  ZMod.natCast_self p

/-- **The cubic `X^3 - 3X + B` has no root in `ZMod p`** — equivalently, Selene has no
point with `y = 0` (no 2-torsion on the affine curve). -/
theorem cubic_no_root (x : ZMod p) : x ^ 3 - 3 * x + (Bcurve : ZMod p) ≠ 0 := by
  intro hf
  have hx : x ^ 3 = 3 * x - (Bcurve : ZMod p) := by linear_combination hf
  -- the certificate: g(x) = x^p for the concrete quadratic g
  have hgx := evalQ_polyPowMod p Bcurve Bcurve_lt_p.le 256 (0, 1, 0) p x p_lt hx
  rw [xp_mod_cubic] at hgx
  have hbase : evalQ p (0, 1, 0) x = x := by
    simp [evalQ]
  rw [hbase, ZMod.pow_card] at hgx
  simp only [evalQ] at hgx
  push_cast at hgx
  -- numeral forms of the special constants
  have hBeq : (Bcurve : ZMod p)
      = (25675911719867737339625140396204798989996478324626569376465022644547366285284
          : ZMod p) := by
    unfold Bcurve; push_cast; ring
  have hPL0 : (57896044618658097711785492504343953926623305935230693509004809574567321395027
      : ZMod p) = 0 := by
    rw [← pLit_cast_zero]; push_cast; ring
  -- lift x to a ℕ cast and specialize the Bezout certificate
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  have hcast := congrArg (Nat.cast : ℕ → ZMod p) (bezout_certificate n)
  push_cast at hcast
  rw [hPL0, zero_mul, add_zero] at hcast
  -- the two vanishing factors
  have hFf : (↑n : ZMod p) ^ 3
      + (57896044618658097711785492504343953926623305935230693509004809574567321395024
          : ZMod p) * ↑n
      + (25675911719867737339625140396204798989996478324626569376465022644547366285284
          : ZMod p) = 0 := by
    linear_combination hf - hBeq + (↑n : ZMod p) * hPL0
  have hHf : (44448728801304602715727824031265654390845438243186137769737421651788403895530
        : ZMod p) * (↑n : ZMod p) ^ 2
      + (16135888693817877337947852316789387065624841778930314169633432304437854951730
        : ZMod p) * ↑n
      + (26894631634706989992115336946156599071555735384089111478534775845557834998994
        : ZMod p) = 0 := by
    linear_combination hgx
  -- combine: 1 = 0 in ZMod p, contradiction
  have hone : (1 : ZMod p) = 0 := by
    linear_combination
      ((10714705466783398919153788324387207784993784905826990448772425602556871707829
          : ZMod p) * ↑n
        + (57235417221613563794669871010566018951260221108442596502766824992869568682169
          : ZMod p)) * hFf
      + ((33876748068821087438090232889582374565686159768566685920920121567467009425787
          : ZMod p) * (↑n : ZMod p) ^ 2
        + (50650572635476552433305898559462997992770685948553974631914612199262475541230
          : ZMod p) * ↑n
        + (13923668626353120404886080384319955949384710940522404749921965605415382174961
          : ZMod p)) * hHf
      - hcast
  exact one_ne_zero hone

/-- **Selene has no 2-torsion**: no `(x, y)` with `y^2 = x^3 - 3x + B` has `y = 0`. -/
theorem no_two_torsion (x y : ZMod p) (h : y ^ 2 = x ^ 3 - 3 * x + (Bcurve : ZMod p)) :
    y ≠ 0 := by
  rintro rfl
  exact cubic_no_root x (by linear_combination -h)

end Selene

end HelioseleneSpec
