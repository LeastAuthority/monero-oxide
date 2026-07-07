/- The abstraction layer: reduced representatives `HField`, the little-endian byte
   value `leVal`, and the bijection `φ : HField ≃ ZMod p` with the mathlib side.

   Everything in this file is PROVED (no `sorry`, no new axioms, no `native_decide`);
   exported lemmas that mention the generated hex-string constants transitively inherit
   the pre-existing `<const>._native.decide.ax_1` axioms baked into Funs.lean
   (see README §5c). -/
import HelioseleneCore.Spec.Externals
import Mathlib.Data.ZMod.Basic

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result
open helioselene

namespace HelioseleneSpec

open crypto_bigint.uint HelioseleneModel

/-! ## The prime (re-exported facts)

`p`, `p_pos`, `one_lt_p`, `p_lt` are defined/proved in `Spec.Externals`
(`HelioseleneSpec.p` etc.) since the constant lemmas there already need them. -/

example : 0 < p := p_pos
example : 1 < p := one_lt_p
example : p < 2^256 := p_lt

instance : NeZero p := ⟨Nat.pos_iff_ne_zero.mp p_pos⟩

instance : Fact (1 < p) := ⟨one_lt_p⟩

/-! ## Little-endian byte values -/

/-- The natural number denoted by a little-endian byte array. -/
def leVal {n : Usize} (bytes : Aeneas.Std.Array Std.U8 n) : ℕ :=
  leBytesToNat bytes.val

theorem leVal_eq_leBytesToNat {n : Usize} (bytes : Aeneas.Std.Array Std.U8 n) :
    leVal bytes = leBytesToNat bytes.val := rfl

theorem leVal_eq_digitsVal {n : Usize} (bytes : Aeneas.Std.Array Std.U8 n) :
    leVal bytes = digitsVal 8 (bytes.val.map UScalar.val) :=
  leBytesToNat_eq_digitsVal bytes.val

/-- `leVal` of an `n`-byte array is below `2^(8·n)`. -/
theorem leVal_lt {n : Usize} (bytes : Aeneas.Std.Array Std.U8 n) :
    leVal bytes < 2^(8 * n.val) := by
  have h := leBytesToNat_lt bytes.val
  rwa [Aeneas.Std.Array.length_eq] at h

/-- `leVal` of a 32-byte array is below `2^256`. -/
theorem leVal_lt_2_256 (bytes : Aeneas.Std.Array Std.U8 32#usize) :
    leVal bytes < 2^256 := by
  have h := leVal_lt bytes
  rwa [show (32#usize).val = 32 from by simp,
       show 8 * 32 = 256 from by norm_num] at h

/-! ## `HField`: reduced field-element representatives -/

/-- The subtype of `Uint4` values that are reduced modulo `p` — the abstract carrier
    of the Helioselene field. -/
def HField := { u : Uint4 // u.toNat < p }

instance : DecidableEq HField :=
  inferInstanceAs (DecidableEq { u : Uint4 // u.toNat < p })

/-! ## The bijection with `ZMod p` -/

/-- The abstraction map into mathlib's `ZMod p`. -/
def φ (x : HField) : ZMod p := (x.val.toNat : ZMod p)

/-- The concretization map: a `ZMod p` value to its (reduced) 4-limb representative. -/
def ofZMod (z : ZMod p) : HField :=
  ⟨Uint.ofNat 4#usize z.val, by
    rw [Uint4.toNat_ofNat (lt_trans (ZMod.val_lt z) p_lt)]
    exact ZMod.val_lt z⟩

theorem ofZMod_val (z : ZMod p) : (ofZMod z).val.toNat = z.val :=
  Uint4.toNat_ofNat (lt_trans (ZMod.val_lt z) p_lt)

theorem φ_val (x : HField) : (φ x).val = x.val.toNat :=
  ZMod.val_cast_of_lt x.property

/-- `HField` is in bijection with `ZMod p`. -/
def equivZMod : HField ≃ ZMod p where
  toFun := φ
  invFun := ofZMod
  left_inv x := by
    apply Subtype.ext
    show Uint.ofNat 4#usize (φ x).val = x.val
    rw [φ_val, Uint.ofNat_toNat]
  right_inv z := by
    show ((ofZMod z).val.toNat : ZMod p) = z
    rw [ofZMod_val]
    exact ZMod.natCast_rightInverse z

@[simp] theorem equivZMod_apply (x : HField) : equivZMod x = φ x := rfl

@[simp] theorem equivZMod_symm_apply (z : ZMod p) : equivZMod.symm z = ofZMod z := rfl

theorem φ_injective : Function.Injective φ := equivZMod.injective

theorem φ_surjective : Function.Surjective φ := equivZMod.surjective

theorem φ_bijective : Function.Bijective φ := equivZMod.bijective

/-- `φ` respects `toNat` congruence: two reduced representatives with the same value
    mod `p` are equal. -/
theorem φ_eq_iff (x y : HField) : φ x = φ y ↔ x = y :=
  ⟨fun h => φ_injective h, fun h => h ▸ rfl⟩

/-! ## Finiteness -/

noncomputable instance : Fintype HField := Fintype.ofEquiv _ equivZMod.symm

instance : Finite HField := Finite.of_equiv _ equivZMod.symm

theorem card_hfield : Fintype.card HField = p := by
  rw [Fintype.card_congr equivZMod, ZMod.card]

end HelioseleneSpec
