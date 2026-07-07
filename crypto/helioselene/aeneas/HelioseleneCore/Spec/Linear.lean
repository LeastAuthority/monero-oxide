/- Spec lemmas for the "linear" field operations: `red1`, `add`, `double`, `sub`, `neg`,
   `is_zero`, `is_odd`.

   Everything in this file is PROVED (no `sorry`, no new axioms, no `native_decide`);
   exported lemmas that mention the generated hex-string constants transitively inherit
   the pre-existing `<const>._native.decide.ax_1` axioms baked into Funs.lean
   (see README §5c). -/
import HelioseleneCore.Spec.Phi

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Aeneas Aeneas.Std Result ControlFlow
open helioselene

namespace HelioseleneSpec

open crypto_bigint.uint crypto_bigint.limb HelioseleneModel

/-! ## Generic helpers -/

private theorem nat_or_eq_zero_iff (a b : ℕ) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact ⟨Nat.le_antisymm (h ▸ Nat.left_le_or) (Nat.zero_le _),
           Nat.le_antisymm (h ▸ Nat.right_le_or) (Nat.zero_le _)⟩
  · rintro ⟨rfl, rfl⟩; rfl

private theorem limb_eq_of_val_eq {a b : Limb} (h : a.val = b.val) : a = b :=
  (UScalar.eq_equiv a b).2 h

private theorem limb_lt (a : Limb) : a.val < 2^64 := a.hBounds

/-- 2p < 2^256 (so sums of reduced elements never wrap). -/
private theorem two_p_lt : 2 * p < 2^256 := by
  have := p_lt_two_pow_255
  omega

private theorem pow_64_4 : 2^(64 * (4#usize).val) = 2^256 := by
  rw [usize4_val]

/-! ## The 4-limb view of a `Uint4` -/

private theorem list_len4 {α : Type u} (l : List α) (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  cases l with
  | nil => simp at h
  | cons a l =>
  cases l with
  | nil => simp at h
  | cons b l =>
  cases l with
  | nil => simp at h
  | cons c l =>
  cases l with
  | nil => simp at h
  | cons d l =>
  cases l with
  | nil => exact ⟨a, b, c, d, rfl⟩
  | cons e l => simp at h

theorem Uint4.length_val (u : Uint4) : u.val.length = 4 := by
  scalar_tac

/-- Every `Uint4` is a list of exactly four limbs. -/
theorem Uint4.exists_limbs (u : Uint4) :
    ∃ l0 l1 l2 l3 : Limb, u.val = [l0, l1, l2, l3] :=
  list_len4 u.val (Uint4.length_val u)

/-- `toNat` as an explicit weighted sum of the four limbs. -/
theorem Uint4.toNat_limbs (u : Uint4) {l0 l1 l2 l3 : Limb} (h : u.val = [l0, l1, l2, l3]) :
    u.toNat = l0.val + 2^64 * l1.val + 2^128 * l2.val + 2^192 * l3.val := by
  show u.val.foldr (fun (l : Std.U64) acc => acc * 2^64 + l.val) 0 = _
  rw [h]
  simp only [List.foldr_cons, List.foldr_nil]
  ring

/-- Two `Uint4`s with the same limbs (via `getElem!`) are equal. -/
theorem Uint4.ext_getElem! (u v : Uint4)
    (h : ∀ j : ℕ, j < 4 → u.val[j]! = v.val[j]!) : u = v := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [Uint4.length_val, Uint4.length_val])
  intro i h1 h2
  have hi : i < 4 := by rwa [Uint4.length_val] at h1
  have := h i hi
  rwa [getElem!_pos u.val i h1, getElem!_pos v.val i h2] at this

/-- `toNat = 0` iff all four limbs are zero. -/
theorem Uint4.toNat_eq_zero_iff (u : Uint4) :
    u.toNat = 0 ↔ ∀ j : ℕ, j < 4 → u.val[j]!.val = 0 := by
  obtain ⟨l0, l1, l2, l3, h⟩ := Uint4.exists_limbs u
  rw [Uint4.toNat_limbs u h]
  constructor
  · intro hz j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl <;> simp [h] <;> omega
  · intro hall
    have h0 := hall 0 (by omega)
    have h1 := hall 1 (by omega)
    have h2 := hall 2 (by omega)
    have h3 := hall 3 (by omega)
    simp [h] at h0 h1 h2 h3
    omega

/-! ## `select_word` -/

/-- `select_word` computed (everything in it is pure). -/
private theorem select_word_eq (x y mask : Limb) :
    field.verified.select_word x y mask
      = ok ⟨x.bv ^^^ ((x.bv ^^^ y.bv) &&& mask.bv)⟩ := rfl

theorem select_word_val (x y mask : Limb) :
    ∃ r, field.verified.select_word x y mask = ok r
      ∧ r.val = x.val ^^^ ((x.val ^^^ y.val) &&& mask.val) := by
  refine ⟨_, select_word_eq x y mask, ?_⟩
  show (x.bv ^^^ ((x.bv ^^^ y.bv) &&& mask.bv)).toNat = _
  rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_xor]
  rfl

/-- With a 0/all-ones mask, `select_word` selects `x` (mask 0) or `y` (mask all-ones). -/
theorem select_word_spec (x y mask : Limb) (h : mask.val = 0 ∨ mask.val = 2^64 - 1) :
    field.verified.select_word x y mask
      ⦃ r => r = if mask.val = 0 then x else y ⦄ := by
  obtain ⟨r, heq, hval⟩ := select_word_val x y mask
  rw [heq, Aeneas.Std.WP.spec_ok]
  rcases h with h | h
  · rw [if_pos h]
    apply limb_eq_of_val_eq
    rw [hval, h]
    simp
  · have hne : mask.val ≠ 0 := by rw [h]; positivity
    rw [if_neg hne]
    apply limb_eq_of_val_eq
    have hxy : x.val ^^^ y.val < 2^64 := Nat.xor_lt_two_pow (limb_lt x) (limb_lt y)
    rw [hval, h, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hxy,
        ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-! ## `sub_value` -/

/-- `sub_value a b` = exact 256-bit subtraction with an all-ones/zero underflow mask. -/
theorem sub_value_spec (a b : Uint4) :
    field.verified.sub_value a b
      ⦃ d bo => (if a.toNat < b.toNat
                 then d.toNat + b.toNat = a.toNat + 2^256 ∧ bo.val = 2^64 - 1
                 else d.toNat + b.toNat = a.toNat ∧ bo.val = 0) ⦄ := by
  unfold field.verified.sub_value
  step as ⟨l, hl⟩
  have h63 : l.val >>> 63 = 0 := by simp [hl]
  apply WP.spec_mono (Uint.sbb_spec a b l)
  intro (d, bo) hd
  rw [h63, Nat.add_zero, pow_64_4] at hd
  exact hd

/-! ## List `set`/`getElem!` helpers -/

private theorem list_getElem!_set_self {α} [Inhabited α] (l : List α) (i : ℕ) (x : α)
    (h : i < l.length) : (l.set i x)[i]! = x := by
  rw [getElem!_pos (l.set i x) i (by simpa using h)]
  exact List.getElem_set_self _

private theorem list_getElem!_set_ne {α} [Inhabited α] (l : List α) (i j : ℕ) (x : α)
    (hne : i ≠ j) (hj : j < l.length) : (l.set i x)[j]! = l[j]! := by
  rw [getElem!_pos (l.set i x) j (by simpa using hj), getElem!_pos l j hj]
  exact List.getElem_set_ne hne _

/-! ## The `red1` select loop -/

/-- The conditional-move loop of `red1` assembles `c` (the value selected limbwise by the
    mask `borrow`, i.e. `reduced` on mask 0 and `a` on mask all-ones). -/
theorem red1_loop_spec (a reduced : Uint4) (borrow : Limb) (c : Uint4)
    (hmask : borrow.val = 0 ∨ borrow.val = 2^64 - 1)
    (hc : ∀ j : ℕ, j < 4 →
      (if borrow.val = 0 then reduced.val[j]! else a.val[j]!) = c.val[j]!)
    (it : core.ops.range.Range Std.Usize) (out : Uint4)
    (hend : it.«end».val = 4) (hstart : it.start.val ≤ 4)
    (hpart : ∀ j : ℕ, j < it.start.val → out.val[j]! = c.val[j]!) :
    field.verified.red1_loop it a reduced borrow out ⦃ r => r = c ⦄ := by
  unfold field.verified.red1_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (st : core.ops.range.Range Std.Usize × Uint4) => 4 - st.1.start.val)
    (inv := fun st => st.1.«end».val = 4 ∧ st.1.start.val ≤ 4 ∧
       ∀ j : ℕ, j < st.1.start.val → st.2.val[j]! = c.val[j]!)
  · rintro ⟨it1, out1⟩ ⟨he, hs, hp⟩
    dsimp only at he hs hp ⊢
    unfold field.verified.red1_loop.body
    step as ⟨o, it2, ho, hoend⟩
    split at ho
    · -- some case: `it1.start < it1.end`
      rename_i hlt
      obtain ⟨ho1, hstart2⟩ := ho
      simp only [ho1]
      have hj4 : it1.start.val < 4 := by omega
      step as ⟨a1, ha1⟩
      subst ha1
      step as ⟨l, hlv⟩
      step as ⟨a2, ha2⟩
      subst ha2
      step as ⟨l1, hl1v⟩
      step with select_word_spec l l1 borrow hmask as ⟨l2, hl2⟩
      step as ⟨a3, back, ha3, hback⟩
      subst ha3
      step as ⟨a4, ha4⟩
      subst ha4
      simp only [hback]
      refine ⟨by rw [hoend]; exact he, by omega, ?_, by omega⟩
      intro j hj
      rw [hstart2] at hj
      rw [Aeneas.Std.Array.set_val_eq]
      by_cases hje : j = it1.start.val
      · subst hje
        rw [list_getElem!_set_self _ _ _ (by scalar_tac)]
        rw [hl2, hlv, hl1v]
        have hcc := hc it1.start.val hj4
        rw [getElem!_pos a1.val it1.start.val (by scalar_tac),
            getElem!_pos a2.val it1.start.val (by scalar_tac)] at hcc
        exact hcc
      · rw [list_getElem!_set_ne _ _ _ _ (fun h => hje h.symm) (by scalar_tac)]
        exact hp j (by omega)
    · -- none case: the range is exhausted
      rename_i hge
      obtain ⟨ho1, hstart2⟩ := ho
      simp only [ho1, Aeneas.Std.WP.spec_ok]
      have h4 : it1.start.val = 4 := by omega
      apply Uint4.ext_getElem!
      intro j hj
      exact hp j (by omega)
  · exact ⟨hend, hstart, hpart⟩

/-! ## `red1` -/

/-- `red1` on inputs below `2p` computes the canonical representative mod `p`. -/
theorem red1_spec (a : Uint4) (h2p : a.toNat < 2 * p) :
    field.verified.red1 a ⦃ r => r.toNat = a.toNat % p ⦄ := by
  unfold field.verified.red1
  step as ⟨u, hu⟩
  step with sub_value_spec as ⟨reduced, borrow, hrb⟩
  step as ⟨out0, hout0⟩
  step as ⟨i, hi⟩
  simp only [hi]
  rw [hu] at hrb
  split at hrb
  · -- a < p: the trial subtraction underflowed, the loop reassembles `a`
    rename_i hlt
    obtain ⟨hred, hbo⟩ := hrb
    have hloop := red1_loop_spec a reduced borrow a (Or.inr hbo)
      (fun j hj => by rw [if_neg (by rw [hbo]; omega)])
      { start := 0#usize, «end» := 4#usize } out0
      (by simp) (by simp) (by intro j hj; simp at hj)
    apply WP.spec_mono hloop
    intro r hr
    rw [hr, Nat.mod_eq_of_lt hlt]
  · -- p ≤ a < 2p: the loop returns `reduced = a - p`
    rename_i hge
    obtain ⟨hred, hbo⟩ := hrb
    have hloop := red1_loop_spec a reduced borrow reduced (Or.inl hbo)
      (fun j hj => by rw [if_pos hbo])
      { start := 0#usize, «end» := 4#usize } out0
      (by simp) (by simp) (by intro j hj; simp at hj)
    apply WP.spec_mono hloop
    intro r hr
    rw [hr, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- `red1` is `ok` on inputs below `2p` and reduces mod `p`. -/
theorem red1_ok (a : Uint4) (h : a.toNat < 2 * p) :
    ∃ r, field.verified.red1 a = .ok r ∧ r.toNat = a.toNat % p :=
  WP.spec_imp_exists (red1_spec a h)

/-! ## `add` -/

theorem add_spec (a b : Uint4) (ha : a.toNat < p) (hb : b.toNat < p) :
    field.HelioseleneField.Insts.CoreOpsArithAddHelioseleneFieldHelioseleneField.add a b
      ⦃ r => r.toNat = (a.toNat + b.toNat) % p ⦄ := by
  unfold field.HelioseleneField.Insts.CoreOpsArithAddHelioseleneFieldHelioseleneField.add
  have h2 := two_p_lt
  step as ⟨u, hu⟩
  have hu' : u.toNat = a.toNat + b.toNat := by
    rw [hu]; apply Nat.mod_eq_of_lt; omega
  step with red1_spec u (by omega) as ⟨u1, hu1⟩
  simp only [hu1, hu']

/-- Modular addition: `ok`, and the value is `(a + b) mod p`. -/
theorem add_ok (a b : Uint4) (ha : a.toNat < p) (hb : b.toNat < p) :
    ∃ r, field.HelioseleneField.Insts.CoreOpsArithAddHelioseleneFieldHelioseleneField.add a b
        = .ok r ∧ r.toNat = (a.toNat + b.toNat) % p :=
  WP.spec_imp_exists (add_spec a b ha hb)

/-! ## `double` -/

private theorem shl1_spec (a : Uint4) :
    crypto_bigint.uint.shl.Uint.shl_vartime a 1#usize
      ⦃ r => r.toNat = (2 * a.toNat) % 2^256 ⦄ := by
  obtain ⟨u, heq, hu⟩ := Uint4.shl_vartime_one_ok a
  rw [heq, Aeneas.Std.WP.spec_ok]
  exact hu

theorem double_spec (a : Uint4) (ha : a.toNat < p) :
    field.verified.double a ⦃ r => r.toNat = (2 * a.toNat) % p ⦄ := by
  unfold field.verified.double
  have h2 := two_p_lt
  step with shl1_spec a as ⟨u, hu⟩
  have hu' : u.toNat = 2 * a.toNat := by
    rw [hu]; apply Nat.mod_eq_of_lt; omega
  step with red1_spec u (by omega) as ⟨u1, hu1⟩
  simp only [hu1, hu']

/-- Field doubling: `ok`, and the value is `(2a) mod p`. -/
theorem double_ok (a : Uint4) (ha : a.toNat < p) :
    ∃ r, field.verified.double a = .ok r ∧ r.toNat = (2 * a.toNat) % p :=
  WP.spec_imp_exists (double_spec a ha)

/-! ## `sub` -/

/-- The select loop of field subtraction assembles `c` (the value selected limbwise by the
    mask `underflowed`, i.e. `candidate` on mask 0 and `plus_modulus` on mask all-ones). -/
theorem sub_loop_spec (candidate plus_modulus : Uint4) (underflowed : Limb) (c : Uint4)
    (hmask : underflowed.val = 0 ∨ underflowed.val = 2^64 - 1)
    (hc : ∀ j : ℕ, j < 4 →
      (if underflowed.val = 0 then candidate.val[j]! else plus_modulus.val[j]!) = c.val[j]!)
    (it : core.ops.range.Range Std.Usize) (out : Uint4)
    (hend : it.«end».val = 4) (hstart : it.start.val ≤ 4)
    (hpart : ∀ j : ℕ, j < it.start.val → out.val[j]! = c.val[j]!) :
    field.HelioseleneField.Insts.CoreOpsArithSubHelioseleneFieldHelioseleneField.sub_loop
      it candidate underflowed plus_modulus out ⦃ r => r = c ⦄ := by
  unfold field.HelioseleneField.Insts.CoreOpsArithSubHelioseleneFieldHelioseleneField.sub_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (st : core.ops.range.Range Std.Usize × Uint4) => 4 - st.1.start.val)
    (inv := fun st => st.1.«end».val = 4 ∧ st.1.start.val ≤ 4 ∧
       ∀ j : ℕ, j < st.1.start.val → st.2.val[j]! = c.val[j]!)
  · rintro ⟨it1, out1⟩ ⟨he, hs, hp⟩
    dsimp only at he hs hp ⊢
    unfold
      field.HelioseleneField.Insts.CoreOpsArithSubHelioseleneFieldHelioseleneField.sub_loop.body
    step as ⟨o, it2, ho, hoend⟩
    split at ho
    · -- some case: `it1.start < it1.end`
      rename_i hlt
      obtain ⟨ho1, hstart2⟩ := ho
      simp only [ho1]
      have hj4 : it1.start.val < 4 := by omega
      step as ⟨a1, ha1⟩
      subst ha1
      step as ⟨l, hlv⟩
      step as ⟨a2, ha2⟩
      subst ha2
      step as ⟨l1, hl1v⟩
      step with select_word_spec l l1 underflowed hmask as ⟨l2, hl2⟩
      step as ⟨a3, back, ha3, hback⟩
      subst ha3
      step as ⟨a4, ha4⟩
      subst ha4
      simp only [hback]
      refine ⟨by rw [hoend]; exact he, by omega, ?_, by omega⟩
      intro j hj
      rw [hstart2] at hj
      rw [Aeneas.Std.Array.set_val_eq]
      by_cases hje : j = it1.start.val
      · subst hje
        rw [list_getElem!_set_self _ _ _ (by scalar_tac)]
        rw [hl2, hlv, hl1v]
        have hcc := hc it1.start.val hj4
        rw [getElem!_pos a1.val it1.start.val (by scalar_tac),
            getElem!_pos a2.val it1.start.val (by scalar_tac)] at hcc
        exact hcc
      · rw [list_getElem!_set_ne _ _ _ _ (fun h => hje h.symm) (by scalar_tac)]
        exact hp j (by omega)
    · -- none case: the range is exhausted
      rename_i hge
      obtain ⟨ho1, hstart2⟩ := ho
      simp only [ho1, Aeneas.Std.WP.spec_ok]
      have h4 : it1.start.val = 4 := by omega
      apply Uint4.ext_getElem!
      intro j hj
      exact hp j (by omega)
  · exact ⟨hend, hstart, hpart⟩

theorem sub_spec (a b : Uint4) (ha : a.toNat < p) (hb : b.toNat < p) :
    field.HelioseleneField.Insts.CoreOpsArithSubHelioseleneFieldHelioseleneField.sub a b
      ⦃ r => r.toNat = (a.toNat + (p - b.toNat)) % p ⦄ := by
  unfold field.HelioseleneField.Insts.CoreOpsArithSubHelioseleneFieldHelioseleneField.sub
  have h2 := two_p_lt
  have hppos := p_pos
  step with sub_value_spec a b as ⟨pv, hcu⟩
  step with MODULUS_spec as ⟨u, hu⟩
  obtain ⟨candidate, underflowed⟩ := pv
  simp only at hcu ⊢
  step as ⟨plus_modulus, hpm⟩
  step as ⟨out0, hout0⟩
  step as ⟨i, hi⟩
  simp only [hi]
  rw [hu, show (2:ℕ)^(64 * 4) = 2^256 from by norm_num] at hpm
  split at hcu
  · -- a < b: underflow, the result is `candidate + p` (which wrapped back into range)
    rename_i hlt
    obtain ⟨hcand, hbo⟩ := hcu
    have hpmv : plus_modulus.toNat = a.toNat + (p - b.toNat) := by
      rw [hpm]
      have : candidate.toNat + p = (a.toNat + (p - b.toNat)) + 2^256 := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hloop := sub_loop_spec candidate plus_modulus underflowed plus_modulus
      (Or.inr hbo) (fun j hj => by rw [if_neg (by rw [hbo]; omega)])
      { start := 0#usize, «end» := 4#usize } out0
      (by simp) (by simp) (by intro j hj; simp at hj)
    step with hloop as ⟨r, hr⟩
    rw [hr, hpmv, Nat.mod_eq_of_lt (by omega)]
  · -- b ≤ a: no underflow, the result is the raw difference `candidate`
    rename_i hge
    obtain ⟨hcand, hbo⟩ := hcu
    have hloop := sub_loop_spec candidate plus_modulus underflowed candidate
      (Or.inl hbo) (fun j hj => by rw [if_pos hbo])
      { start := 0#usize, «end» := 4#usize } out0
      (by simp) (by simp) (by intro j hj; simp at hj)
    step with hloop as ⟨r, hr⟩
    have hval : a.toNat + (p - b.toNat) = candidate.toNat + p := by omega
    rw [hr, hval, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Modular subtraction: `ok`, and the value is `(a + (p - b)) mod p` (= `(a - b) mod p`). -/
theorem sub_ok (a b : Uint4) (ha : a.toNat < p) (hb : b.toNat < p) :
    ∃ r, field.HelioseleneField.Insts.CoreOpsArithSubHelioseleneFieldHelioseleneField.sub a b
        = .ok r ∧ r.toNat = (a.toNat + (p - b.toNat)) % p :=
  WP.spec_imp_exists (sub_spec a b ha hb)

/-! ## `is_zero` -/

/-- The OR-fold loop of `is_zero`: the accumulator is zero iff all visited limbs are zero. -/
theorem is_zero_loop_spec (value : Uint4) (it : core.ops.range.Range Std.Usize) (all : Limb)
    (hend : it.«end».val = 4) (hstart : it.start.val ≤ 4)
    (hall : all.val = 0 ↔ ∀ j : ℕ, j < it.start.val → value.val[j]!.val = 0) :
    field.verified.is_zero_loop it value all
      ⦃ r => r.val = 0 ↔ ∀ j : ℕ, j < 4 → value.val[j]!.val = 0 ⦄ := by
  unfold field.verified.is_zero_loop
  apply Aeneas.Std.loop.spec_decr_nat
    (measure := fun (st : core.ops.range.Range Std.Usize × field.HelioseleneField × Limb) =>
      4 - st.1.start.val)
    (inv := fun st => st.2.1 = value ∧ st.1.«end».val = 4 ∧ st.1.start.val ≤ 4 ∧
       (st.2.2.val = 0 ↔ ∀ j : ℕ, j < st.1.start.val → value.val[j]!.val = 0))
  · rintro ⟨it1, v1, all1⟩ ⟨hv, he, hs, hiv⟩
    dsimp only at hv he hs hiv ⊢
    subst hv
    unfold field.verified.is_zero_loop.body
    step as ⟨o, it2, ho, hoend⟩
    split at ho
    · -- some case
      rename_i hlt
      obtain ⟨ho1, hstart2⟩ := ho
      simp only [ho1]
      have hj4 : it1.start.val < 4 := by omega
      step as ⟨a1, ha1⟩
      subst ha1
      step as ⟨l, hlv⟩
      step as ⟨all2, hall2⟩
      have hl! : l = a1.val[it1.start.val]! := by
        rw [getElem!_pos a1.val it1.start.val (by scalar_tac)]; exact hlv
      refine ⟨by rw [hoend]; exact he, by omega, ?_, by omega⟩
      rw [hall2, nat_or_eq_zero_iff, hiv, hstart2]
      constructor
      · rintro ⟨hprev, hl0⟩ j hj
        by_cases hje : j = it1.start.val
        · subst hje; rw [← hl!]; exact hl0
        · exact hprev j (by omega)
      · intro hall0
        exact ⟨fun j hj => hall0 j (by omega),
               by rw [hl!]; exact hall0 it1.start.val (by omega)⟩
    · -- none case
      rename_i hge
      obtain ⟨ho1, hstart2⟩ := ho
      simp only [ho1, Aeneas.Std.WP.spec_ok]
      have h4 : it1.start.val = 4 := by omega
      rw [h4] at hiv
      exact hiv
  · exact ⟨rfl, hend, hstart, hall⟩

theorem is_zero_spec (a : Uint4) :
    field.verified.is_zero a ⦃ c => c = true ↔ a.toNat = 0 ⦄ := by
  unfold field.verified.is_zero
  step as ⟨all, hall⟩
  step as ⟨i, hi⟩
  simp only [hi]
  have hloop := is_zero_loop_spec a { start := 0#usize, «end» := 4#usize } all
    (by simp) (by simp) (by simp [hall])
  step with hloop as ⟨all1, hall1⟩
  apply WP.spec_mono (Limb.ct_eq_spec all1 all)
  intro cres hcres
  rw [hcres, hall, hall1, ← Uint4.toNat_eq_zero_iff]

/-- Constant-time zero test: `ok`, and true iff the value is zero. -/
theorem is_zero_ok (a : Uint4) :
    ∃ c, field.verified.is_zero a = .ok c ∧ (c = true ↔ a.toNat = 0) :=
  WP.spec_imp_exists (is_zero_spec a)

private theorem FfField_is_zero_spec (a : Uint4) :
    field.HelioseleneField.Insts.FfField.is_zero a ⦃ c => c = true ↔ a.toNat = 0 ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.is_zero
  exact is_zero_spec a

/-! ## `neg` -/

private theorem FfField_ZERO_spec :
    field.HelioseleneField.Insts.FfField.ZERO ⦃ z => Uint.toNat z = 0 ⦄ := by
  unfold field.HelioseleneField.Insts.FfField.ZERO
  step as ⟨u, hu⟩
  exact hu

theorem neg_spec (a : Uint4) (ha : a.toNat < p) :
    field.HelioseleneField.Insts.CoreOpsArithNegHelioseleneField.neg a
      ⦃ r => r.toNat = (p - a.toNat) % p ⦄ := by
  unfold field.HelioseleneField.Insts.CoreOpsArithNegHelioseleneField.neg
  have hppos := p_pos
  have hplt := p_lt
  step with MODULUS_spec as ⟨u, hu⟩
  step as ⟨u1, hu1⟩
  have hu1' : u1.toNat = p - a.toNat := by
    rw [hu1, hu, show (2:ℕ)^(64 * 4) = 2^256 from by norm_num]
    have : p + 2^256 - a.toNat = (p - a.toNat) + 2^256 := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  step with FfField_ZERO_spec as ⟨hf, hhf⟩
  step with FfField_is_zero_spec a as ⟨c, hc⟩
  unfold field.HelioseleneField.Insts.SubtleConditionallySelectable.conditional_select
  step as ⟨rsel, hrsel⟩
  by_cases haz : a.toNat = 0
  · have hct : c = true := hc.mpr haz
    simp [hrsel, hct, hhf, haz, Nat.mod_self]
  · have hcf : c = false := by
      cases c with
      | false => rfl
      | true => exact absurd (hc.mp rfl) haz
    simp only [hrsel, hcf, Bool.false_eq_true, ite_false]
    rw [hu1', Nat.mod_eq_of_lt (by omega)]

/-- Field negation: `ok`, and the value is `(p - a) mod p`. -/
theorem neg_ok (a : Uint4) (ha : a.toNat < p) :
    ∃ r, field.HelioseleneField.Insts.CoreOpsArithNegHelioseleneField.neg a = .ok r
      ∧ r.toNat = (p - a.toNat) % p :=
  WP.spec_imp_exists (neg_spec a ha)

/-! ## `is_odd` -/

theorem is_odd_spec (a : Uint4) :
    field.verified.is_odd a ⦃ c => c = true ↔ a.toNat % 2 = 1 ⦄ := by
  obtain ⟨l0, l1, l2, l3, hl⟩ := Uint4.exists_limbs a
  unfold field.verified.is_odd
  step as ⟨arr, harr⟩
  subst harr
  step as ⟨l, hlv⟩
  step as ⟨i, hiv, hibv⟩
  step as ⟨i1, hi1⟩
  apply WP.spec_mono (Choice.from_spec i1)
  intro c hc
  rw [hc]
  -- `l` is the least-significant limb
  simp only [hl, List.getElem_cons_zero] at hlv
  -- `i = l₀ & 1 = l₀ % 2`
  have hi' : i.val = l0.val % 2 := by
    rw [hiv]
    have hand : (l &&& 1#u64).val = l.val &&& (1#u64).val := by
      show (l.bv &&& (1#u64).bv).toNat = _
      rw [BitVec.toNat_and]
      rfl
    rw [hand, show (1#u64).val = 1 from by simp, Nat.and_one_is_mod, hlv]
  -- the cast to `U8` is exact (the value is 0 or 1)
  have hi1v : i1.val = l0.val % 2 := by
    rw [hi1, UScalar.cast_val_eq]
    simp only [UScalarTy.U8_numBits_eq]
    rw [hi']
    omega
  have ht := Uint4.toNat_limbs arr hl
  rw [hi1v]
  omega


/-- Constant-time parity test: `ok`, and true iff the canonical value is odd. -/
theorem is_odd_ok (a : Uint4) :
    ∃ c, field.verified.is_odd a = .ok c ∧ (c = true ↔ a.toNat % 2 = 1) :=
  WP.spec_imp_exists (is_odd_spec a)

end HelioseleneSpec
