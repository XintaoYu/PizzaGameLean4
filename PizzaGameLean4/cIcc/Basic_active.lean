import Mathlib.Tactic

/-
Update 03/25/25

There are some big modifications in this version.

We develop `Turns` with different lengths, instead of just `Fin (n + 1) → Fin (n + 1)`
-/

set_option autoImplicit false

section FinCircular

variable {n : ℕ}

/--
Instance of circular order on `Fin (n + 1)`.
-/
instance Fin.instCircularOrder : CircularOrder (Fin (n + 1)) := {
  btw := fun a b c =>
    if a < c then
      a ≤ b ∧ b ≤ c
    else if c < a then
      a ≤ b ∨ b ≤ c
    else
      True
  sbtw := fun a b c =>
    if a < c then
      a < b ∧ b < c
    else if c < a then
      a < b ∨ b < c
    else
      False
  btw_refl := fun a => by
    simp only [btw]
    repeat rw [if_neg (lt_irrefl _)]
    exact trivial
  btw_cyclic_left := @fun a b c h => by
    simp only [btw] at *
    split at h
    · next h₁ =>
      rw [if_neg (not_lt_of_le h.left)]
      split
      · exact Or.inl h.right
      · exact trivial
    split at h
    · next h₁ h₂ =>
      split
      · next h₃ =>
        constructor
        · match h with
          | Or.inl h₄ =>
            exact False.elim <| not_lt_of_le h₄ <| h₃
          | Or.inr h₄ =>
            exact h₄
        · exact le_of_not_lt h₁
      split
      · exact Or.inr <| le_of_lt h₂
      · exact trivial
    · next h₁ h₂ =>
      apply le_of_not_lt at h₁
      apply le_of_not_lt at h₂
      have eq : a = c := le_antisymm h₂ h₁
      split
      · next h₃ =>
        exact ⟨le_of_lt (eq ▸ h₃), le_of_eq eq.symm⟩
      split
      · exact Or.inr <| le_of_eq eq.symm
      · exact trivial
  sbtw_iff_btw_not_btw := @fun a b c => by
    simp only [btw, sbtw] at *
    constructor <;> intro h
    · if h₁ : a < c then
        constructor
        · rw [if_pos h₁] at *
          exact ⟨le_of_lt h.left, le_of_lt h.right⟩
        · rw [if_pos h₁] at h
          rw [if_neg (not_lt_of_lt h₁), if_pos h₁]
          push_neg
          exact h.symm
      else if h₂ : c < a then
        constructor
        · rw [if_neg h₁, if_pos h₂] at *
          refine Or.elim h ?_ ?_
          · exact Or.inl ∘ le_of_lt
          · exact Or.inr ∘ le_of_lt
        · rw [if_neg h₁, if_pos h₂] at h
          rw [if_pos h₂]
          push_neg
          refine Or.elim h ?_ ?_
          · exact fun g _ => g
          · exact fun f g => False.elim <| not_lt_of_le g f
      else
        repeat rw [if_neg h₁, if_neg h₂] at *
        exact False.elim h
    · if h₁ : a < c then
        repeat rw [if_neg (not_lt_of_lt h₁), if_pos h₁] at h
        push_neg at h
        rw [if_pos h₁]
        exact h.right.symm
      else if h₂ : c < a then
        repeat rw [if_neg h₁, if_pos h₂] at h
        push_neg at h
        rw [if_neg h₁, if_pos h₂]
        if h₃ : b < c then
          exact Or.inr h₃
        else
          exact Or.inl <| h.right <| le_of_not_lt h₃
      else
        repeat rw [if_neg h₁, if_neg h₂] at *
        exact not_true.mp h.right
  sbtw_trans_left := @fun a b c d h₁ h₂ => by
    simp only [sbtw] at *
    if h₃ : a < c then
      rw [if_pos h₃] at *
      rw [if_pos h₁.right] at h₂
      exact ⟨lt_trans h₁.left h₂.left, h₂.right⟩
    else if h₄ : c < a then
      rw [if_neg h₃, if_pos h₄] at *
      refine Or.elim h₁ ?_ ?_ <;> intro h₅
      · rw [if_neg (not_lt_of_lt <| lt_trans h₄ h₅), if_pos (lt_trans h₄ h₅)] at h₂
        refine Or.elim h₂ ?_ ?_
        · exact fun g => Or.inl <| lt_trans h₅ g
        · exact fun g => Or.inr g
      · rw [if_pos h₅] at h₂
        exact Or.inr h₂.right
    else
      rw [if_neg h₃, if_neg h₄] at *
      exact h₁
  btw_antisymm := @fun a b c h₁ h₂ => by
    simp only [btw] at *
    if h₃ : a < c then
      rw [if_neg (not_lt_of_lt h₃), if_pos h₃] at *
      refine Or.elim h₂ ?_ ?_
      · exact fun g => Or.inr <| Or.inl <| le_antisymm h₁.right g
      · exact fun g => Or.inl <| le_antisymm h₁.left g
    else if h₄ : c < a then
      rw [if_neg h₃, if_pos h₄] at *
      refine Or.elim h₁ ?_ ?_
      · exact fun g => Or.inl <| le_antisymm g h₂.right
      · exact fun g => Or.inr <| Or.inl <| le_antisymm g h₂.left
    else
      apply le_of_not_lt at h₃
      apply le_of_not_lt at h₄
      exact Or.inr <| Or.inr <| le_antisymm h₃ h₄
  btw_total := fun a b c => by
    simp only [btw]
    if h₁ : a < c then
      repeat rw [if_neg (not_lt_of_lt h₁), if_pos h₁]
      refine Or.elim (Classical.em (a ≤ b ∧ b ≤ c)) ?_ ?_
      · exact fun g => Or.inl g
      · intro h₂
        push_neg at h₂
        by_cases h₃ : a ≤ b
        · exact Or.inr <| Or.inl <| le_of_lt <| h₂ h₃
        · push_neg at h₃
          exact Or.inr <| Or.inr <| le_of_lt h₃
    else if h₂ : c < a then
      repeat rw [if_neg h₁, if_pos h₂]
      refine Or.elim (Classical.em (c ≤ b ∧ b ≤ a)) ?_ ?_
      · exact fun g => Or.inr g
      · intro h₃
        push_neg at h₃
        by_cases h₄ : c ≤ b
        · exact Or.inl <| Or.inl <| le_of_lt <| h₃ h₄
        · push_neg at h₄
          exact Or.inl <| Or.inr <| le_of_lt h₄
    else
      repeat rw [if_neg h₁, if_neg h₂]
      exact Or.inl trivial
}

/--
Auxilary instance: show that `btw` is `Decidable`.
-/
instance aux_btw_decidable (a b : Fin (n + 1)) : DecidablePred (fun x => btw a x b) := fun x => by
  simp [btw]
  exact inferInstance

/--
Circular left-closed right-closed interval `[a -> b]` on `Fin (n + 1)`: if `a = b`, the interval is defined to be the single point `a`(or `b`); otherwise, this interval includes `a`, and all the numbers obtained by starting from `a` and successively adding `1` until reaching `b`.
-/
def Fin.cIcc (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  if a = b then
    {a}
  else
    {x | btw a x b}.toFinset

/--
Use `[a ->> b]` to represent `Fin.cIcc a b`.
-/
notation:max "[" a " ->> " b "]" => Fin.cIcc a b

/--
Left endpoint belongs to the `cIcc`.
-/
theorem Fin.left_mem_cIcc {a b : Fin (n + 1)} : a ∈ [a ->> b] := by
  simp only [Fin.cIcc]
  if h : a = b then
    rw [if_pos h, Finset.mem_singleton]
  else
    rw [if_neg h, Set.mem_toFinset, Set.mem_setOf]
    exact btw_rfl_left

/--
Right endpoint belongs to the `cIcc`.
-/
theorem Fin.right_mem_cIcc {a b : Fin (n + 1)} : b ∈ [a ->> b] := by
  simp only [Fin.cIcc]
  if h : a = b then
    rw [if_pos h, h, Finset.mem_singleton]
  else
    rw [if_neg h, Set.mem_toFinset, Set.mem_setOf]
    exact btw_refl_right _ _

/--
If endpoints of `cIcc` are not equal, then `x ∈ [a ->> b] ↔ btw a x b`.
-/
theorem Fin.mem_cIcc_of_ne {a b : Fin (n + 1)} (h : a ≠ b) (x : Fin (n + 1)) : x ∈ [a ->> b] ↔ btw a x b := by
  simp only [Fin.cIcc]
  rw [if_neg h, Set.mem_toFinset]
  exact Set.mem_setOf

/--
`x ∈ [a ->> a] ↔ x = a`.
-/
theorem Fin.mem_cIcc_self {a : Fin (n + 1)} (x : Fin (n + 1)) : x ∈ [a ->> a] ↔ x = a := by
  simp only [Fin.cIcc, if_pos]
  exact Finset.mem_singleton

/--
`[a ->> a]` only contains the single point `a`, i.e. `[a ->> a] = {a}`.
-/
theorem Fin.cIcc_self {a : Fin (n + 1)} : [a ->> a] = {a} := by
  ext x
  rw [Finset.mem_singleton]
  exact Fin.mem_cIcc_self _

/--
If endpoints of `cIcc` are not equal, then the two `cIcc`s obtained by swapping endpoints cover the whole `Fin (n + 1)`.
-/
theorem Fin.mem_cIcc_or {a b : Fin (n + 1)} (h : a ≠ b) (x : Fin (n + 1)) : x ∈ [a ->> b] ∨ x ∈ [b ->> a] := by
  rw [Fin.mem_cIcc_of_ne h, Fin.mem_cIcc_of_ne h.symm]
  exact btw_total _ _ _

/--
Intersection of the two `cIcc`s obtained by swapping endpoints only contains the endpoints.
-/
theorem Fin.mem_cIcc_antisymm {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ [a ->> b] ∧ x ∈ [b ->> a] ↔ x = a ∨ x = b := by
  constructor <;> intro h
  · rcases h with ⟨mem₁, mem₂⟩
    if h : a = b then
      rw [h, Fin.mem_cIcc_self] at mem₁ mem₂
      exact Or.inr mem₁
    else
      rw [Fin.mem_cIcc_of_ne h] at mem₁
      rw [Fin.mem_cIcc_of_ne (by tauto)] at mem₂
      have h₁ := Btw.btw.antisymm mem₁ mem₂
      match h₁ with
      | Or.inl h₂ =>
        exact Or.inl <| h₂.symm
      | Or.inr <| Or.inl h₂ =>
        exact Or.inr h₂
      | Or.inr <| Or.inr h₂ =>
        tauto
  · refine Or.elim h ?_ ?_ <;> intro h₁
    · rw [h₁]
      exact ⟨Fin.left_mem_cIcc, Fin.right_mem_cIcc⟩
    · rw [h₁]
      exact ⟨Fin.right_mem_cIcc, Fin.left_mem_cIcc⟩

/--
If the `cIcc` contains more than one element, then the "previous" (under the circular order) element of the right endpoint belongs to that `cIcc`.
-/
theorem Fin.sub_one_mem_cIcc {a : Fin (n + 1)} : ∀ b, a ≠ b → a - 1 ∈ [b ->> a] := by
  intro b ne
  if h₁ : b < a then
    rw [Fin.mem_cIcc_of_ne ne.symm]
    simp only [btw]
    rw [if_pos h₁]
    suffices h₂ : a - 1 < a
    · exact ⟨by
        have lt : 0 < a := by
          exact Fin.sub_one_lt_iff.mp h₂
        have le : 1 ≤ a := by
          if h₃ : n = 0 then
            omega
          else
            rw [Fin.le_def, Fin.val_one'']
            rw [Nat.mod_eq_of_lt (by omega)]
            omega
        rw [Fin.lt_def] at h₁
        rw [Fin.le_def, Fin.coe_sub_iff_le.mpr le, Fin.val_one'']
        rw [Nat.mod_eq_of_lt (by omega)]
        omega, le_of_lt h₂⟩
    · rw [Fin.lt_def] at h₁
      rw [Fin.sub_one_lt_iff, Fin.lt_def]
      change 0 < _
      omega
  else if h₂ : a < b then
    rw [Fin.mem_cIcc_of_ne (by tauto)]
    simp only [btw]
    rw [if_neg h₁, if_pos h₂]
    if h₃ : a = 0 then
      refine Or.inl ?_
      rw [h₃, Fin.le_def]
      suffices h₄ : (0 - 1 : Fin (n + 1)).val = n
      · rw [h₄]
        omega
      · rw [Fin.coe_sub_one, if_pos rfl]
    else
      refine Or.inr ?_
      rw [Fin.le_def, Fin.coe_sub_one, if_neg h₃]
      omega
  else
    omega

/--
If the `cIcc` contains more than one element, then the "next" (under the circular order) element of the left endpoint belongs to that `cIcc`.
-/
theorem Fin.add_one_mem_cIcc {a : Fin (n + 1)} : ∀ b, a ≠ b → a + 1 ∈ [a ->> b] := by
  intro b ne
  rw [Fin.mem_cIcc_of_ne ne]
  simp only [btw]
  if h₁ : a < b then
    rw [if_pos h₁]
    have h₂ : a ≠ Fin.last n := by
      intro h₂
      rw [← Fin.val_inj, Fin.val_last] at h₂
      omega
    constructor
    · rw [Fin.lt_def] at h₁
      rw [Fin.le_def, Fin.val_add_one, if_neg h₂]
      exact le_of_lt <| Nat.lt_add_one _
    · rw [Fin.le_def, Fin.val_add_one, if_neg h₂]
      omega
  else if h₂ : b < a then
    rw [if_neg h₁, if_pos h₂]
    if h₃ : a = Fin.last n then
      refine Or.inr ?_
      rw [h₃, Fin.last_add_one]
      exact Fin.zero_le _
    else
      refine Or.inl ?_
      rw [Fin.le_def, Fin.val_add_one, if_neg h₃]
      omega
  else
    rw [if_neg h₁, if_neg h₂]
    exact trivial

/--
If the sum of distances from point `x` to the two endpoints equals the length of the `cIcc`, then `x` belongs to that `cIcc`.
-/
theorem Fin.val_sub_add_eq_iff_mem_cIcc {a b : Fin (n + 1)} (x : Fin (n + 1)) : (x - a).val + (b - x).val = (b - a).val ↔ x ∈ [a ->> b] := by
  if h₁ : a < b then
    rw [Fin.mem_cIcc_of_ne (ne_of_lt h₁), Fin.coe_sub_iff_le.mpr (le_of_lt h₁)]
    simp only [btw, if_pos h₁]
    if h₂ : a ≤ x then
      rw [Fin.coe_sub_iff_le.mpr h₂, ← Nat.sub_add_comm (Fin.le_def.mp h₂)]
      constructor <;> intro h₃
      · replace h₃ := show x.val + (b - x).val = b.val by
          omega
        apply Nat.eq_sub_of_add_eq' at h₃
        rw [Fin.coe_sub_iff_le] at h₃
        exact ⟨h₂, h₃⟩
      · rw [Fin.coe_sub_iff_le.mpr h₃.right]
        omega
    else
      push_neg at h₂
      rw [Fin.coe_sub_iff_lt.mpr h₂]
      omega     -- amazing `omega`!!
  else if h₂ : b < a then
    rw [Fin.mem_cIcc_of_ne (ne_of_gt h₂), Fin.coe_sub_iff_lt.mpr h₂]
    simp only [btw, if_neg h₁, if_pos h₂]
    if h₃ : x ≤ b then
      rw [Fin.coe_sub_iff_le.mpr h₃, Fin.coe_sub_iff_lt.mpr (lt_of_le_of_lt h₃ h₂)]
      omega
    else
      rw [Fin.coe_sub_iff_lt.mpr (show b < x by push_neg at h₃; exact h₃)]
      constructor <;> intro h₄
      · replace h₄ := show (x - a).val = x.val - a.val by omega
        rw [Fin.coe_sub_iff_le] at h₄
        exact Or.inl h₄
      · replace h₄ := Or.resolve_right h₄ h₃
        rw [Fin.coe_sub_iff_le.mpr h₄]
        omega
  else
    have eq : a = b := by
      push_neg at h₁
      push_neg at h₂
      exact Fin.le_antisymm h₂ h₁
    repeat rw [eq]
    rw [sub_self, Fin.mem_cIcc_self]
    show _ = 0 ↔ _
    if h₃ : x < b then
      rw [Fin.coe_sub_iff_lt.mpr h₃, Fin.coe_sub_iff_le.mpr (le_of_lt h₃)]
      omega
    else if h₄ : b < x then
      rw [Fin.coe_sub_iff_lt.mpr h₄, Fin.coe_sub_iff_le.mpr (le_of_lt h₄)]
      omega
    else
      have eq' : x = b := by
        push_neg at h₃
        push_neg at h₄
        exact Fin.le_antisymm h₄ h₃
      repeat rw [eq']
      rw [sub_self]
      show 0 + 0 = 0 ↔ _
      rw [add_zero]
      exact ⟨fun _ => rfl, fun _ => rfl⟩

/--
Suppose `a` and `b` are two distinct points, `x` is between `a` and `b` (by the circular order), if and only if, the distance between `x` and `a` is no more than which between `b` and `a`.
-/
theorem Fin.val_sub_le_iff_btw {a x b : Fin (n + 1)} (ne : a ≠ b) : btw a x b ↔ (x - a).val ≤ (b - a).val := by
  simp only [btw]
  constructor <;> intro h
  · if h₁ : a < b then
      rw [if_pos h₁] at h
      rw [Fin.coe_sub_iff_le.mpr h.left, Fin.coe_sub_iff_le.mpr (le_of_lt h₁)]
      omega
    else if h₂ : b < a then
      rw [if_neg h₁, if_pos h₂] at h
      refine Or.elim h ?_ ?_ <;> intro h₃
      · rw [Fin.coe_sub_iff_le.mpr h₃, Fin.coe_sub_iff_lt.mpr h₂]
        refine Nat.sub_le_sub_right ?_ _
        exact le_trans (le_of_lt x.isLt) (Nat.le_add_right _ _)
      · rw [Fin.coe_sub_iff_lt.mpr h₂, Fin.coe_sub_iff_lt.mpr (lt_of_le_of_lt h₃ h₂)]
        refine Nat.sub_le_sub_right ?_ _
        refine Nat.add_le_add_left ?_ _
        exact Fin.val_le_of_le h₃
    else
      exfalso
      apply le_of_not_lt at h₁
      apply le_of_not_lt at h₂
      exact ne <| le_antisymm h₂ h₁
  · if h₁ : a < b then
      rw [Fin.coe_sub_iff_le.mpr (le_of_lt h₁)] at h
      rw [if_pos h₁]
      suffices h₂ : a ≤ x
      · rw [Fin.coe_sub_iff_le.mpr h₂] at h
        exact ⟨h₂, by omega⟩
      · by_contra h₂
        push_neg at h₂
        rw [Fin.coe_sub_iff_lt.mpr h₂] at h
        omega
    else if h₂ : b < a then
      rw [if_neg h₁, if_pos h₂]
      by_cases h₃ : a ≤ x
      · exact Or.inl h₃
      · push_neg at h₃
        rw [Fin.coe_sub_iff_lt.mpr h₂, Fin.coe_sub_iff_lt.mpr h₃] at h
        omega
    else
      rw [if_neg h₁, if_neg h₂]
      exact trivial

/--
Auxilary instance: for a fixed point `a` and a point `x`, the proposition `∃ m, 0 ≤ m ∧ m ≤ length ∧ x = a + m` is `Decidabale`.
-/
instance aux_continuous_segment_decidable (a : Fin (n + 1)) (length : ℕ) : DecidablePred (fun x => ∃ m, 0 ≤ m ∧ m ≤ length ∧ x = a + m) := fun x => by
  if h : (x - a).val ≤ length then
    refine .isTrue ?_
    exists (x - a).val
    constructor
    · exact Nat.zero_le _
    constructor
    · exact h
    · rw [← sub_eq_iff_eq_add', ← Fin.val_inj, Fin.val_natCast, Nat.mod_eq_of_lt (x - a).isLt]
  else
    refine .isFalse ?_
    rintro ⟨m, zero_le, le_length, eq_add⟩
    rw [eq_add, add_sub_cancel_left, Fin.val_natCast] at h
    linarith [Nat.mod_le m (n + 1)]


/-! `length + 1` is the real length, maybe we will modify the definition here later. -/
/--
The `Finset` containing `a` and the numbers obtained by starting from `a` and successively adding `1` until reaching `a + m`.
-/
def Fin.continuous_segment (a : Fin (n + 1)) (length : ℕ) : Finset (Fin (n + 1)) :=
  {x | ∃ m : ℕ, 0 ≤ m ∧ m ≤ length ∧ x = a + m}.toFinset

/--
`[a ->> b]` is the same as the continuous segment starting from `a` with length `(b - a).val`.
-/
theorem Fin.cIcc_eq_continuous_segment {a b : Fin (n + 1)} : [a ->> b] = Fin.continuous_segment a (b - a).val := by
  simp only [Fin.cIcc, Fin.continuous_segment]
  ext x
  constructor <;> intro mem
  · if h : a = b then
      rw [if_pos h, Finset.mem_singleton] at mem
      rw [Set.mem_toFinset, Set.mem_setOf]
      exists 0
      exact ⟨le_refl _, Nat.zero_le _, (show _ = _ + 0 from (add_zero a).symm ▸ mem)⟩
    else
      rw [if_neg h, Set.mem_toFinset, Set.mem_setOf] at mem
      rw [Set.mem_toFinset, Set.mem_setOf]
      exists (x - a).val
      exact ⟨Nat.zero_le _, (Fin.val_sub_le_iff_btw h).mp mem, by
        rw [← sub_eq_iff_eq_add', ← Fin.val_inj, Fin.cast_val_eq_self]⟩
  · rw [Set.mem_toFinset, Set.mem_setOf] at mem
    rcases mem with ⟨m, le₁, le₂, eq⟩
    if h : a = b then
      rw [h, sub_self] at le₂
      rw [if_pos h, Finset.mem_singleton]
      have eq_zero : (m : Fin (n + 1)) = 0 := by
        rw [← Fin.val_inj, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
        exact antisymm le₂ le₁
      exact add_zero a ▸ eq_zero ▸ eq
    else
      rw [if_neg h, Set.mem_toFinset, Set.mem_setOf, Fin.val_sub_le_iff_btw h, eq, add_sub_cancel_left, Fin.val_natCast]
      rw [Nat.mod_eq_of_lt (lt_of_le_of_lt le₂ (b - a).isLt)]
      exact le₂

/--
Given a continuous segment starting from `a` with length `length`, `x` belongs to the segment, if and only if, `x` can be expressed as the form of `a + n`, where `n` is a nonnegative number no more than `length`.
-/
theorem Fin.mem_continuous_segment {a : Fin (n + 1)} {length : ℕ} (x : Fin (n + 1)) : x ∈ a.continuous_segment length ↔ ∃ n, 0 ≤ n ∧ n ≤ length ∧ x = a + n := by
  simp only [Fin.continuous_segment]
  rw [Set.mem_toFinset]
  exact Set.mem_setOf

/--
Cardinality of `[a ->> b]` equals `(b - a).val + 1`.
-/
theorem Fin.card_cIcc {a b : Fin (n + 1)} : [a ->> b].card = (b - a).val + 1 := by
  rw [Fin.cIcc_eq_continuous_segment]
  let f : (i : ℕ) → i < (b - a).val + 1 → Fin (n + 1) :=
    fun i _ => a + i
  refine Finset.card_eq_of_bijective f ?_ ?_ ?_
  · intro x mem
    rw [Fin.mem_continuous_segment] at mem
    rcases mem with ⟨m, p⟩
    exists m, (Nat.lt_add_one_iff.mpr p.right.left)
    exact p.right.right.symm
  · intro i lt
    rw [Fin.mem_continuous_segment]
    exists i, Nat.zero_le _, (Nat.lt_add_one_iff.mp lt)
  · intro i j lt₁ lt₂ eq
    change a + i = a + j at eq
    rw [add_left_cancel_iff, ← Fin.val_inj, Fin.val_natCast, Fin.val_natCast] at eq
    have length_le : (b - a).val + 1 ≤ n + 1 := by
      omega
    replace lt₁ := lt_of_lt_of_le lt₁ length_le
    replace lt₂ := lt_of_lt_of_le lt₂ length_le
    convert eq <;> symm
    · exact Nat.mod_eq_of_lt lt₁
    · exact Nat.mod_eq_of_lt lt₂

/--
`[a ->> b]` equals `univ`, if and only if, `a = b + 1`.
-/
theorem Fin.cIcc_eq_univ {a b : Fin (n + 1)} : [a ->> b] = Finset.univ ↔ a = b + 1 := by
  constructor <;> intro h
  · if h₁ : a = b then
      rw [h₁, Fin.cIcc_self] at h
      have zero_mem : (0 : Fin (n + 1)) ∈ Finset.univ := Finset.mem_univ _
      have one_mem : (1 : Fin (n + 1)) ∈ Finset.univ := Finset.mem_univ _
      rw [← h, Finset.mem_singleton] at zero_mem
      rw [← h, Finset.mem_singleton] at one_mem
      rw [one_mem]
      nth_rw 2 [← zero_mem]
      rw [add_zero, h₁]
    else
      have h₂ : b + 1 ∈ Fin.cIcc a b := h ▸ Finset.mem_univ _
      have h₃ : b + 1 ∈ Fin.cIcc b a := by
        rw [Fin.cIcc_eq_continuous_segment, Fin.mem_continuous_segment]
        exists 1, by omega
        constructor
        · apply sub_ne_zero_of_ne at h₁
          apply Fin.pos_of_ne_zero at h₁
          rw [Fin.lt_def] at h₁
          show 0 + 1 ≤ _
          rw [← Nat.lt_iff_add_one_le]
          exact h₁
        · exact rfl
      refine Or.elim (Fin.mem_cIcc_antisymm.mp ⟨h₂, h₃⟩) ?_ ?_ <;> intro h₄
      · exact h₄.symm
      · nth_rw 2 [← add_zero b] at h₄
        rw [add_left_cancel_iff, Fin.one_eq_zero_iff] at h₄
        omega
  · refine Finset.eq_univ_of_card _ ?_
    rw [Fin.card_cIcc, Fintype.card_fin]
    if h₁ : a ≤ b then
      rw [Fin.coe_sub_iff_le.mpr h₁]
      rw [h, Fin.add_one_le_iff] at h₁
      rw [h₁, Fin.last_add_one] at h
      rw [← Fin.val_inj] at h h₁
      change _ = 0 at h
      change _ = n at h₁
      omega
    else
      push_neg at h₁
      rw [← sub_eq_iff_eq_add', ← Fin.val_inj, Fin.coe_sub_iff_le.mpr (le_of_lt h₁), Nat.sub_eq_iff_eq_add (le_of_lt h₁), Fin.val_one''] at h
      rw [Fin.coe_sub_iff_lt.mpr h₁, h]
      have lt : 1 < n + 1 := by
        nth_rw 1 [← zero_add 1]
        rw [Nat.add_lt_add_iff_right]
        by_contra h₂
        push_neg at h₂
        apply Nat.eq_zero_of_le_zero at h₂
        subst h₂
        omega
      rw [Nat.mod_eq_of_lt lt]
      omega

/--
`[a ->> a]` (formed by a single point `a`) equal to `univ` only happens in `Fin 1`.
-/
theorem Fin.cIcc_self_eq_univ_iff_fin_one {a : Fin (n + 1)} : [a ->> a] = Finset.univ ↔ n = 0 := by
  constructor <;> intro h
  · rw [Fin.cIcc_eq_univ] at h
    nth_rw 1 [← add_zero a] at h
    rw [add_left_cancel_iff, Fin.zero_eq_one_iff] at h
    omega
  · subst h
    rw [Fin.cIcc_self]
    ext x
    constructor <;> intro _
    · exact Finset.mem_univ _
    · rw [Finset.mem_singleton]
      omega

/--
Every `cIcc` equals `univ` in `Fin 1`.
-/
theorem Fin.cIcc_eq_univ_of_fin_one {a b : Fin (n + 1)} (h : n = 0) : [a ->> b] = Finset.univ := by
  subst h
  rw [Fin.cIcc_eq_univ]
  omega

/--
For any number `x` in `[a ->> b]`, `[x ->> b]` lies within `[a ->> b]`.
-/
theorem Fin.cIcc_subset_right {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ [a ->> b] → [x ->> b] ⊆ [a ->> b] := by
  intro mem₁ y mem₂
  if h₁ : a = b then
    subst h₁
    rw [Fin.mem_cIcc_self] at *
    rw [mem₁, Fin.mem_cIcc_self] at mem₂
    exact mem₂
  else if h₂ : x = b then
    rw [h₂, Fin.mem_cIcc_self] at mem₂
    rw [mem₂]
    exact right_mem_cIcc
  else
    rw [Fin.cIcc_eq_continuous_segment, Fin.mem_continuous_segment] at *
    rcases mem₁ with ⟨m₁, le₁₁, le₁₂, eq₁⟩
    rcases mem₂ with ⟨m₂, le₂₁, le₂₂, eq₂⟩
    exists m₁ + m₂
    constructor
    · omega
    constructor
    · have h₃ : (m₁ : Fin (n + 1)) ≤ b - a := by
        rw [Fin.le_def, Fin.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt le₁₂ (b - a).isLt)]
        exact le₁₂
      rw [eq₁, ← sub_sub, Fin.coe_sub_iff_le.mpr h₃, Fin.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt le₁₂ (b - a).isLt)] at le₂₂
      omega
    · rw [eq₂, eq₁, add_assoc, add_left_cancel_iff, ← Fin.val_inj, Fin.val_add]
      repeat rw [Fin.val_natCast]
      rw [Nat.mod_eq_of_lt (lt_of_le_of_lt le₁₂ (b - a).isLt), Nat.mod_eq_of_lt (lt_of_le_of_lt le₂₂ (b - x).isLt)]

/--
For any number `x` in `[a ->> b]`, `[a ->> x]` lies within `[a ->> b]`.
-/
theorem Fin.cIcc_subset_left {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ [a ->> b] → [a ->> x] ⊆ [a ->> b] := by
  intro mem₁ y mem₂
  if h₁ : a = b then
    subst h₁
    rw [Fin.mem_cIcc_self] at *
    rw [mem₁, Fin.mem_cIcc_self] at mem₂
    exact mem₂
  else if h₂ : x = a then
    rw [h₂, Fin.mem_cIcc_self] at mem₂
    rw [mem₂]
    exact left_mem_cIcc
  else
    rw [Fin.cIcc_eq_continuous_segment, Fin.mem_continuous_segment] at *
    rcases mem₁ with ⟨m₁, _, le₁₂, eq₁⟩
    rcases mem₂ with ⟨m₂, le₂₁, le₂₂, eq₂⟩
    exists m₂
    constructor
    · omega
    constructor
    · rw [eq₁, add_sub_assoc, add_sub_cancel, Fin.val_natCast, Nat.mod_eq_of_lt (lt_of_le_of_lt le₁₂ (b - a).isLt)] at le₂₂
      omega
    · exact eq₂

/--
If `[a ->> b]` contains more than one point (i.e. `a ≠ b`), then the `Finset` obtained by deleting the left endpoint of `[a ->> b]` is `[(a + 1) ->> b]`.
-/
theorem Fin.cIcc_sdiff_endpoint_left {a b : Fin (n + 1)} (h : a ≠ b) : [a ->> b] \ {a} = [(a + 1) ->> b] := by
  ext x
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  constructor <;> intro mem
  · rw [Fin.cIcc_eq_continuous_segment, Fin.mem_continuous_segment] at *
    rcases mem.left with ⟨m, _, le₂, eq⟩
    replace mem := mem.right
    exists m - 1
    constructor
    · omega
    constructor
    · have h₁ : 1 ≤ b - a := by
        rw [Fin.le_def, Fin.val_one'']
        if h₂ : n = 0 then
          omega
        else
          rw [Nat.mod_eq_of_lt (by omega)]
          by_contra h₃
          push_neg at h₃
          rw [Nat.lt_one_iff, ← Fin.val_zero (n + 1), Fin.val_inj, sub_eq_zero] at h₃
          exact h h₃.symm
      rw [← sub_sub, Fin.coe_sub_iff_le.mpr h₁, Fin.val_one'']
      if h₂ : n = 0 then
        omega
      else
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    · rw [eq, add_assoc, add_left_cancel_iff, ← Fin.val_inj, Fin.val_add, Fin.val_one'', Fin.val_natCast, Fin.val_natCast]
      if h₁ : n = 0 then
        omega
      else
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega), Nat.mod_eq_of_lt (show m - 1 < n + 1 by omega), ← Nat.add_sub_assoc (by
          by_contra h₂
          push_neg at h₂
          rw [Nat.lt_one_iff] at h₂
          rw [h₂] at eq
          change _ = _ + 0 at eq
          rw [add_zero] at eq
          exact mem eq), add_comm 1 m, Nat.add_sub_cancel]
  · exact ⟨Fin.cIcc_subset_right (add_one_mem_cIcc b h) <| mem, by
      intro h₁
      if h₂ : a + 1 = b then
        rw [h₂, Fin.mem_cIcc_self, h₁] at mem
        exact h mem
      else
        rw [h₁] at mem
        have mem' : a ∈ Fin.cIcc b (a + 1) := by
          nth_rw 2 [← add_sub_cancel_right a 1]
          exact sub_one_mem_cIcc b h₂
        refine Or.elim (Fin.mem_cIcc_antisymm.mp ⟨mem, mem'⟩) ?_ ?_ <;> intro h₂
        · nth_rw 1 [← add_zero a] at h₂
          rw [add_left_cancel_iff, Fin.zero_eq_one_iff] at h₂
          omega
        · exact h h₂⟩

/--
If `[a ->> b]` contains more than one point (i.e. `a ≠ b`), then the `Finset` obtained by deleting the right endpoint of `[a ->> b]` is `[a ->> (b - 1)]`.
-/
theorem Fin.cIcc_sdiff_endpoint_right {a b : Fin (n + 1)} (h : a ≠ b) : [a ->> b] \ {b} = [a ->> (b - 1)] := by
  ext x
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  constructor <;> intro mem
  · rw [Fin.cIcc_eq_continuous_segment, Fin.mem_continuous_segment] at *
    rcases mem.left with ⟨m, le₁, le₂, eq⟩
    replace mem := mem.right
    exists m
    constructor
    · omega
    constructor
    · have h₁ : 1 ≤ b - a := by
        rw [Fin.le_def, Fin.val_one'']
        if h₂ : n = 0 then
          omega
        else
          rw [Nat.mod_eq_of_lt (by omega)]
          by_contra h₃
          push_neg at h₃
          rw [Nat.lt_one_iff, ← Fin.val_zero (n + 1), Fin.val_inj, sub_eq_zero] at h₃
          exact h h₃.symm
      rw [sub_sub, add_comm 1 a, ← sub_sub, Fin.coe_sub_iff_le.mpr h₁, Fin.val_one'']
      replace le₂ := lt_of_le_of_ne le₂ (by
        intro h₂
        rw [h₂, Fin.cast_val_eq_self, add_sub_cancel] at eq
        exact mem eq)
      if h₂ : n = 0 then
        omega
      else
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    · exact eq
  · exact ⟨Fin.cIcc_subset_left (sub_one_mem_cIcc a h.symm) <| mem, by
      intro h₁
      if h₂ : a = b - 1 then
        rw [← h₂, Fin.mem_cIcc_self, h₁] at mem
        exact h mem.symm
      else
        rw [h₁] at mem
        have mem' : b ∈ Fin.cIcc (b - 1) a := by
          nth_rw 2 [← sub_add_cancel b 1]
          exact add_one_mem_cIcc a (by tauto)
        refine Or.elim (Fin.mem_cIcc_antisymm.mp ⟨mem, mem'⟩) ?_ ?_ <;> intro h₂
        · exact h h₂.symm
        · nth_rw 2 [← add_zero b] at h₂
          rw [eq_sub_iff_add_eq, add_left_cancel_iff, Fin.one_eq_zero_iff] at h₂
          omega⟩

/--
If `[a ->> b]` is not `univ`, then we can get `[(a - 1) ->> b]` by inserting `a - 1` into `[a ->> b]`.
-/
theorem Fin.cIcc_insert_eq_cIcc_left {a b : Fin (n + 1)} (h : [a ->> b] ≠ Finset.univ) : insert (a - 1) [a ->> b] = [(a - 1) ->> b] := by
  ext x
  rw [Finset.mem_insert]
  have aux : a - 1 ≠ b :=
    fun eq => by
      exact h (Fin.cIcc_eq_univ.mpr (eq_add_of_sub_eq eq))
  constructor <;> intro mem
  · cases mem with
    | inl mem =>
      exact mem ▸ Fin.left_mem_cIcc
    | inr mem =>
      refine (Fin.cIcc_subset_right ?_) mem
      conv =>
        enter [2]
        rw [← sub_add_cancel a 1]
      exact Fin.add_one_mem_cIcc b aux
  · if h' : x = a - 1 then
      exact Or.inl h'
    else
      rw [← Finset.mem_singleton] at h'
      conv =>
        enter [2, 1, 1]
        rw [← sub_add_cancel a 1]
      rw [← Fin.cIcc_sdiff_endpoint_left aux]
      exact Or.inr (Finset.mem_sdiff.mpr ⟨mem, h'⟩)

/--
If `[a ->> b]` is not `univ`, then we can get `[a ->> (b + 1)]` by inserting `b + 1` into `[a ->> b]`.
-/
theorem Fin.cIcc_insert_eq_cIcc_right {a b : Fin (n + 1)} (h : [a ->> b] ≠ Finset.univ) : insert (b + 1) [a ->> b] = [a ->> (b + 1)] := by
  ext x
  rw [Finset.mem_insert]
  have aux : a ≠ b + 1 :=
    fun eq => by
      exact h (Fin.cIcc_eq_univ.mpr eq)
  constructor <;> intro mem
  · cases mem with
    | inl mem =>
      exact mem ▸ Fin.right_mem_cIcc
    | inr mem =>
      refine (Fin.cIcc_subset_left ?_) mem
      conv =>
        enter [2]
        rw [← add_sub_cancel_right b 1]
      exact Fin.sub_one_mem_cIcc a aux.symm
  · if h' : x = b + 1 then
      exact Or.inl h'
    else
      rw [← Finset.mem_singleton] at h'
      conv =>
        enter [2, 1, 2]
        rw [← add_sub_cancel_right b 1]
      rw [← Fin.cIcc_sdiff_endpoint_right aux]
      exact Or.inr (Finset.mem_sdiff.mpr ⟨mem, h'⟩)

/--
If `[a ->> b]` is not equal to `univ`, then the complement of `[a ->> b]` is `[(b + 1) ->> (a - 1)]`.
-/
theorem Fin.cIcc_compl {a b : Fin (n + 1)} (h : Fin.cIcc a b ≠ Finset.univ) : Finset.univ \ [a ->> b] = [(b + 1) ->> (a - 1)] := by
  if h₁ : a = b then
    subst h₁
    rw [Fin.cIcc_self, ← Fin.cIcc_eq_univ.mpr (show a + 1 = a + 1 from rfl), Fin.cIcc_sdiff_endpoint_right]
    intro h₂
    nth_rw 2 [← add_zero a] at h₂
    rw [add_left_cancel_iff, Fin.one_eq_zero_iff] at h₂
    nth_rw 2 [← zero_add 1] at h₂
    rw [add_right_cancel_iff] at h₂
    rw [Fin.cIcc_self] at h
    subst h₂
    refine h ?_
    ext x
    constructor <;> intro _
    · exact Finset.mem_univ _
    · rw [Finset.mem_singleton, Fin.eq_zero x, Fin.eq_zero a]
  else
    rw [← Fin.cIcc_sdiff_endpoint_right (show b + 1 ≠ a by
      intro h₂
      exact h <| Fin.cIcc_eq_univ.mpr h₂.symm), ← Fin.cIcc_sdiff_endpoint_left (by tauto)]
    ext x
    constructor <;> intro mem
    · rw [Finset.mem_sdiff] at mem
      replace mem := mem.right
      have ne₁ : x ≠ a := by
        contrapose! mem
        rw [mem]
        exact left_mem_cIcc
      have ne₂ : x ≠ b := by
        contrapose! mem
        rw [mem]
        exact right_mem_cIcc
      replace mem := Or.resolve_left (Fin.mem_cIcc_or (show a ≠ b by tauto) x) mem
      repeat rw [Finset.mem_sdiff, Finset.mem_singleton]
      tauto
    · repeat rw [Finset.mem_sdiff, Finset.mem_singleton] at mem
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, fun h₂ => by
        have h₃ := Fin.mem_cIcc_antisymm.mp ⟨h₂, mem.left.left⟩
        tauto⟩

/--
If `a ≤ b`, then `Icc a b = [a ->> b]`.
-/
theorem Fin.Icc_eq_cIcc {a b : Fin (n + 1)} (h : a ≤ b) : Finset.Icc a b = [a ->> b] := by
  rw [le_iff_lt_or_eq] at h
  ext x
  rw [Finset.mem_Icc]
  rcases h with h | h
  · rw [Fin.mem_cIcc_of_ne (ne_of_lt h)]
    simp only [btw, if_pos h]
  · rw [h, Fin.mem_cIcc_self]
    constructor <;> intro h'
    · exact le_antisymm h'.right h'.left
    · rw [h']
      exact ⟨le_refl _, le_refl _⟩

/--
Especially, `Iic a = Icc 0 a = [0 ->> a]` for any `a`.
-/
theorem Fin.Iic_eq_cIcc {a : Fin (n + 1)} : Finset.Iic a = [0 ->> a] := by
  rw [show Finset.Iic a = Finset.Icc 0 a from rfl,
    Fin.Icc_eq_cIcc (Fin.zero_le _)]

/--
`a - 1 ∈ [a ->> b]`, if and only if, `[a ->> b] = univ`.
-/
theorem Fin.left_mem_cIcc_iff_cIcc_eq_univ {a b : Fin (n + 1)} : a - 1 ∈ [a ->> b] ↔ [a ->> b] = Finset.univ := by
  constructor <;> intro h
  · by_contra! h₁
    have h₂ := Fin.cIcc_compl h₁
    have h₃ : a - 1 ∉ [b + 1 ->> a - 1] := by
      rw [← h₂]
      exact Finset.not_mem_sdiff_of_mem_right h
    exact h₃ Fin.right_mem_cIcc
  · rw [h]
    exact Finset.mem_univ _

/--
`b + 1 ∈ [a ->> b]`, if and only if, `[a ->> b] = univ`.
-/
theorem Fin.right_mem_cIcc_iff_cIcc_eq_univ {a b : Fin (n + 1)} : b + 1 ∈ [a ->> b] ↔ [a ->> b] = Finset.univ := by
  constructor <;> intro h
  · by_contra! h₁
    have h₂ := Fin.cIcc_compl h₁
    have h₃ : b + 1 ∉ [b + 1 ->> a - 1] := by
      rw [← h₂]
      exact Finset.not_mem_sdiff_of_mem_right h
    exact h₃ Fin.left_mem_cIcc
  · rw [h]
    exact Finset.mem_univ _

/--
`a - 1 ∉ [a ->> b]`, if `[a ->> b] ≠ univ`.
-/
theorem Fin.left_not_mem_cIcc_of_ne_univ {a b : Fin (n + 1)} (h : [a ->> b] ≠ Finset.univ) : a - 1 ∉ [a ->> b] :=
  (not_iff_not.mpr Fin.left_mem_cIcc_iff_cIcc_eq_univ).mpr h

/--
`b + 1 ∉ [a ->> b]`, if `[a ->> b] ≠ univ`.
-/
theorem Fin.right_not_mem_cIcc_of_ne_univ {a b : Fin (n + 1)} (h : [a ->> b] ≠ Finset.univ) : b + 1 ∉ [a ->> b] :=
  (not_iff_not.mpr Fin.right_mem_cIcc_iff_cIcc_eq_univ).mpr h

/--
Two non-univ `cIcc`s, say `[a ->> b]` and `[c ->> d]`, are equal, if and only if, `a = c ∧ b = d`.
-/
theorem Fin.cIcc_eq_cIcc_iff_of_ne_univ {a b c d : Fin (n + 1)} (h : [a ->> b] ≠ Finset.univ ∨ [c ->> d] ≠ Finset.univ) : [a ->> b] = [c ->> d] ↔ a = c ∧ b = d := by
  constructor <;> intro h₁
  · have h₂ := h₁
    apply_fun fun x => x.card at h₂
    simp only [Fin.card_cIcc] at h₂
    apply add_right_cancel at h₂
    suffices h₃ : a = c
    · rw [Fin.val_inj, h₃, sub_eq_iff_eq_add, sub_add_cancel] at h₂
      exact ⟨h₃, h₂⟩
    · by_contra! h₃
      wlog h₄ : [a ->> b] ≠ Finset.univ generalizing a b c d with H
      · exact H h.symm h₁.symm h₂.symm h₃.symm (Or.resolve_left h h₄)
      · wlog h₅ : a < c generalizing a b c d with H
        · replace h₅ := lt_of_le_of_ne (le_of_not_lt h₅) h₃.symm
          exact H h.symm h₁.symm h₂.symm h₃.symm (h₁ ▸ h₄) h₅
        · if h' : n = 0 then
            rw [Fin.cIcc_eq_univ_of_fin_one h'] at h₄
            exact h₄ rfl
          else
            replace h₄ := h₁ ▸ (not_iff_not.mpr Fin.right_mem_cIcc_iff_cIcc_eq_univ).mpr h₄
            refine h₄ ?_
            rw [Fin.cIcc_eq_continuous_segment, Fin.mem_continuous_segment]
            exists (b + 1 - c).val
            constructor
            · exact Nat.zero_le _
            constructor
            · have aux₁ : n + 1 ≠ 0 := NeZero.out
              rw [← h₂, Fin.coe_sub, Fin.coe_sub, Fin.val_add, Fin.val_one'',
                (Nat.mod_eq_iff_lt aux₁).mpr (show 1 < n + 1 by omega)]
              rw [Fin.lt_def] at h₅
              if aux₂ : b = Fin.last n then
                rw [aux₂, Fin.val_last, Nat.mod_self, add_zero, ← Nat.sub_add_comm (le_of_lt a.isLt),
                  Nat.add_sub_assoc (show a.val ≤ n from Nat.le_of_lt_succ a.isLt), Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
                rw [(Nat.mod_eq_iff_lt aux₁).mpr (by omega),
                  (Nat.mod_eq_iff_lt aux₁).mpr (Nat.sub_lt_succ n a.val)]
                omega
              else
                replace aux₂ := Fin.val_lt_last aux₂
                rw [(Nat.mod_eq_iff_lt aux₁).mpr (show b.val + 1 < n + 1 by omega),
                  add_comm b.val 1, ← add_assoc, ← tsub_tsub_assoc (le_of_lt c.isLt) (by omega),
                    ← Nat.sub_add_comm (by omega), ← Nat.sub_add_comm (le_of_lt a.isLt)]
                if aux₃ : b.val < a.val then
                  rw [(Nat.mod_eq_iff_lt aux₁).mpr (by omega),
                    (Nat.mod_eq_iff_lt aux₁).mpr (by omega)]
                  omega
                else if aux₄ : a.val ≤ b.val ∧ b.val < c.val - 1 then
                  exfalso
                  have h₆ : c ∉ [c ->> d] := by
                    rw [← h₁, ← Fin.Icc_eq_cIcc aux₄.left, Finset.mem_Icc]
                    omega
                  exact h₆ Fin.left_mem_cIcc
                else
                  rw [Nat.add_sub_assoc (by omega), Nat.add_sub_assoc (by omega),
                    Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
                      Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
                        (Nat.mod_eq_iff_lt aux₁).mpr (by omega),
                          (Nat.mod_eq_iff_lt aux₁).mpr (by omega)]
                  omega
            · rw [← sub_eq_iff_eq_add', ← Fin.val_inj, Fin.val_natCast,
                (Nat.mod_eq_iff_lt (show n + 1 ≠ 0 by omega)).mpr (b + 1 - c).isLt]
  · rw [h₁.left, h₁.right]

/--
For a finite set `s : Finset (Fin (n + 1))`, the boundary of `s` is defined as the number, one of whose neighbours are not members of `s`.
-/
def Fin.boundary (s : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  {a : Fin (n + 1) | a ∈ s ∧ ((a + 1) ∉ s ∨ (a - 1) ∉ s)}.toFinset

/--
The boundary of `[a ->> b]` is `{a, b}`.
-/
theorem Fin.boundary_cIcc {a b : Fin (n + 1)} (h : [a ->> b] ≠ Finset.univ) : Fin.boundary [a ->> b] = {a, b} := by
  if h₁ : a = b then
    simp only [Fin.boundary]
    simp_rw [h₁, Fin.mem_cIcc_self, Finset.insert_eq_of_mem <| Finset.mem_singleton_self b]
    ext x
    constructor <;> intro mem
    · rw [Set.mem_toFinset, Set.mem_setOf] at mem
      rw [Finset.mem_singleton, mem.left]
    · rw [Finset.mem_singleton] at mem
      rw [Set.mem_toFinset, Set.mem_setOf]
      exact ⟨mem, by
        by_contra h₂
        push_neg at h₂
        replace h₂ := h₂.left
        rw [mem] at h₂
        conv at h₂ =>
          enter [2]
          rw [← add_zero b]
        rw [add_left_cancel_iff, Fin.one_eq_zero_iff] at h₂
        refine h ?_
        rw [h₁, Fin.cIcc_self_eq_univ_iff_fin_one]
        omega⟩
  else
    simp only [Fin.boundary]
    rw [Fin.cIcc_eq_continuous_segment]
    ext x
    constructor <;> intro mem
    · rw [Set.mem_toFinset, Set.mem_setOf] at mem
      rw [Finset.mem_insert, Finset.mem_singleton]
      rw [Fin.mem_continuous_segment] at mem
      rcases mem.left with ⟨m, le₁, le₂, eq⟩
      replace mem := mem.right
      if h₂ : m = 0 then
        rw [h₂] at eq
        change _ = _ + 0 at eq
        rw [add_zero] at eq
        exact Or.inl eq
      else if h₃ : m = (b - a).val then
        rw [h₃, Fin.cast_val_eq_self, add_sub_cancel] at eq
        exact Or.inr eq
      else
        replace le₁ := lt_of_le_of_ne le₁ (by tauto)
        replace le₂ := lt_of_le_of_ne le₂ (by tauto)
        have lt₁ : m < n + 1 := lt_trans le₂ (b - a).isLt
        have lt₂ : 1 < n + 1 := by
          omega
        exfalso
        refine and_iff_not_or_not.mp ?_ <| mem
        constructor <;> rw [Fin.mem_continuous_segment]
        · exists m + 1
          exact ⟨by omega, by omega, by
            rw [eq, add_assoc, add_left_cancel_iff, ← Fin.val_inj, Fin.val_natCast]
            show (_ + _) % _ = _ % _
            rw [Nat.mod_eq_of_lt lt₁, Nat.mod_eq_of_lt lt₂]⟩
        · exists m - 1
          exact ⟨by omega, by omega, by
            rw [eq, add_sub_assoc, add_left_cancel_iff, ← Fin.val_inj, Fin.coe_sub_iff_le.mpr (Fin.le_def.mpr (by
              rw [Fin.val_one'', Fin.val_natCast, Nat.mod_eq_of_lt lt₁, Nat.mod_eq_of_lt lt₂]
              omega))]
            rw [Fin.val_one'', Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (show m - 1 < n + 1 by omega), Nat.mod_eq_of_lt lt₁, Nat.mod_eq_of_lt lt₂]⟩
    · rw [Finset.mem_insert, Finset.mem_singleton] at mem
      rw [Set.mem_toFinset, Set.mem_setOf, Fin.mem_continuous_segment]
      refine Or.elim mem ?_ ?_ <;> intro h₂
      · constructor
        · exists 0
          exact ⟨by omega, by omega, by
            show _ = _ + 0
            rw [add_zero _, h₂]⟩
        · refine Or.inr ?_
          intro h₃
          rw [h₂, ← Fin.cIcc_eq_continuous_segment] at h₃
          refine Or.elim (Fin.mem_cIcc_antisymm.mp ⟨h₃, (Fin.sub_one_mem_cIcc b h₁)⟩) ?_ ?_
          · exact fun g => by
              refine h <| Fin.cIcc_eq_univ_of_fin_one ?_
              apply_fun fun x => x + 1 at g
              rw [sub_add_cancel] at g
              nth_rw 1 [← add_zero a] at g
              rw [add_left_cancel_iff, Fin.zero_eq_one_iff] at g
              omega
          · exact fun g => by
              rw [sub_eq_iff_eq_add, ← Fin.cIcc_eq_univ] at g
              exact h <| g
      · constructor
        · exists (b - a).val
          exact ⟨by omega, by omega, by
            rw [Fin.cast_val_eq_self, h₂, add_sub_cancel]⟩
        · refine Or.inl ?_
          intro h₃
          rw [h₂, ← Fin.cIcc_eq_continuous_segment] at h₃
          refine Or.elim (Fin.mem_cIcc_antisymm.mp ⟨h₃, (Fin.add_one_mem_cIcc a (by tauto))⟩) ?_ ?_
          · exact fun g => by
              symm at g
              rw [← Fin.cIcc_eq_univ] at g
              exact h <| g
          · exact fun g => by
              refine h <| Fin.cIcc_eq_univ_of_fin_one ?_
              nth_rw 2 [← add_zero b] at g
              rw [add_left_cancel_iff, Fin.one_eq_zero_iff] at g
              omega

/- Theorems not used. -/
-- theorem Fin.map_add_left_cIcc {a b c : Fin (n + 1)} : Finset.map (addLeftEmbedding c) [a ->> b] = [c + a ->> c + b] :=
--   sorry

/- Theorems not used. -/
-- theorem Fin.map_add_right_cIcc {a b c : Fin (n + 1)} : Finset.map (addRightEmbedding c) [a ->> b] = [a + c ->> b + c] :=
--   sorry

end FinCircular

section FinAux

variable (n : ℕ)

/--
`Iic 0 = {0}` in `Fin (n + 1)`.
-/
theorem Fin.Iic_zero : Finset.Iic (0 : Fin (n + 1)) = {0} := by
  ext x
  rw [Finset.mem_Iic, Finset.mem_singleton]
  exact Fin.le_zero_iff

/--
`Iic n = univ` in `Fin (n + 1)`.
-/
theorem Fin.Iic_last : Finset.Iic (Fin.last n) = Finset.univ := by
  ext x
  rw [Finset.mem_Iic]
  exact ⟨fun _ => Finset.mem_univ _, fun _ => Fin.le_last _⟩

/--
`Iic (i + 1) = insert (i + 1) (Iic i)` in `Fin (n + 1)`.
-/
theorem Fin.Iic_succ_eq_insert (i : Fin n) : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
  ext x
  rw [Finset.mem_insert, Finset.mem_Iic, Finset.mem_Iic]
  constructor <;> intro h
  · if h' : x = i.succ then
      exact Or.inl h'
    else
      replace h' := lt_of_le_of_ne h h'
      rw [Fin.lt_def, Fin.val_succ] at h'
      refine Or.inr ?_
      rw [Fin.le_def]
      linarith [show i.castSucc.val = i.val from rfl]
  · cases h with
    | inl h =>
      exact le_of_eq h
    | inr h =>
      rw [Fin.le_def] at *
      refine le_trans h ?_
      linarith [Fin.val_succ i, show i.castSucc.val = i.val from rfl]

/--
`0 - 1 = n` in `Fin (n + 1)`.
-/
theorem Fin.zero_sub_one : (0 : Fin (n + 1)) - 1 = Fin.last n := by
  rw [← Fin.last_add_one, add_sub_cancel_right]

/--
For a finset `s : Finset (Fin (n + 1))`, `sᶜ = Finset.univ \ s`.
-/
theorem Fin.compl_def (s : Finset (Fin (n + 1))) : sᶜ = Finset.univ \ s :=
  rfl

end FinAux



namespace Pizza

section Fundamental

variable (n : ℕ)

/--
`Cuts n` for some nonnegative integer `n` represents all possible cuts that divide the pizza into `n + 1` pieces, indexed from `0`. It includes the following three fields:

• For each piece `i`, `cut.area i` is the area of that piece.

• `nonneg` states that, the area of every piece is no less than 0.

• `sum_eq_one` means the sum of areas of all pieces is `1`.
-/
structure Cuts where
  area : Fin (n + 1) → ℝ
  nonneg : ∀ i : Fin (n + 1), area i ≥ 0
  sum_eq_one : ∑ i : Fin (n + 1), area i = 1

section Turn

/--
`Turns n k` represents a game process with length `k`, with value in `Fin (n + 1)`. It is defined recursively.
-/
inductive Turns : Nat → Type where
  | init : Turns 0
  | next : {k : ℕ} → Turns k → Fin (n + 1) → Turns (k + 1)

variable {n}

/--
For `turn : Turns n (k + 1)`, `turn.head` is the first `k` turns of `turn`, with type `Turns n k`.
-/
def Turns.head {k : ℕ} (turn : Turns n (k + 1)) : Turns n k :=
  match turn with
  | next t _ =>
    t

/--
For any `turn : Turns n (k + 1)`, the `head` of `.next turn ...` is `turn` itself.
-/
theorem Turns.head_next {k : ℕ} (turn : Turns n (k + 1)) (x : Fin (n + 1)) : (turn.next x).head = turn :=
  rfl

/--
For `turn : Turns n (k + 1)`, `turn.first m _` is the first `m` turns of `turn`, with type `Turns n (m + 1)`.
-/
def Turns.first {k : ℕ} (m : ℕ) (h : m ≤ k) (turn : Turns n (k + 1)) : Turns n (m + 1) :=
  match k with
  | 0 =>
    have aux : m = 0 := by omega
    aux ▸ turn
  | k + 1 =>
    if aux : m = k + 1 then
      aux ▸ turn
    else
      turn.head.first m (by omega)

/--
For any `turn : Turns n (k + 1)`, the first `m` elements of `.next turn ...` are just those first `m` elements of `turn`.
-/
theorem Turns.first_next {k : ℕ} (m : ℕ) (h : m ≤ k) (turn : Turns n (k + 1)) (x : Fin (n + 1)) : turn.first m h = (turn.next x).first m (Nat.le_add_right_of_le h) := by
  simp only [Turns.first, dif_neg (show m ≠ k + 1 by omega), Turns.head_next]

/--
For `turn : Turns n (k + 1)`, `turn.first k _` equals itself.
-/
theorem Turns.first_eq_self {k : ℕ} (turn : Turns n (k + 1)) : turn = turn.first k (Nat.le_refl _) :=
  match k with
  | 0 =>
    rfl
  | k + 1 => by
    simp only [Turns.first, dif_pos trivial]

/--
For `turn : Turns n (k + 1)`, `turn.head = turn.first k _`.
-/
theorem Turns.first_eq_head {k : ℕ} (turn : Turns n (k + 1 + 1)) : turn.head = turn.first k (Nat.le_succ k) :=
  match turn with
  | next t _ => by
    simp only [Turns.first, dif_neg (Nat.ne_add_one k)]
    show t = Turns.first _ _ t
    exact Turns.first_eq_self _

/--
For any `turn : Turns n (k + 1)`, the first `l` elements of the first `m` elements of `turn` are just those first `l` elements of `turn`.
-/
theorem Turns.first_first {k : ℕ} (turn : Turns n (k + 1)) (m : ℕ) (h : m ≤ k) (l : ℕ) (h' : l ≤ m) : (turn.first m h).first l h' = turn.first l (le_trans h' h) :=
  match k with
  | 0 => by
    have aux : m = 0 := by omega
    subst aux
    simp only [Turns.first]
  | k + 1 => by
    simp only [Turns.first]
    split <;> rename _ => aux
    · subst aux
      rfl
    · simp only [dif_neg (show l ≠ k + 1 by omega)]
      exact turn.head.first_first _ _ _ _

/--
The last element of any `turn : Turns n (k + 1)`.
-/
def Turns.last {k : ℕ} (turn : Turns n (k + 1)) : Fin (n + 1) :=
  match turn with
  | next _ x =>
    x

/--
The last element of any `.next turn x` is `x`.
-/
theorem Turns.last_next {k : ℕ} (turn : Turns n k) (x : Fin (n + 1)) : (turn.next x).last = x :=
  rfl

/--
For any `turn : Turns n (k + 1)`, `turn.at i` represents the "i-th" element of turn.
-/
def Turns.at {k : ℕ} (turn : Turns n (k + 1)) (m : ℕ) (h : m ≤ k) : Fin (n + 1) :=
  match k with
  | 0 =>
    turn.last
  | k + 1 =>
    if aux : m = k + 1 then
      turn.last
    else
      turn.head.at m (by omega)

/--
For any `turn : Turns n (k + 1)`, the last element of `turn.first m _` is just `turn.at m _`.
-/
theorem Turns.last_first {k : ℕ} (turn : Turns n (k + 1)) (m : ℕ) (h : m ≤ k) : (turn.first m h).last = turn.at m h :=
  match k with
  | 0 => by
    have aux : m = 0 := by omega
    subst aux
    simp only [Turns.first, Turns.at]
  | k + 1 => by
    if aux : m = k + 1 then
      subst aux
      simp only [Turns.first, dif_pos, Turns.at]
    else
      simp only [Turns.first, Turns.at, dif_neg aux]
      exact turn.head.last_first _ _

/--
For any `turn : Turns n (k + 1 + 1)`, the last element of `turn.head` is just `turn.at k _`.
-/
theorem Turns.last_head {k : ℕ} (turn : Turns n (k + 1 + 1)) : turn.head.last = turn.at k (Nat.le_add_right _ _) := by
  rw [Turns.first_eq_head]
  exact Turns.last_first _ _ _

/--
For any `turn : Turns n (k + 1)`, the "k-th" element of `turn` is the last element of it.
-/
theorem Turns.at_eq_last {k : ℕ} (turn : Turns n (k + 1)) : turn.at k (le_refl _) = turn.last :=
  match k with
  | 0 =>
    rfl
  | _ + 1 => by
    simp only [Turns.at, dif_pos]

/--
For any `turn : Turns n (k + 1)`, the "l-th" elements of the first `m` elements of `turn` is just the "l-the" element of `turn`, if `l ≤ m` holds.
-/
theorem Turns.at_first {k : ℕ} (turn : Turns n (k + 1)) (m : ℕ) (h : m ≤ k) (l : ℕ) (h' : l ≤ m) : (turn.first m h).at l h' = turn.at l (le_trans h' h) := by
  match k with
  | 0 =>
    have aux : m = 0 := by omega
    subst aux
    simp only [Turns.at, ← Turns.first_eq_self]
  | k + 1 =>
    simp only [Turns.first]
    split <;> rename _ => aux
    · subst aux
      rfl
    · simp only [Turns.at, dif_neg (show l ≠ k + 1 by omega)]
      exact turn.head.at_first _ _ _ _

/--
For any `turn : Turns n (k + 1)`, the "m-th" element of `turn.head` is just the "m-the" element of `turn`.
-/
theorem Turns.at_head {k : ℕ} (turn : Turns n (k + 1 + 1)) (m : ℕ) (h : m ≤ k) : turn.head.at m h = turn.at m (le_trans h (Nat.le_add_right _ _)) := by
  rw [Turns.first_eq_head]
  exact turn.at_first _ _ _ _

/--
For any `turn : Turns n (k + 1)` and `x : Fin (n + 1)`, the "m-th" element of `turn.next x` is just the "m-th" element of `turn`, if `m ≤ k`.
-/
theorem Turns.at_next_eq_at {k : ℕ} (turn : Turns n (k + 1)) (m : ℕ) (h : m ≤ k) (x : Fin (n + 1)) : (turn.next x).at m (Nat.le_add_right_of_le h) = turn.at m h := by
  simp only [Turns.at, dif_neg (show m ≠ k + 1 by omega), Turns.head_next]

/--
For any `turn : Turns n k` and `x : Fin (n + 1)`, the "k-th" element of `turn.next x` is `x`.
-/
theorem Turns.at_next_eq {k : ℕ} (turn : Turns n k) (x : Fin (n + 1)) : (turn.next x).at k (le_refl _) = x :=
  match k with
  | 0 =>
    show (turn.next x).last = x from turn.last_next _
  | k + 1 => by
    simp only [Turns.at, dif_pos]
    exact turn.last_next _

/--
Elements of `turn : Turns n (k + 1)` are distinct from each other.
-/
def Turns.inj {k : ℕ} (turn : Turns n (k + 1)) : Prop :=
  ∀ i j (hi : i ≤ k) (hj : j ≤ k),
    turn.at i hi = turn.at j hj → i = j

/--
If a `turn : Turns n (k + 1)` satisfies `turn.inj`, then it contains at most `n` elements.
-/
theorem Turns.le_of_inj {k : ℕ} (turn : Turns n (k + 1)) (inj : turn.inj) : k ≤ n :=
  let f : Fin (k + 1) → Fin (n + 1) :=
    fun i => turn.at i.val (by omega)
  have f_inj : Function.Injective f :=
    fun x y eq => by
      simp only [f] at eq
      rw [← Fin.val_inj]
      exact inj x.val y.val (by omega) (by omega) eq
  le_of_add_le_add_right (show k + 1 ≤ n + 1 from
    calc
      _ = (Finset.univ (α := Fin (k + 1))).card :=
        (Finset.card_fin _).symm
      _ = (Finset.image f Finset.univ).card :=
        (Finset.card_image_of_injective _ f_inj).symm
      _ ≤ (Finset.univ (α := Fin (n + 1))).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = _ :=
        Finset.card_fin _)

/--
`turn.head.inj` holds if `turn.inj` holds.
-/
theorem Turns.head_inj_of_inj {k : ℕ} (turn : Turns n (k + 1 + 1)) (inj : turn.inj) : turn.head.inj :=
  fun i j hi hj eq => by
    rw [Turns.at_head, Turns.at_head] at eq
    exact inj i j (by omega) (by omega) eq

/--
The finset containing all the elements of `turn : Turns n (k + 1)`.
-/
def Turns.toFinset {k : ℕ} (turn : Turns n (k + 1)) : Finset (Fin (n + 1)) :=
  match k with
  | 0 =>
    {turn.last}
  | _ + 1 =>
    insert turn.last turn.head.toFinset

/--
If `turn` has only one element, then `turn.toFinset` is a singleton.
-/
theorem Turns.toFinset_singleton (turn : Turns n (0 + 1)) : turn.toFinset = {turn.last} :=
  rfl

/--
If `turn` has more than one element, then `turn.toFinset` equals `insert turn.last turn.head.toFinset`.
-/
theorem Turns.toFinset_eq_insert {k : ℕ} (turn : Turns n (k + 1 + 1)) : turn.toFinset = insert turn.last turn.head.toFinset :=
  rfl

/--
The "m-th" element of `turn : Turns n (k + 1)` belongs to `turn.toFinset`.
-/
theorem Turns.at_mem_toFinset {k : ℕ} (turn : Turns n (k + 1)) {m : ℕ} (h : m ≤ k) : turn.at m h ∈ turn.toFinset :=
  match k with
  | 0 =>
    show turn.last ∈ {_} from Finset.mem_singleton_self _
  | k + 1 => by
    simp only [Turns.at]
    show _ ∈ insert _ _
    split <;> rename _ => h
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (turn.head.at_mem_toFinset (by omega))

/--
A `x : Fin (n + 1)` is a member of `turn.toFinset`, if and only if, it is an element of `turn`.
-/
theorem Turns.mem_toFinset_iff {k : ℕ} (turn : Turns n (k + 1)) (x : Fin (n + 1)) : x ∈ turn.toFinset ↔ ∃ (m : {m : ℕ // m ≤ k}), turn.at m.val m.property = x := by
  constructor <;> intro h
  · match k with
    | 0 =>
      rw [Turns.toFinset_singleton, Finset.mem_singleton] at h
      exists ⟨0, le_refl _⟩
      rw [h, Turns.at_eq_last]
    | k + 1 =>
      rw [Turns.toFinset_eq_insert, Finset.mem_insert] at h
      rcases h with h | h
      · exists ⟨k + 1,  le_refl _⟩
        rw [h, ← Turns.at_eq_last]
      · replace h := (turn.head.mem_toFinset_iff x).mp h
        rcases h with ⟨m, eq⟩
        exists ⟨m, by omega⟩
        rw [Turns.at_head] at eq
        exact eq
  · rcases h with ⟨m, eq⟩
    exact eq ▸ turn.at_mem_toFinset m.property

/--
For any `turn : Turns n (k + 1)`, `turn.toFinset.card = k + 1` if `turn.inj` holds.
-/
theorem Turns.card_toFinset_of_inj {k : ℕ} (turn : Turns n (k + 1)) (inj : turn.inj) : turn.toFinset.card = k + 1 :=
  match k with
  | 0 => by
    rw [Turns.toFinset_singleton]
    exact Finset.card_singleton _
  | k + 1 => by
    have aux : turn.last ∉ turn.head.toFinset :=
      fun mem => by
        rw [← Turns.at_eq_last, Turns.mem_toFinset_iff] at mem
        rcases mem with ⟨⟨m, h⟩, eq⟩
        change turn.head.at m _ = _ at eq
        rw [Turns.at_head] at eq
        replace eq := inj m (k + 1) (by omega) (le_refl _) eq
        omega
    rw [Turns.toFinset_eq_insert, Finset.card_insert_of_not_mem aux, add_right_cancel_iff]
    exact turn.head.card_toFinset_of_inj (turn.head_inj_of_inj inj)

variable (n)

/--
`LegalTurns n k` collects all the turns with length `k + 1`, with:

• `turn.inj` holds

• the "(i + 1)-th" element of the turn satisfies the basic rule of the game, i.e., the "(i + 1)-th" element is always in the boundary of the finset formed by the first `i` elements.

As a result, `LegalTurns n k` represents the collective of all possible game process of length `k + 1`.
-/
structure LegalTurns (k : ℕ) where
  turn : Turns n (k + 1)
  inj : turn.inj
  legal : ∀ i (h : i < k), turn.at (i + 1) (Nat.succ_le.mpr h) ∈ Fin.boundary ((turn.first i (le_of_lt h)).toFinset)ᶜ

variable {n}

/--
A constructor of making a `legal_turn : LegalTurns n 0`.
-/
def LegalTurns_of_single (x : Fin (n + 1)) : LegalTurns n 0 := {
  turn :=
    Turns.next Turns.init x
  inj :=
    fun _ _ hi hj eq => by
      omega
  legal :=
    fun i hi =>
      False.elim <| Nat.not_lt_zero i hi
}

/--
Add a specific move to a certain game process of length `k + 1` to get the result process of length `k + 1 + 1`.
-/
def LegalTurns.mk_of {k : ℕ} (legal_turn : LegalTurns n k) (x : Fin (n + 1)) (h₁ : x ∉ legal_turn.turn.toFinset) (h₂ : x ∈ Fin.boundary legal_turn.turn.toFinsetᶜ) : LegalTurns n (k + 1) := {
  turn :=
    Turns.next legal_turn.turn x
  inj :=
    fun i j hi hj eq => by
      contrapose! eq
      wlog h : i < j generalizing i j with H
      · push_neg at h
        exact (H j i hj hi eq.symm (lt_of_le_of_ne h eq.symm)).symm
      · if h' : j = k + 1 then
          conv =>
            enter [2, 2]
            rw [h']
          rw [Turns.at_next_eq, Turns.at_next_eq_at _ _ (by omega)]
          by_contra eq'
          refine h₁ ?_
          rw [Turns.mem_toFinset_iff]
          exists ⟨i, show i ≤ k by omega⟩
        else
          rw [Turns.at_next_eq_at _ _ (by omega), Turns.at_next_eq_at _ _ (by omega)]
          by_contra eq'
          exact eq <| legal_turn.inj i j (by omega) (by omega) eq'
  legal :=
    fun i hi => by
      simp only [Turns.at]
      split <;> rename _ => h₃
      · conv =>
          enter [1, 1, 1, 1]
          rw [← Turns.first_next _ (by omega)]
        replace h₃ : i = k := Nat.succ_inj'.mp h₃
        subst h₃
        rw [← Turns.first_eq_self, Turns.last_next]
        exact h₂
      · rw [Turns.head_next, ← Turns.first_next _ (by omega)]
        exact legal_turn.legal i (by omega)
}

/--
**TBA**
-/
theorem LegalTurns.turn_mk_of {k : ℕ} (legal_turn : LegalTurns n k) (x : Fin (n + 1)) (h₁ : x ∉ legal_turn.turn.toFinset) (h₂ : x ∈ Fin.boundary legal_turn.turn.toFinsetᶜ) : (legal_turn.mk_of x h₁ h₂).turn = legal_turn.turn.next x :=
  rfl

/--
Take a sub game process of the first `m + 1` turns from a given game process `legal_turn : LegalTurns n k` with length `k + 1`.
-/
def LegalTurns.first {k : ℕ} (legal_turn : LegalTurns n k) (m : ℕ) (h : m ≤ k) : LegalTurns n m := {
  turn :=
    legal_turn.turn.first m h
  inj :=
    fun i j hi hj eq => by
      simp only [Turns.at_first] at eq
      exact legal_turn.inj i j (by omega) (by omega) eq
  legal :=
    fun i hi => by
      simp only [Turns.at_first, Turns.first_first]
      exact legal_turn.legal i (by omega)
}

/--
The underlying turn of `legal_turn.first m _` is just `legal_turn.turn.first m _`.
-/
theorem LegalTurns.turn_first {k : ℕ} (legal_turn : LegalTurns n k) (m : ℕ) (h : m ≤ k) : (legal_turn.first m h).turn = legal_turn.turn.first m h :=
  rfl

/--
For any `legal_turn : LegalTurns n k` and any `x : Fin (n + 1)` which satisfies the "basic rule", `(legal_turn.mk_of x).first k _` is just `legal_turn` itself.
-/
theorem LegalTurns.first_mk_of_eq_self {k : ℕ} (legal_turn : LegalTurns n k) (x : Fin (n + 1)) (h₁ : x ∉ legal_turn.turn.toFinset) (h₂ : x ∈ Fin.boundary legal_turn.turn.toFinsetᶜ) : (legal_turn.mk_of x h₁ h₂).first k (Nat.le_add_right _ _) = legal_turn := by
  rw [LegalTurns.mk.injEq, LegalTurns.turn_first, LegalTurns.turn_mk_of,
    ← Turns.first_next _ (le_refl _), ← Turns.first_eq_self]

/--
For a `legal_turn : LegalTurns n k`, `legal_turn.turn.toFinset` forms some `[a ->> b]`.
-/
theorem LegalTurns.taken_pieces_eq_cIcc {k : ℕ} (legal_turn : LegalTurns n k) : ∃ a b, legal_turn.turn.toFinset = [a ->> b] :=
  match k with
  | 0 => by
    rw [Turns.toFinset_singleton]
    exists legal_turn.turn.last, legal_turn.turn.last
    exact Fin.cIcc_self.symm
  | k + 1 => by
    rw [Turns.toFinset_eq_insert]
    have ith_take := (legal_turn.first k (Nat.le_add_right _ _)).taken_pieces_eq_cIcc
    conv at ith_take =>
      enter [1, a, 1, b, 1, 1]
      change legal_turn.turn.first k (Nat.le_add_right _ _)
      rw [← Turns.first_eq_head]
    rcases ith_take with ⟨a, b, eq_cIcc⟩
    have legal := legal_turn.legal k (lt_add_one k)
    rw [Turns.at_eq_last, ← Turns.first_eq_head, eq_cIcc, Fin.compl_def] at legal
    have h₁ : [a ->> b] ≠ Finset.univ :=
      fun eq_univ => by
        apply_fun fun x => Finset.card x at eq_cIcc
        rw [Turns.card_toFinset_of_inj] at eq_cIcc
        · rw [eq_univ, Finset.card_fin] at eq_cIcc
          have _ := legal_turn.turn.le_of_inj legal_turn.inj
          omega
        · exact legal_turn.turn.head_inj_of_inj legal_turn.inj
    have h₂ : [b + 1 ->> a - 1] ≠ Finset.univ :=
      fun eq_univ => by
        rw [Fin.cIcc_eq_univ, sub_add_cancel, eq_comm, ← Fin.cIcc_eq_univ] at eq_univ
        exact h₁ eq_univ
    rw [Fin.cIcc_compl h₁, Fin.boundary_cIcc h₂, Finset.mem_insert, Finset.mem_singleton] at legal
    conv =>
      enter [1, a, 1, b]
      rw [eq_cIcc]
    cases legal with
    | inl legal =>
      exists a, b + 1
      rw [legal, Fin.cIcc_insert_eq_cIcc_right h₁]
    | inr legal =>
      exists a - 1, b
      rw [legal, Fin.cIcc_insert_eq_cIcc_left h₁]

end Turn

/-
**NOTE** Initially, we define `Strategies n` for only even turns. But **Prop 1.3** in the original paper yields some strategy for Bob. For flexibility, we remove the "even" condition, so now a `strategy : Strategies n` can either acts on even turns or on odd turns, i.e. restricts either Alice's moves or Bob's moves.
-/
/--
`Strategies n` is defined as an abbreviation of `Cuts n → Turns n → Fin (n + 1) → Prop`.

`strategy cut turn i` is the condition Alice or Bob should follow in the i-th turn.
-/
abbrev Strategies := Cuts n → (k : ℕ) → Set (LegalTurns n k)

variable {n}

class Strategies.Valid (cut : Cuts n) (strategy : Strategies n) : Prop where
  init : ∃ x, LegalTurns_of_single x ∈ strategy cut 0
  recursive : ∀ i < n, ∀ legal_turn ∈ strategy cut i,
    ∃ x : {x : Fin (n + 1) // x ∉ legal_turn.turn.toFinset ∧ x ∈ Fin.boundary legal_turn.turn.toFinsetᶜ},
      legal_turn.mk_of x.val x.property.left x.property.right ∈ strategy cut (i + 1)

end Fundamental

section GameDef

variable {n : ℕ}

/-
Note: `cut : Cuts n` and `strategy : Strategies n` are not designed as fields, because they are varying for different results, and it's convenient to treat them as parameters of `Game` for providing the `Nonempty` instance in this way.
-/
/--
A `Game` contains two data, along with a prop:

• a `cut : Cuts n` describing the division of the pizza

• a `legal_turn : LegalTurns n n` describing the process of the game

• a `strategy : Strategies n` restricting both players' moves

• `good : ∀ i (h : i ≤ n), (legal_turn.first i h) ∈ strategy cut i` showing the game process follows the given strategy
-/
structure Game (cut : Cuts n) (strategy : Strategies n) where
  legal_turn : LegalTurns n n
  good : ∀ i (h : i ≤ n), (legal_turn.first i h) ∈ strategy cut i

/--
`Game.result` is the total area Alice can get under `strategy : Strategies`. The strategy is required to be **VALID**, i.e. an instance for `Valid strategy` is needed.
-/
def Game.result {cut : Cuts n} {strategy : Strategies n} [Strategies.Valid cut strategy] (game : Game cut strategy) : ℝ :=
  ∑ i : Fin (n + 1) with Even i.val, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i))

end GameDef

end Pizza

/-!
**NOTE** We should design Alice's Strategies and Bob's Strategies as types separately. Because when we want to express "whatever strategy Bob takes", we shall put an arbitrary `strategy : Strategies n` and this might have some restrictions on Alice's turns.
**REMARK** We use `fun _ _ _ => True` to represent "whatever strategy sb. takes", so no need to add another type so far.
**REMARK** It seems no need to split a strategy into two parts. If we combine them together, the combined one works well the same...
-/


/-!
In this part, we prove the even case.
-/

section AuxLem

theorem Nat.odd_iff_odd_add_one_add_one (n : ℕ) : Odd n ↔ Odd (n + 1 + 1) := calc
    _ ↔ Even (n + 1) := by
      rw [Nat.even_add_one, Nat.not_even_iff_odd]
    _ ↔ _ := by
      rw [Nat.odd_add_one, Nat.not_odd_iff_even]

theorem Nat.even_iff_even_add_one_add_one (n : ℕ) : Even n ↔ Even (n + 1 + 1) := by
  rw [← not_iff_not, Nat.not_even_iff_odd, Nat.not_even_iff_odd]
  exact odd_iff_odd_add_one_add_one _

theorem Nat.odd_iff_odd_two_mul_add (n m : ℕ) : Odd n ↔ Odd (2 * m + n) := by
  have h := even_two_mul m
  constructor <;> intro h'
  · exact Even.add_odd h h'
  · convert Odd.sub_even ?_ h' h
    · exact Nat.eq_sub_of_add_eq' rfl
    · exact le_add_right (2 * m) n

theorem Nat.even_iff_even_two_mul_add (n m : ℕ) : Even n ↔ Even (2 * m + n) := by
  rw [← not_iff_not, Nat.not_even_iff_odd, Nat.not_even_iff_odd]
  exact Nat.odd_iff_odd_two_mul_add _ _

end AuxLem

namespace Pizza
namespace Evencase

variable {n : ℕ} [Fact (Even (n + 1))]

theorem fin_val_one : (1 : Fin (n + 1)).val = 1 := by
  have even_case : Even (n + 1) := Fact.out
  rw [Fin.val_one', Nat.mod_eq_iff_lt]
  · by_contra! h
    nth_rw 2 [← zero_add 1] at h
    rw [add_le_add_iff_right, Nat.le_zero] at h
    rw [h, zero_add] at even_case
    exact Nat.not_even_one even_case
  · omega

theorem fin_val_parity (a : Fin (n + 1)) : Odd a.val ↔ ¬Odd (a + 1).val := by
  have even_case : Even (n + 1) := Fact.out
  if h : a = Fin.last n then
    rw [h, Fin.val_last, Fin.last_add_one, Fin.val_zero]
    rw [Nat.even_add_one, Nat.not_even_iff_odd] at even_case
    have _ := Nat.not_odd_zero
    tauto
  else
    rw [Fin.val_add_one, if_neg h, ← not_iff_not, not_not]
    exact Nat.odd_add_one.symm

theorem fin_val_parity' (a : Fin (n + 1)) : Even a.val ↔ ¬Even (a + 1).val := by
  have even_case : Even (n + 1) := Fact.out
  rw [← Nat.not_odd_iff_even, Nat.not_even_iff_odd]
  exact Decidable.not_iff_comm.mp (fin_val_parity a).symm


variable (n)

/--
The strategy Alice takes when the number of pieces is even. Let's denote `A` the sum of area of the pieces with even indices and `B` the sum of area of the pieces with odd indices.

• In the 0-th turn, if `A ≥ B`, Alice takes piece 0, or she takes piece 1.

• In other turns, Alice always takes the piece which shares the same parity with the one she took in the 0-th turn.
-/
def evenCase : Strategies n :=
  fun cut i =>
    match i with
    | 0 =>
      if ∑ i with Even i.val, cut.area i ≤ ∑ i with Odd i.val, cut.area i then
        {legal_turn | Odd legal_turn.turn.last.val}
      else
        {legal_turn | Even legal_turn.turn.last.val}
    | i + 1 =>
      if Even (i + 1) then
        if ∑ i with Even i.val, cut.area i ≤ ∑ i with Odd i.val, cut.area i then
          {legal_turn | Odd legal_turn.turn.last.val ∧ legal_turn.first i (Nat.le_add_right _ _) ∈ evenCase cut i}
        else
          {legal_turn | Even legal_turn.turn.last.val ∧ legal_turn.first i (Nat.le_add_right _ _) ∈ evenCase cut i}
      else
        {legal_turn | legal_turn.first i (Nat.le_add_right _ _) ∈ evenCase cut i}

variable {n}

instance valid_even_case {cut : Cuts n} : Strategies.Valid cut (evenCase n) := {
  init := by
    simp only [evenCase]
    split <;> simp only [Set.mem_setOf]
    · exists 1
      show Odd (Turns.next Turns.init 1).last.val
      rw [Turns.last_next, fin_val_one]
      exact Nat.odd_iff.mpr rfl
    · exists 0
      show Even (Turns.next Turns.init 0).last.val
      rw [Turns.last_next, Fin.val_zero]
      exact Nat.even_iff.mpr rfl
  recursive :=
    fun i hi legal_turn mem => by
      have even_case : Even (n + 1) := Fact.out
      simp only [evenCase]
      obtain ⟨a, b, eq_cIcc⟩ := legal_turn.taken_pieces_eq_cIcc
      have h₁ : [a ->> b] ≠ Finset.univ :=
        fun eq_univ => by
          apply_fun fun x => Finset.card x at eq_cIcc
          rw [Turns.card_toFinset_of_inj] at eq_cIcc
          · rw [eq_univ, Finset.card_fin] at eq_cIcc
            have _ := legal_turn.turn.le_of_inj legal_turn.inj
            omega
          · exact legal_turn.inj
      have h₂ : [b + 1 ->> a - 1] ≠ Finset.univ :=
        fun eq_univ => by
          rw [Fin.cIcc_eq_univ, sub_add_cancel, eq_comm, ← Fin.cIcc_eq_univ] at eq_univ
          exact h₁ eq_univ
      split <;> rename _ => h
      · have aux : Even (a - 1).val ↔ ¬Even (b + 1).val := by
          have h₃ : Even [a ->> b].card := by
            rw [← eq_cIcc, Turns.card_toFinset_of_inj _ legal_turn.inj]
            exact h
          rw [Fin.card_cIcc, Nat.even_add_one, Nat.not_even_iff_odd] at h₃
          if h₄ : a ≤ b then
            rw [Fin.coe_sub_iff_le.mpr h₄] at h₃
            constructor <;> intro h₅
            · have h₆ : ¬a = 0 :=
                fun eq => by
                  rw [eq, ← Fin.last_add_one, add_sub_cancel_right, Fin.val_last] at h₅
                  exact Nat.even_add_one.mp even_case h₅
              replace h₆ : 1 ≤ a := by
                rw [← Fin.val_inj, Fin.val_zero] at h₆
                rw [Fin.le_def, fin_val_one]
                omega
              rw [Fin.coe_sub_iff_le.mpr h₆, fin_val_one] at h₅
              replace h₃ := Odd.add_even h₃ h₅
              rw [Fin.le_def] at h₄
              rw [Fin.le_def, fin_val_one] at h₆
              rw [← Nat.add_sub_assoc h₆, Nat.sub_add_cancel h₄, Nat.odd_iff_odd_add_one_add_one, Nat.sub_add_cancel (le_trans h₆ h₄)] at h₃
              have h₇ : ¬b = Fin.last _ :=
                fun eq => by
                  rw [eq, Fin.val_last] at h₃
                  exact Nat.not_even_iff_odd.mpr h₃ even_case
              rw [Fin.val_add_one, if_neg h₇, Nat.not_even_iff_odd]
              exact h₃
            · have h₆ : ¬b = Fin.last _ :=
                fun eq => by
                  rw [eq, Fin.last_add_one, Fin.val_zero] at h₅
                  exact h₅ <| Nat.even_iff.mpr rfl
              rw [Nat.not_even_iff_odd, Fin.val_add_one, if_neg h₆] at h₅
              have h₇ : ¬a = 0 :=
                fun eq => by
                  rw [eq, Fin.val_zero, Nat.sub_zero] at h₃
                  exact Nat.odd_add_one.mp h₅ h₃
              replace h₇ : 1 ≤ a := by
                rw [← Fin.val_inj, Fin.val_zero] at h₇
                rw [Fin.le_def, fin_val_one]
                omega
              by_contra h₈
              rw [Nat.not_even_iff_odd, Fin.coe_sub_iff_le.mpr h₇, fin_val_one] at h₈
              replace h₃ := Odd.add_odd h₃ h₈
              rw [Fin.le_def] at h₄
              rw [Fin.le_def, fin_val_one] at h₇
              rw [← Nat.add_sub_assoc h₇, Nat.sub_add_cancel h₄, Nat.even_iff_even_add_one_add_one, Nat.sub_add_cancel (le_trans h₇ h₄)] at h₃
              exact Nat.not_odd_iff_even.mpr h₃ h₅
          else
            push_neg at h₄
            rw [Fin.coe_sub_iff_lt.mpr h₄] at h₃
            have h₅ : ¬a = 0 :=
              fun eq => by
                exact Fin.ne_zero_of_lt h₄ eq
            have h₆ : ¬b = Fin.last _ :=
              fun eq => by
                exact Fin.ne_last_of_lt h₄ eq
            replace h₅ : 1 ≤ a := by
              rw [← Fin.val_inj, Fin.val_zero] at h₅
              rw [Fin.le_def, fin_val_one]
              omega
            rw [Fin.coe_sub_iff_le.mpr h₅, fin_val_one, Fin.val_add_one, if_neg h₆]
            rw [Fin.le_def, fin_val_one] at h₅
            constructor <;> intro h₇
            · replace h₃ := Odd.add_even h₃ h₇
              rw [← Nat.add_sub_assoc h₅, Nat.sub_add_cancel (by omega),
                add_assoc, add_comm 1, ← add_assoc, Nat.add_sub_cancel] at h₃
              replace h₃ := Odd.add_even h₃ even_case
              rw [← add_assoc, add_assoc _ b.val, add_comm _ n, ← add_assoc, ← two_mul, add_assoc] at h₃
              rw [Nat.not_even_iff_odd]
              exact (Nat.odd_iff_odd_two_mul_add _ _).mpr h₃
            · by_contra h₈
              rw [Nat.not_even_iff_odd] at h₇ h₈
              replace h₃ := Odd.add_odd h₃ h₈
              rw [← Nat.add_sub_assoc h₅, Nat.sub_add_cancel (by omega),
                add_assoc, add_comm 1, ← add_assoc, Nat.add_sub_cancel_right] at h₃
              replace h₃ := Even.add_odd h₃ h₇
              rw [← add_assoc, add_assoc n, ← two_mul, add_comm n, add_assoc] at h₃
              exact Nat.not_even_iff_odd.mpr ((Nat.odd_iff_odd_two_mul_add _ _).mpr h₃) even_case
        split <;> rename _ => h' <;> simp only [Set.mem_setOf, LegalTurns.turn_mk_of, Turns.last_next, LegalTurns.first_mk_of_eq_self]
        · if h₃ : Even (a - 1).val then
            replace h₃ := Nat.not_even_iff_odd.mp <| aux.mp h₃
            refine Exists.intro ⟨b + 1, ?_, ?_⟩ ⟨h₃, mem⟩
            · rw [eq_cIcc]
              exact Fin.right_not_mem_cIcc_of_ne_univ h₁
            · rw [eq_cIcc, Fin.compl_def, Fin.cIcc_compl h₁, Fin.boundary_cIcc h₂, Finset.mem_insert]
              exact Or.inl rfl
          else
            replace h₃ := Nat.not_even_iff_odd.mp h₃
            refine Exists.intro ⟨a - 1, ?_, ?_⟩ ⟨h₃, mem⟩
            · rw [eq_cIcc]
              exact Fin.left_not_mem_cIcc_of_ne_univ h₁
            · rw [eq_cIcc, Fin.compl_def, Fin.cIcc_compl h₁, Fin.boundary_cIcc h₂, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr rfl
        · if h₃ : Even (a - 1).val then
            refine Exists.intro ⟨a - 1, ?_, ?_⟩ ⟨h₃, mem⟩
            · rw [eq_cIcc]
              exact Fin.left_not_mem_cIcc_of_ne_univ h₁
            · rw [eq_cIcc, Fin.compl_def, Fin.cIcc_compl h₁, Fin.boundary_cIcc h₂, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr rfl
          else
            replace h₃ : Even (b + 1).val := by
              by_contra h₄
              exact h₃ <| aux.mpr h₄
            refine Exists.intro ⟨b + 1, ?_, ?_⟩ ⟨h₃, mem⟩
            · rw [eq_cIcc]
              exact Fin.right_not_mem_cIcc_of_ne_univ h₁
            · rw [eq_cIcc, Fin.compl_def, Fin.cIcc_compl h₁, Fin.boundary_cIcc h₂, Finset.mem_insert]
              exact Or.inl rfl
      · refine Exists.intro (Subtype.mk (b + 1) ?_) ?_
        · rw [eq_cIcc, Fin.compl_def, Fin.cIcc_compl h₁, Fin.boundary_cIcc h₂, Finset.mem_insert]
          exact ⟨Fin.right_not_mem_cIcc_of_ne_univ h₁, Or.inl rfl⟩
        · simp only [Set.mem_setOf, legal_turn.first_mk_of_eq_self]
          exact mem
}

/-
Remark 03/28/25

We should put the `even_case` condition into the definition of `evenCast : Strategies n`, and as a result, we do not need `even_case` in the instance of `Valid ...`.

Don't know it is good enough...

I'm afraid that there are some circumstances where we cannot give a specific choice for the player, and as a result, we have to give extra conditions when give the instance of `Valid ...`...

But at the first glance, it seems impossible...

Fake Remark!!
I didn't remark this! XD
-/
theorem main {cut : Cuts n} (game : Game cut (evenCase n)) : game.result ≥ 1 / 2 := by
  let A := {a : Fin (n + 1) | Odd a.val}.toFinset
  let B := {a : Fin (n + 1) | Even a.val}.toFinset
  have auxA (a : Fin (n + 1)) : Odd a.val ↔ a ∈ A := by
    rw [Set.mem_toFinset]
    rfl
  have auxB (a : Fin (n + 1)) : Even a.val ↔ a ∈ B := by
    rw [Set.mem_toFinset]
    rfl
  have auxCompl : A = Bᶜ := by
    ext x
    rw [← auxA, Finset.mem_compl, ← auxB]
    exact Nat.not_even_iff_odd.symm
  have auxCard : A.card = B.card := by
    refine Finset.card_bijective (fun i => i + 1) ?_ (fun i => ?_)
    · exact AddGroup.addRight_bijective 1
    · show _ ↔ i + 1 ∈ B
      simp only [A, B, Set.mem_toFinset, Set.mem_setOf]
      rw [← Nat.not_odd_iff_even]
      exact fin_val_parity i
  have auxSumEq : ∑ i : Fin (n + 1), cut.area (game.legal_turn.turn.at i.val (Fin.is_le _)) = ∑ i : Fin (n + 1), cut.area i := by
    refine Finset.sum_bijective (fun i => game.legal_turn.turn.at i.val (Fin.is_le i)) ?_ ?_ (fun _ _ => rfl)
    · have h₃ : Function.Injective (fun i => game.legal_turn.turn.at i.val (Fin.is_le i)) :=
        fun i j eq =>
          Fin.val_inj.mp <| game.legal_turn.inj i j (Fin.is_le _) (Fin.is_le _) eq
      exact Finite.injective_iff_bijective.mp h₃
    · exact fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩
  have lem₁ : ∑ i : Fin (n + 1) with Odd i.val, cut.area (game.legal_turn.turn.at i.val (Fin.is_le _)) ≤ ∑ i : Fin (n + 1) with Even i.val, cut.area (game.legal_turn.turn.at i.val (Fin.is_le _)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    simp_rw [auxA, auxB]
    repeat rw [Finset.sum_ite_mem, Finset.inter_comm, Finset.inter_univ]
    have h₁ := game.good
    if h₂ : ∑ i with Even i.val, cut.area i
    ≤ ∑ i with Odd i.val, cut.area i then
      have aux₁ : ∑ i ∈ B, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) = ∑ i ∈ A, cut.area i := by
        have h₃ (i : Fin (n + 1)) (mem : i ∈ B) : (fun i x => game.legal_turn.turn.at i.val (Fin.is_le _)) i mem ∈ A := by
          show game.legal_turn.turn.at _ _ ∈ _
          rw [Set.mem_toFinset, Set.mem_setOf] at mem ⊢
          replace h₁ := h₁ i (Fin.is_le _)
          match i with
          | Fin.mk i is_lt =>
            change Even i at mem
            change game.legal_turn.first i _ ∈ evenCase n cut i at h₁
            change Odd (game.legal_turn.turn.at i _).val
            match i with
            | 0 =>
              simp only [evenCase, if_pos h₂, Set.mem_setOf, LegalTurns.turn_first, Turns.last_first] at h₁
              exact h₁
            | i + 1 =>
              simp only [evenCase, if_pos mem, if_pos h₂, Set.mem_setOf, LegalTurns.turn_first, Turns.last_first] at h₁
              exact h₁.left
        refine Finset.sum_bij (fun i _ => game.legal_turn.turn.at i.val (Fin.is_le i))
          (fun i mem => h₃ i mem) (fun a₁ _ a₂ _ eq => Fin.val_inj.mp <| game.legal_turn.inj _ _ _ _ eq)
            (fun b mem => ?_) (fun _ _ => rfl)
        have h₄ : Function.Injective (fun i => game.legal_turn.turn.at i.val (Fin.is_le i)) :=
          fun i j eq =>
            Fin.val_inj.mp <| game.legal_turn.inj i.val j.val (Fin.is_le _) (Fin.is_le _) eq
        have h₅ : Finset.map ⟨_, h₄⟩ B = A := by
          refine Finset.eq_of_subset_of_card_le (fun j mem' => ?_) (le_of_eq <| ?_)
          · rw [Finset.mem_map] at mem'
            rcases mem' with ⟨i, mem', eq⟩
            convert h₃ i mem'
            exact eq.symm
          · rw [Finset.card_map]
            exact auxCard
        rw [← h₅, Finset.mem_map] at mem
        rcases mem with ⟨a, mem, eq⟩
        exists a, mem
      have aux₂ : ∑ i ∈ A, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) = ∑ i ∈ B, cut.area i := calc
        _ = ∑ i, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) - ∑ i ∈ B, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) := by
          rw [auxCompl, ← Finset.sum_compl_add_sum B]
          linarith
        _ = ∑ i : Fin (n + 1), cut.area i - ∑ i ∈ B, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) := by
          rw [sub_left_inj]
          exact auxSumEq
        _ = _ := by
          rw [aux₁, auxCompl, ← Finset.sum_compl_add_sum B]
          linarith
      rw [aux₁, aux₂]
      rw [Finset.sum_filter, Finset.sum_filter] at h₂
      simp_rw [auxA, auxB] at h₂
      repeat rw [Finset.sum_ite_mem, Finset.inter_comm, Finset.inter_univ] at h₂
      exact h₂
    else
      have aux₁ : ∑ i ∈ B, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) = ∑ i ∈ B, cut.area i := by
        have h₃ (i : Fin (n + 1)) (mem : i ∈ B) : (fun i x => game.legal_turn.turn.at i.val (Fin.is_le _)) i mem ∈ B := by
          show game.legal_turn.turn.at _ _ ∈ _
          rw [Set.mem_toFinset, Set.mem_setOf] at mem ⊢
          replace h₁ := h₁ i (Fin.is_le _)
          match i with
          | Fin.mk i is_lt =>
            change Even i at mem
            change game.legal_turn.first i _ ∈ evenCase n cut i at h₁
            change Even (game.legal_turn.turn.at i _).val
            match i with
            | 0 =>
              simp only [evenCase, if_neg h₂, Set.mem_setOf, LegalTurns.turn_first, Turns.last_first] at h₁
              exact h₁
            | i + 1 =>
              simp only [evenCase, if_pos mem, if_neg h₂, Set.mem_setOf, LegalTurns.turn_first, Turns.last_first] at h₁
              exact h₁.left
        refine Finset.sum_bij (fun i _ => game.legal_turn.turn.at i.val (Fin.is_le i))
          (fun i mem => h₃ i mem) (fun a₁ _ a₂ _ eq => Fin.val_inj.mp <| game.legal_turn.inj _ _ _ _ eq)
            (fun b mem => ?_) (fun _ _ => rfl)
        have h₄ : Function.Injective (fun i => game.legal_turn.turn.at i.val (Fin.is_le i)) :=
          fun i j eq =>
            Fin.val_inj.mp <| game.legal_turn.inj i.val j.val (Fin.is_le _) (Fin.is_le _) eq
        have h₅ : Finset.map ⟨_, h₄⟩ B = B := by
          refine Finset.eq_of_subset_of_card_le (fun j mem' => ?_) (le_of_eq <| ?_)
          · rw [Finset.mem_map] at mem'
            rcases mem' with ⟨i, mem', eq⟩
            convert h₃ i mem'
            exact eq.symm
          · rw [Finset.card_map]
        rw [← h₅, Finset.mem_map] at mem
        rcases mem with ⟨a, mem, eq⟩
        exists a, mem
      have aux₂ : ∑ i ∈ A, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) = ∑ i ∈ A, cut.area i := calc
        _ = ∑ i, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) - ∑ i ∈ B, cut.area (game.legal_turn.turn.at i.val (Fin.is_le i)) := by
          rw [auxCompl, ← Finset.sum_compl_add_sum B]
          linarith
        _ = ∑ i : Fin (n + 1), cut.area i - ∑ i ∈ B, cut.area i := by
          rw [← aux₁, sub_left_inj]
          exact auxSumEq
        _ = _ := by
          rw [auxCompl, ← Finset.sum_compl_add_sum B]
          linarith
      rw [aux₁, aux₂]
      rw [Finset.sum_filter, Finset.sum_filter] at h₂
      simp_rw [auxA, auxB] at h₂
      repeat rw [Finset.sum_ite_mem, Finset.inter_comm, Finset.inter_univ] at h₂
      exact le_of_lt <| lt_of_not_le h₂
  have lem₂ : ∑ i : Fin (n + 1) with Odd i.val, cut.area (game.legal_turn.turn.at i.val _) + ∑ i : Fin (n + 1) with Even i.val, cut.area (game.legal_turn.turn.at i.val _) = 1 := calc
    _ = ∑ i : Fin (n + 1), cut.area (game.legal_turn.turn.at i.val _) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      conv =>
        enter [1, 2, 2, x, 1]
        rw [auxB, ← compl_compl B, ← auxCompl]
      conv =>
        enter [1, 1, 2, x, 1]
        rw [auxA]
      repeat rw [Finset.sum_ite_mem, Finset.inter_comm, Finset.inter_univ]
      exact Finset.sum_add_sum_compl _ _
    _ = _ := by
      rw [← cut.sum_eq_one]
      exact auxSumEq
  rw [← add_le_add_iff_right (∑ i : Fin (n + 1) with Even i.val, cut.area (game.legal_turn.turn.at i.val _))] at lem₁
  rw [← two_mul, lem₂] at lem₁
  simp only [Game.result]
  linarith

end Evencase
end Pizza

/-
Things below are still old school. We need some fancy definitions.
-/

section

variable {n : ℕ}

def red_pieces (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  {x | x ∈ Fin.cIcc a b ∧ Even (x - a).val}.toFinset

def green_pieces (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  {x | x ∈ Fin.cIcc a b ∧ Odd (x - a).val}.toFinset

def red_pieces₀ (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  {x | x ∈ Fin.cIcc a b ∧ Even (b - x).val}.toFinset

def green_pieces₀ (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  {x | x ∈ Fin.cIcc a b ∧ Odd (b - x).val}.toFinset

theorem mem_red_pieces {a b : Fin (n + 1)} (x : Fin (n + 1)) : x ∈ red_pieces a b ↔ x ∈ Fin.cIcc a b ∧ Even (x - a).val := by
  simp only [red_pieces]
  rw [Set.mem_toFinset, Set.mem_setOf]

theorem mem_green_pieces {a b : Fin (n + 1)} (x : Fin (n + 1)) : x ∈ green_pieces a b ↔ x ∈ Fin.cIcc a b ∧ Odd (x - a).val := by
  simp only [green_pieces]
  rw [Set.mem_toFinset, Set.mem_setOf]

theorem mem_red_pieces₀ {a b : Fin (n + 1)} (x : Fin (n + 1)) : x ∈ red_pieces₀ a b ↔ x ∈ Fin.cIcc a b ∧ Even (b - x).val := by
  simp only [red_pieces₀]
  rw [Set.mem_toFinset, Set.mem_setOf]

theorem mem_green_pieces₀ {a b : Fin (n + 1)} (x : Fin (n + 1)) : x ∈ green_pieces₀ a b ↔ x ∈ Fin.cIcc a b ∧ Odd (b - x).val := by
  simp only [green_pieces₀]
  rw [Set.mem_toFinset, Set.mem_setOf]

theorem red_pieces_eq_cIcc_sdiff_green_pieces {a b : Fin (n + 1)} : red_pieces a b = Fin.cIcc a b \ green_pieces a b := by
  ext x
  rw [mem_red_pieces, Finset.mem_sdiff, mem_green_pieces]
  constructor <;> intro mem
  · rw [not_and_or]
    exact ⟨mem.left, Or.inr <| Nat.not_odd_iff_even.mpr mem.right⟩
  · exact ⟨mem.left, by
      push_neg at mem
      exact Nat.not_odd_iff_even.mp <| mem.right mem.left⟩

theorem red_pieces_same_of_odd_length {a b : Fin (n + 1)} (h : Odd ((b - a).val + 1)) : red_pieces a b = red_pieces₀ a b := by
  ext x
  rw [mem_red_pieces, mem_red_pieces₀, ← Fin.val_sub_add_eq_iff_mem_cIcc]
  constructor <;> intro ⟨h₁, h₂⟩
  · exact ⟨h₁, by
      by_contra h₃
      rw [Nat.not_even_iff_odd] at h₃
      exact Nat.not_even_iff_odd.mpr h <| Odd.add_odd (h₁ ▸ Even.add_odd h₂ h₃) odd_one⟩
  · exact ⟨h₁, by
      by_contra h₃
      rw [Nat.not_even_iff_odd] at h₃
      exact Nat.not_even_iff_odd.mpr h <| Odd.add_odd (h₁ ▸ Odd.add_even h₃ h₂) odd_one⟩

theorem red_pieces_eq_green_pieces₀_of_even_length {a b : Fin (n + 1)} (h : Even ((b - a).val + 1)) : red_pieces a b = green_pieces₀ a b := by
  ext x
  rw [mem_red_pieces, mem_green_pieces₀]
  constructor <;> intro mem
  · exact ⟨mem.left, by
      have h₁ := (Fin.val_sub_add_eq_iff_mem_cIcc _).mpr mem.left
      by_contra h₂
      apply Nat.not_odd_iff_even.mp at h₂
      replace h₂ := h₁ ▸ Even.add mem.right h₂
      exact Nat.even_add_one.mp h h₂⟩
  · exact ⟨mem.left, by
      have h₁ := (Fin.val_sub_add_eq_iff_mem_cIcc _).mpr mem.left
      by_contra h₂
      apply Nat.not_even_iff_odd.mp at h₂
      replace h₂ := h₁ ▸ Odd.add_odd h₂ mem.right
      exact Nat.even_add_one.mp h h₂⟩

theorem green_pieces_eq_red_pieces₀_of_even_length {a b : Fin (n + 1)} (h : Even ((b - a).val + 1)) : green_pieces a b = red_pieces₀ a b := by
  ext x
  rw [mem_green_pieces, mem_red_pieces₀]
  constructor <;> intro mem
  · exact ⟨mem.left, by
      have h₁ := (Fin.val_sub_add_eq_iff_mem_cIcc _).mpr mem.left
      by_contra h₂
      apply Nat.not_even_iff_odd.mp at h₂
      replace h₂ := h₁ ▸ Odd.add_odd mem.right h₂
      exact Nat.even_add_one.mp h h₂⟩
  · exact ⟨mem.left, by
      have h₁ := (Fin.val_sub_add_eq_iff_mem_cIcc _).mpr mem.left
      by_contra h₂
      apply Nat.not_odd_iff_even.mp at h₂
      replace h₂ := h₁ ▸ Even.add h₂ mem.right
      exact Nat.even_add_one.mp h h₂⟩



end


/-
This method is stll not right. We need Alice and Bob not symmetric.

Update 03/29/25: Now it's right :-)
-/
