import Mathlib.Tactic

open Classical

section basic

variable {n : ℕ}

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

noncomputable def Fin.cIcc (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  if a = b then
    {a}
  else
    {x | btw a x b}.toFinset

theorem Fin.left_mem_cIcc {a b : Fin (n + 1)} : a ∈ Fin.cIcc a b := by
  simp only [Fin.cIcc]
  if h : a = b then
    rw [if_pos h, Finset.mem_singleton]
  else
    rw [if_neg h, Set.mem_toFinset, Set.mem_setOf]
    exact btw_rfl_left

theorem Fin.right_mem_cIcc {a b : Fin (n + 1)} : b ∈ Fin.cIcc a b := by
  simp only [Fin.cIcc]
  if h : a = b then
    rw [if_pos h, h, Finset.mem_singleton]
  else
    rw [if_neg h, Set.mem_toFinset, Set.mem_setOf]
    exact btw_refl_right _ _

theorem Fin.mem_cIcc_of_ne {a b : Fin (n + 1)} (h : a ≠ b) (x : Fin (n + 1)) : x ∈ Fin.cIcc a b ↔ btw a x b := by
  simp only [Fin.cIcc]
  rw [if_neg h, Set.mem_toFinset]
  exact Set.mem_setOf

theorem Fin.mem_cIcc_self {a : Fin (n + 1)} (x : Fin (n + 1)) : x ∈ Fin.cIcc a a ↔ x = a := by
  simp only [Fin.cIcc, if_pos]
  exact Finset.mem_singleton

theorem Fin.cIcc_self {a : Fin (n + 1)} : Fin.cIcc a a = {a} := by
  ext x
  rw [Finset.mem_singleton]
  exact Fin.mem_cIcc_self _

theorem Fin.mem_cIcc_or {a b : Fin (n + 1)} (h : a ≠ b) (x : Fin (n + 1)) : x ∈ Fin.cIcc a b ∨ x ∈ Fin.cIcc b a := by
  rw [Fin.mem_cIcc_of_ne h, Fin.mem_cIcc_of_ne h.symm]
  exact btw_total _ _ _

theorem Fin.mem_cIcc_antisymm {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ Fin.cIcc a b ∧ x ∈ Fin.cIcc b a ↔ x = a ∨ x = b := by
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

theorem Fin.sub_one_mem_cIcc {a : Fin (n + 1)} : ∀ b, a ≠ b → a - 1 ∈ Fin.cIcc b a := by
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

theorem Fin.add_one_mem_cIcc {a : Fin (n + 1)} : ∀ b, a ≠ b → a + 1 ∈ Fin.cIcc a b := by
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

theorem Fin.val_sub_add_eq_iff_mem_cIcc {a b : Fin (n + 1)} (x : Fin (n + 1)) : (x - a).val + (b - x).val = (b - a).val ↔ x ∈ Fin.cIcc a b := by
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

/- `length + 1` is the real length, maybe we will modify the definition here later. -/
noncomputable def Fin.continuous_segment (a : Fin (n + 1)) (length : ℕ) : Finset (Fin (n + 1)) :=
  {x | ∃ m, 0 ≤ m ∧ m ≤ length ∧ x = a + m}.toFinset

theorem Fin.cIcc_eq_continuous_segment {a b : Fin (n + 1)} : Fin.cIcc a b = Fin.continuous_segment a (b - a).val := by
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

theorem Fin.mem_continuous_segment {a : Fin (n + 1)} {length : ℕ} (x : Fin (n + 1)) : x ∈ a.continuous_segment length ↔ ∃ n, 0 ≤ n ∧ n ≤ length ∧ x = a + n := by
  simp only [Fin.continuous_segment]
  rw [Set.mem_toFinset]
  exact Set.mem_setOf

theorem Fin.cIcc_card_eq {a b : Fin (n + 1)} : (Fin.cIcc a b).card = (b - a).val + 1 := by
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

theorem Fin.cIcc_eq_univ {a b : Fin (n + 1)} : Fin.cIcc a b = Finset.univ ↔ a = b + 1 := by
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
    rw [Fin.cIcc_card_eq, Fintype.card_fin]
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

theorem Fin.cIcc_self_eq_univ_iff_fin_one {a : Fin (n + 1)} : Fin.cIcc a a = Finset.univ ↔ n = 0 := by
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

theorem Fin.cIcc_eq_univ_of_fin_one {a b : Fin (n + 1)} (h : n = 0) : Fin.cIcc a b = Finset.univ := by
  subst h
  rw [Fin.cIcc_eq_univ]
  omega

theorem Fin.cIcc_subset_right {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ Fin.cIcc a b → Fin.cIcc x b ⊆ Fin.cIcc a b := by
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

theorem Fin.cIcc_subset_left {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ Fin.cIcc a b → Fin.cIcc a x ⊆ Fin.cIcc a b := by
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

theorem Fin.cIcc_sdiff_endpoint_left {a b : Fin (n + 1)} (h : a ≠ b) : Fin.cIcc a b \ {a} = Fin.cIcc (a + 1) b := by
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

theorem Fin.cIcc_sdiff_endpoint_right {a b : Fin (n + 1)} (h : a ≠ b) : Fin.cIcc a b \ {b} = Fin.cIcc a (b - 1) := by
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

theorem Fin.cIcc_compl {a b : Fin (n + 1)} (h : Fin.cIcc a b ≠ Finset.univ) : Finset.univ \ (Fin.cIcc a b) = Fin.cIcc (b + 1) (a - 1) := by
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

end basic

section

variable (n : ℕ)

/- A term `cut : cuts n` for some positive integer `n` represents a cut that divides the pizza into `n + 1`-pieces. indexed from `0`. For each piece `i`, `cut i` is the area of that piece. -/
def cuts :=
  {f : Fin (n + 1) → ℝ // (∀ i : Fin (n + 1), f i ≥ 0) ∧ ∑ i : Fin (n + 1), f i = 1}

/- A term `turn : turns n` for some positive integer `n` describes the process of the game. For round `i`, `turn i` is the NO. of the chosen pizza in this round. -/
def turns :=
  {f : Fin (n + 1) → Fin (n + 1) // Function.Injective f}

/- A term `strategy : strategies n` represents the strategy we choose. More specifically, for some cut of pizza `cut : cuts n` and some game process `turn : turns n`, `strategy cut turn` is the constraints we require for `turn`, such that we make it the best strategy. -/
/- **Note!! This definition might be wrong.** -/
def strategies :=
  cuts n → turns n → Fin (n + 1) → Prop

end

section

variable {n : ℕ}

/- ... -/
def taken_pieces (t : turns n) (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.image t.val (Finset.Iic i)

theorem card_taken_pieces {t : turns n} {i : Fin (n + 1)} : (taken_pieces t i).card = i.val + 1 := by
  simp only [taken_pieces]
  rw [Finset.card_image_of_injective _ t.property, Fin.card_Iic]

/- Given a game process `turn` and some round `i`, `current_state turn i` represents the left pieces before round `i` begins. -/
def current_state (t : turns n) (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  if i = 0 then
    Finset.univ
  else
    Finset.univ \ taken_pieces t (i - 1)

theorem current_state_of_ne_zero {t : turns n} {i : Fin (n + 1)} (ne : i ≠ 0) : current_state t i = Finset.univ \ taken_pieces t (i - 1) := by
  simp only [current_state, if_neg ne]

/- For a situation `s`, `boundary s` are those pieces on the boundary. -/
def boundary (s : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  {a : Fin (n + 1) | a ∈ s ∧ ((a + 1) ∉ s ∨ (a - 1) ∉ s)}.toFinset

theorem cIcc_boundary {a b : Fin (n + 1)} (h : Fin.cIcc a b ≠ Finset.univ) : boundary (Fin.cIcc a b) = {a, b} := by
  if h₁ : a = b then
    simp only [boundary]
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
    simp only [boundary]
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

/- `basic_rule : turns n → Prop` represents the rule of the game, and here, it means that each time, the chosen piece should be on the boundary. -/
def basic_rule : turns n → Prop :=
  fun turn => ∀ i, i.val > 0 → turn.val i ∈ boundary (current_state turn i)

theorem legal_turn {turn : turns n} : basic_rule turn ↔ ∀ i, i.val > 0 → turn.val i ∈ boundary (current_state turn i) := by
  simp only [basic_rule]

end

/- A term `game : games` is one concrete game, containing the following fields:
 - `cut : cuts n` represents the cut of the pizza in this `game`;
 - `strategy : strategies n` represents the strategy we use to get the best result;
 - `turn : {t : turns n // basic_rule t ∧ strategy cut t}` represents the game process of `game` under the strategy above we choose. -/
structure games (n : ℕ) where
  cut : cuts n
  turn : turns n
  strategy : strategies n
  legality : basic_rule turn
  good_turn : ∀ i, strategy cut turn i

section

variable {n : ℕ}

/- `result : ℝ` represents the result of `game`, and here, it is the total area of the pieces chosen by us. -/
def games.result (game : games n) : ℝ :=
  ∑ i with Even i.val, game.cut.val (game.turn.val i)

def games_with_strategy (strategy : strategies n) :=
  {g : games n // g.strategy = strategy}

def alice's_pieces (game : games n) : Finset (Fin (n + 1)) :=
  {x | ∃ i : Fin (n + 1), Even i.val ∧ game.turn.val i = x}.toFinset

def bob's_pieces (game : games n) : Finset (Fin (n + 1)) :=
  {x | ∃ i : Fin (n + 1), Odd i.val ∧ game.turn.val i = x}.toFinset

theorem alice's_pieces_def {game : games n} : alice's_pieces game = {x | ∃ i : Fin (n + 1), Even i.val ∧ game.turn.val i = x}.toFinset := rfl

theorem bob's_pieces_def {game : games n} : bob's_pieces game = {x | ∃ i : Fin (n + 1), Odd i.val ∧ game.turn.val i = x}.toFinset := rfl

theorem alice's_pieces_eq_univ_sdiff_bob's_pieces {game : games n} : alice's_pieces game = Finset.univ \ bob's_pieces game := by
  rw [alice's_pieces_def, bob's_pieces_def]
  ext x
  rw [Finset.mem_sdiff]
  repeat rw [Set.mem_toFinset, Set.mem_setOf]
  constructor <;> intro mem
  · rcases mem with ⟨i, even, h⟩
    exact ⟨Finset.mem_univ _, by
      intro mem'
      rcases mem' with ⟨j, odd, h'⟩
      rw [← h'] at h
      apply game.turn.property at h
      rw [h] at even
      exact Nat.not_even_iff_odd.mpr odd <| even⟩
  · replace mem := mem.right
    push_neg at mem
    by_contra mem'
    push_neg at mem'
    have h : ∀ i : Fin (n + 1), game.turn.val i ≠ x := by
      intro i
      by_cases h₁ : Even i.val
      · exact mem' i h₁
      · exact mem i <| Nat.not_even_iff_odd.mp h₁
    have h' : Function.Surjective game.turn.val := by
      exact Finite.surjective_of_injective game.turn.property
    rcases h' x with ⟨i, eq⟩
    exact h i eq

end

section

variable {n : ℕ}

theorem fin_Iic_zero : Finset.Iic (0 : Fin (n + 1)) = {0} := by
  ext x
  constructor <;> intro mem
  · rw [Finset.mem_Iic] at mem
    by_contra h
    rw [Finset.mem_singleton, show ¬ x = 0 ↔ x ≠ 0 from Eq.to_iff rfl, ← Fin.pos_iff_ne_zero] at h
    exact not_lt.mpr mem h
  · rw [Finset.mem_singleton] at mem
    rw [mem, Finset.mem_Iic]

theorem fin_Iic_last : Finset.Iic (n : Fin (n + 1)) = Finset.univ := by
  rw [Fin.natCast_eq_last]
  ext x
  constructor <;> intro _
  · exact Finset.mem_univ _
  · rw [Finset.mem_Iic]
    exact Fin.le_last _

theorem fin_Icc_zero_last : Finset.Icc 0 (n : Fin (n + 1)) = Finset.univ := by
  ext x
  constructor <;> intro _
  · exact Finset.mem_univ _
  · rw [Finset.mem_Icc, Fin.natCast_eq_last]
    constructor
    · exact Fin.zero_le _
    · exact Fin.le_last _

theorem first_piece (turn : turns n) : taken_pieces turn 0 = {turn.val 0} := by
  simp only [taken_pieces]
  rw [fin_Iic_zero, Finset.image_singleton]

theorem take_all (turn : turns n) : taken_pieces turn n = Finset.univ := by
  simp only [taken_pieces]
  rw [fin_Iic_last]
  refine Finset.image_univ_of_surjective ?_
  exact Finite.surjective_of_injective turn.property

theorem taken_pieces_eq_insert {t : turns n} {i : Fin n} : (taken_pieces t i.succ) = insert (t.val i.succ) (taken_pieces t i.castSucc) := by
  simp only [taken_pieces]
  rw [Finset.insert_eq]
  ext x
  constructor <;> intro mem
  · if h₃ : x = t.val i.succ then
      rw [Finset.mem_union, Finset.mem_singleton]
      exact Or.inl h₃
    else
      rw [Finset.mem_image] at mem
      rcases mem with ⟨j, mem, eq⟩
      have h₁ : j ≠ i.succ := by
        intro h₁
        rw [h₁] at eq
        exact h₃ eq.symm
      rw [Finset.mem_union]
      refine Or.inr ?_
      rw [Finset.mem_image]
      exists j
      constructor
      · rw [Finset.mem_Iic] at *
        replace mem := lt_of_le_of_ne mem h₁
        exact Fin.le_castSucc_iff.mpr mem
      · exact eq
  · rw [Finset.mem_union, Finset.mem_singleton] at mem
    rw [Finset.mem_image]
    refine Or.elim mem ?_ ?_ <;> intro h₃
    · exists i.succ
      constructor
      · rw [Finset.mem_Iic]
      · exact h₃.symm
    · rw [Finset.mem_image] at h₃
      rcases h₃ with ⟨j, h₃, eq⟩
      exists j
      constructor
      · rw [Finset.mem_Iic] at *
        exact le_of_lt <| Fin.le_castSucc_iff.mp h₃
      · exact eq

theorem taken_pieces_eq_cIcc (game : games n) : ∀ i, ∃ a b, taken_pieces game.turn i = Fin.cIcc a b := by
  intro i
  induction i using Fin.induction with
  | zero =>
    exists (game.turn.val 0), (game.turn.val 0)
    rw [first_piece]
    ext x
    rw [Fin.mem_cIcc_self]
    exact Finset.mem_singleton
  | succ i hi =>
    if h : i.succ = n then
      exists 0, Fin.last n
      rw [h, take_all, Fin.cIcc_eq_univ.mpr (Fin.last_add_one _).symm]
    else
      rcases hi with ⟨a, b, eq_cIcc⟩
      have i_take := game.legality
      rw [legal_turn] at i_take
      replace i_take := i_take i.succ (Nat.zero_lt_succ _)
      have h₁ : taken_pieces game.turn i.castSucc ≠ Finset.univ := by
        intro h₁
        rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin, card_taken_pieces, Nat.add_right_cancel_iff] at h₁
        rw [show i.castSucc.val = i.val from rfl] at h₁
        linarith [i.isLt]
      rw [current_state_of_ne_zero (Fin.succ_ne_zero _), ← Fin.coeSucc_eq_succ, add_sub_cancel_right, eq_cIcc, Fin.cIcc_compl (eq_cIcc ▸ h₁)] at i_take
      if h₂ : Fin.cIcc (b + 1) (a - 1) = Finset.univ then
        rw [Fin.cIcc_eq_univ, sub_add_cancel] at h₂
        symm at h₂
        rw [← Fin.cIcc_eq_univ, ← eq_cIcc] at h₂
        exact False.elim <| h₁ h₂
      else
        rw [cIcc_boundary (by tauto), Fin.coeSucc_eq_succ, Finset.mem_insert, Finset.mem_singleton] at i_take
        rw [taken_pieces_eq_insert, eq_cIcc, Finset.insert_eq]
        have h₃ : a ≠ b + 1 := by
          intro h₃
          rw [← Fin.cIcc_eq_univ, ← eq_cIcc] at h₃
          exact h₁ h₃
        refine Or.elim i_take ?_ ?_ <;> intro h₄ <;> rw [h₄]
        · exists a, b + 1
          ext x
          rw [Finset.mem_union, Finset.mem_singleton]
          constructor <;> intro mem
          · refine Or.elim mem ?_ ?_ <;> intro mem'
            · rw [mem']
              exact Fin.right_mem_cIcc
            · exact Fin.cIcc_subset_left (by
                nth_rw 2 [show b = b + 1 - 1 from (add_sub_cancel_right _ _).symm]
                exact Fin.sub_one_mem_cIcc a h₃.symm) <| mem'
          · if h₅ : x = b + 1 then
              exact Or.inl h₅
            else
              rw [← Finset.mem_singleton] at h₅
              replace h₅ := Finset.mem_sdiff.mpr ⟨mem, h₅⟩
              rw [Fin.cIcc_sdiff_endpoint_right h₃, add_sub_cancel_right] at h₅
              exact Or.inr h₅
        · replace h₃ := show a - 1 ≠ b by
            intro eq
            rw [sub_eq_iff_eq_add] at eq
            exact h₃ eq
          exists a - 1, b
          ext x
          rw [Finset.mem_union, Finset.mem_singleton]
          constructor <;> intro mem
          · refine Or.elim mem ?_ ?_ <;> intro mem'
            · rw [mem']
              exact Fin.left_mem_cIcc
            · exact Fin.cIcc_subset_right (by
                nth_rw 2 [show a = a - 1 + 1 from (sub_add_cancel a 1).symm]
                exact Fin.add_one_mem_cIcc b h₃) <| mem'
          · if h₅ : x = a - 1 then
              exact Or.inl h₅
            else
              rw [← Finset.mem_singleton] at h₅
              replace h₅ := Finset.mem_sdiff.mpr ⟨mem, h₅⟩
              rw [Fin.cIcc_sdiff_endpoint_left h₃, sub_add_cancel] at h₅
              exact Or.inr h₅

theorem current_state_eq_cIcc (game : games n) : ∀ i, i ≠ 0 → ∃ a b, current_state game.turn i = Fin.cIcc a b := by
  intro i ne_zero
  rw [current_state_of_ne_zero ne_zero]
  rcases taken_pieces_eq_cIcc game (i - 1) with ⟨a, b, eq⟩
  rw [eq, Fin.cIcc_compl (by
    intro h
    rw [h, ← Finset.card_eq_iff_eq_univ, card_taken_pieces, Fintype.card_fin, add_right_cancel_iff] at eq
    conv at eq =>
      enter [2]
      rw [← Fin.val_last n]
    rw [Fin.val_inj, sub_eq_iff_eq_add, Fin.last_add_one] at eq
    exact ne_zero eq)]
  exists b + 1, a - 1

end

section

variable {n : ℕ}

noncomputable def red_pieces (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  {x | x ∈ Fin.cIcc a b ∧ Even (x - a).val}.toFinset

noncomputable def green_pieces (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  {x | x ∈ Fin.cIcc a b ∧ Odd (x - a).val}.toFinset

noncomputable def red_pieces₀ (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  {x | x ∈ Fin.cIcc a b ∧ Even (b - x).val}.toFinset

noncomputable def green_pieces₀ (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
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

section

variable {n : ℕ} [NeZero n]

def even_case_strategy (_ : Even (n + 1)) : strategies n :=
  fun cut turn i =>
    if Even i.val then
      if ∑ i with Even i.val, cut.val i ≥ ∑ i with Odd i.val, cut.val i then
        Even (turn.val i).val
      else
        Odd (turn.val i).val
    else
      True

theorem even_case₀ (h : Even (n + 1)) : Nonempty (games_with_strategy (even_case_strategy h)) ∧ ∀ game : games_with_strategy (even_case_strategy h), game.val.result ≥ (1 : ℝ) / 2 := by
  constructor
  · refine Nonempty.intro ?_
    let sample_game : games n := {
      cut := ⟨fun i => (1 : ℝ) / (n + 1), by
        constructor
        · intro i
          positivity
        · show ∑ _, (1 : ℝ) / (n + 1) = 1
          rw [Finset.sum_const, Finset.card_fin]
          field_simp⟩
      turn := ⟨fun i => i, fun _ _ eq => eq⟩
      strategy := even_case_strategy h
      legality := by
        rw [legal_turn]
        intro i pos
        show i ∈ _

        admit
      good_turn := sorry
    }
    admit
  · admit

end
