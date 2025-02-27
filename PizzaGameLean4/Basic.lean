import Mathlib

--NOTE : it seems that we can replace n with n + 1 and NeZero n ; it is equivalent to n > 1 and there will be much lesser cases to deal with
variable {n : ℕ}

instance Fin.instCircularOrder : CircularOrder (Fin (n + 1)) where
  btw := fun a b c =>
    if a < c then a ≤ b ∧ b ≤ c
    else if c < a then a ≤ b ∨ b ≤ c
    else True
  sbtw := fun a b c =>
    if a < c then a < b ∧ b < c
    else if c < a then a < b ∨ b < c
    else False
  btw_refl := fun _ => by simp
  btw_cyclic_left := @fun a b c habc => by
    simp [btw] at *
    split at habc
    · next h =>
      simp [not_lt.mpr habc.1]
      intro h'
      left
      exact habc.2
    · next h =>
      split
      · next h' =>
        have := le_of_not_lt h
        constructor
        · rcases lt_or_eq_of_le this with h | h
          · rcases (habc h) with hd | hd
            · absurd h'
              exact not_lt_of_le hd
            · exact hd
          · rw [← h] at h'
            exact le_of_lt h'
        · exact this
      · next h' =>
        intro hd
        right
        exact le_of_not_lt h
  sbtw_iff_btw_not_btw := @fun a b c => by
    constructor
    · intro h
      constructor
      · simp [btw, sbtw] at *
        split at h
        · next h₁ =>
          simp [h₁]
          exact ⟨le_of_lt h.1, le_of_lt h.2⟩
        · next h₁ =>
          simp [h₁]
          intro this
          rcases h.2 with h | h
          · left
            exact le_of_lt h
          · right
            exact le_of_lt h
      · simp only [btw, sbtw] at *
        split at h
        · next h₁ =>
          have : ¬ (c ≤ b ∨ b ≤ a) := by
            simp
            exact ⟨h.2, h.1⟩
          simp [h₁, this]
          intro h' h₁'
          exact h.1
        · next h₁ =>
          have := le_of_not_lt h₁
          rcases lt_or_eq_of_le this with hd | hd
          · simp [hd] at *
            intro h'
            rcases h with h | h
            · exact h
            · absurd h
              exact not_lt_of_le h'
          · simp [hd] at *
    · intro h
      simp only [btw, sbtw] at *
      rcases h with ⟨h₁, h₂⟩
      split at h₁
      · next hd =>
        have hd' : ¬ c < a := not_lt_of_lt hd
        simp [hd, hd'] at *
        exact ⟨h₂.2, h₂.1⟩
      · next hd =>
        have := le_of_not_lt hd
        rcases lt_or_eq_of_le this with hd | hd
        · have hd' := not_lt_of_lt hd
          simp [hd, hd'] at *
          rcases h₁ with h₁' | h₁'
          · rcases lt_or_eq_of_le h₁' with h₁' | h₁'
            · left
              exact h₁'
            · rw [h₁'] at this
              left
              exact h₂ this
          · rcases lt_or_eq_of_le h₁' with h₁' | h₁'
            · right
              exact h₁'
            · left
              exact h₂ (le_of_eq h₁'.symm)
        · simp [hd] at *
  sbtw_trans_left := @fun a b c d fabc fbdc => by
    simp only [sbtw] at *
    split at fabc
    · next h =>
      simp [h]
      split at fbdc
      · next h' =>
        exact ⟨lt_trans fabc.1 fbdc.1, fbdc.2⟩
      · next h' =>
        absurd fabc.2
        exact h'
    · next h =>
      have := le_of_not_lt h
      rcases lt_or_eq_of_le this with hd | hd
      · simp only [h, hd] at *
        split at fbdc
        · next h' =>
          simp at *
          rcases fabc with hd' | hd'
          · left
            exact lt_trans hd' fbdc.1
          · right
            exact fbdc.2
        · next h' =>
          have := le_of_not_lt h'
          rcases lt_or_eq_of_le this with hd' | hd'
          · simp [hd'] at *
            rcases fabc with hq | hq
            · rcases fbdc with hq' | hq'
              · left
                exact lt_trans hq hq'
              · right
                exact hq'
            · absurd hq
              exact not_lt_of_le h'
          · simp [hd'] at *
      · simp [hd] at *
  btw_antisymm := @fun a b c fabc fcba => by
    simp only [btw] at *
    split at fabc
    · next h =>
      split at fcba
      · next h' =>
        left
        exact eq_of_le_of_le fabc.1 fcba.2
      · next h' =>
        rcases fcba with hd | hd
        · right
          left
          exact eq_of_le_of_le fabc.2 hd
        · left
          apply eq_of_le_of_le fabc.1 hd
    · next h =>
      split at fcba
      · next h' =>
        simp [h'] at fabc
        rcases fabc with hd | hd
        · left
          exact eq_of_le_of_le hd fcba.2
        · right
          left
          exact eq_of_le_of_le hd fcba.1
      · next h' =>
        right
        right
        exact eq_of_le_of_le (le_of_not_lt h) (le_of_not_lt h')
  btw_total := fun a b c => by
    simp only [btw]
    if h : a < c then
      simp [h]
      have : ¬ c < a := lt_asymm h
      simp [this]
      if h' : a ≤ b then
        if h'' : b ≤ c then
          left
          exact ⟨h', h''⟩
        else
          right
          left
          exact le_of_not_le h''
      else
        right
        right
        exact le_of_not_le h'
    else if h₁ : c < a then
      simp [h₁]
      have : ¬ a < c := lt_asymm h₁
      simp [this]
      if h' : a ≤ b then
        left
        left
        exact h'
      else
        if h'' : b ≤ c then
          left
          right
          exact h''
        else
          right
          exact ⟨le_of_not_le h'', le_of_not_le h'⟩
    else
      simp [h, h₁]


instance __aux_btw_decidable (a b : Fin (n + 1)) : DecidablePred (fun x => btw a x b) := fun x => by
  simp [btw]
  exact inferInstance


theorem Fin.left_btw (a b : Fin (n + 1)) : btw a a b := by
  simp only [btw]
  split
  · next h =>
    simp
    exact le_of_lt h
  · next h =>
    have h' : b ≤ a := le_of_not_lt h
    have := lt_or_eq_of_le h'
    rcases this with hd | hd
    · simp [hd]
    · simp [hd]

theorem Fin.right_btw (a b : Fin (n + 1)) : btw a b b := by
  simp only [btw]
  split
  · next h =>
    simp
    exact le_of_lt h
  · next h =>
    have h' : b ≤ a := le_of_not_lt h
    have := lt_or_eq_of_le h'
    rcases this with hd | hd
    · simp [hd]
    · simp [hd]


def Fin.cIcc (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  if a = b then
    {a}
  else
    {x | btw a x b}.toFinset


theorem Fin.left_mem_cIcc {a b : Fin (n + 1)} : a ∈ Fin.cIcc a b := by
  simp only [cIcc]
  if h : a = b then
    simp [h]
  else
    simp [h]
    exact left_btw a b

theorem Fin.right_mem_cIcc {a b : Fin (n + 1)} : b ∈ Fin.cIcc a b := by
  simp only [cIcc]
  if h : a = b then
    simp [h]
  else
    simp [h]
    exact right_btw a b

theorem Fin.mem_cIcc_of_ne {a b : Fin (n + 1)} (h : a ≠ b) (x : Fin (n + 1)) : x ∈ Fin.cIcc a b ↔ btw a x b := by
  simp only [cIcc, h]
  simp

theorem Fin.mem_cIcc_self {a : Fin (n + 1)} (x : Fin (n + 1)) : x ∈ Fin.cIcc a a ↔ x = a := by
  simp only [cIcc]
  simp

theorem Fin.cIcc_self {a : Fin (n + 1)} : Fin.cIcc a a = {a} := by
  simp [cIcc]

theorem Fin.mem_cIcc_or {a b : Fin (n + 1)} (h : a ≠ b) (x : Fin (n + 1)) : x ∈ Fin.cIcc a b ∨ x ∈ Fin.cIcc b a := by
  have : b ≠ a := fun a₁ ↦ h (id (Eq.symm a₁))
  simp [cIcc, h, this]
  exact btw_total a x b

theorem Fin.mem_cIcc_antisymm {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ Fin.cIcc a b ∧ x ∈ Fin.cIcc b a ↔ x = a ∨ x = b := by
  if h : a = b then
    simp [h]
    simp [cIcc_self]
  else
    simp only [cIcc]
    simp [h]
    have : b ≠ a := fun a₁ ↦ h (id (Eq.symm a₁))
    simp [this]
    constructor
    · intro h'
      have h' := btw_antisymm h'.1 h'.2
      simp [this] at h'
      rcases h' with hd | hd
      · left
        exact hd.symm
      · right
        exact hd
    · intro h'
      rcases h' with hd | hd
      · rw [hd]
        exact ⟨left_btw a b, right_btw b a⟩
      · rw [hd]
        exact ⟨right_btw a b, left_btw b a⟩

theorem Fin.add_one_mem_cIcc {a : Fin (n + 1)} : ∀ b, a ≠ b → a + 1 ∈ Fin.cIcc a b := by
  intro b h
  simp [cIcc, h]
  simp only [btw]
  split
  · next h' =>
    constructor
    · have : a < Fin.last n := lt_of_lt_of_le h' (Fin.le_last b)
      apply Fin.le_def.mpr
      rw [Fin.val_add_one_of_lt this]
      simp
    · apply Fin.add_one_le_of_lt h'
  · next h' =>
    have := le_of_not_lt h'
    have h₁ := lt_or_eq_of_le this
    rcases h₁ with h₁ | h₁
    · simp [h₁]
      if hd : a < Fin.last n then
        left
        apply Fin.le_def.mpr
        rw [Fin.val_add_one_of_lt hd]
        simp
      else
        have hd := le_of_not_lt hd
        have hd' := le_last a
        have hd := eq_of_le_of_le hd' hd
        right
        simp [hd]
    · simp [h₁]

theorem Fin.sub_one_mem_cIcc {a : Fin (n + 1)} : ∀ b, a ≠ b → a - 1 ∈ Fin.cIcc b a := by
  intro b h
  simp [cIcc, h.symm]
  simp only [btw]
  split
  · next h' =>
    have := zero_le b
    have := lt_of_le_of_lt this h'
    have hd : ¬ a = 0 := pos_iff_ne_zero.mp this
    have h' := Fin.lt_def.mp h'
    constructor
    · apply Fin.le_def.mpr
      simp [Fin.coe_sub_one]
      simp [hd]
      exact (Nat.le_sub_one_iff_lt this).mpr h'
    · apply Fin.le_def.mpr
      simp [Fin.coe_sub_one]
      simp [hd]
  · next h' =>
    have := le_of_not_lt h'
    have h₁ := lt_or_eq_of_le this
    rcases h₁ with h₁ | h₁
    · simp [h₁]
      if hd : 1 ≤ a then
        right
        exact hd
      else
        if g : 0 < n then
          left
          have hd := lt_of_not_le hd
          have hd := Fin.lt_def.mp hd
          have hd := Nat.le_sub_one_of_lt hd
          have : (1 : Fin (n + 1)).val = (1 : ℕ) := by
            simp
            exact g
          rw [this] at hd
          simp at hd
          have : (0 : Fin (n + 1)).val = (0 : ℕ) := rfl
          rw [← this] at hd
          have hd := Fin.val_inj.mp hd
          apply Fin.le_def.mpr
          rw [Fin.coe_sub_one]
          simp [hd]
          have : (Fin.last n).val = n := rfl
          simp_rw [← this]
          apply Fin.le_def.mp
          exact le_last b
        else
          simp at g
          subst g
          left
          simp
    · simp [h₁]

theorem Fin.val_sub_add_eq_iff_mem_cIcc {a b : Fin (n + 1)} (x : Fin (n + 1)) : (x - a).val + (b - x).val = (b - a).val ↔ x ∈ Fin.cIcc a b := by
  if h : a = b then
    simp [h]
    simp [mem_cIcc_self]
    have : (0 : ℕ) = (0 : Fin (n + 1)) := rfl
    rw [this] at *
    simp only [Fin.val_inj]
    rw [sub_eq_zero]
    rw [sub_eq_zero]
    simp
    intro h'
    exact h'.symm
  else
    rw [Fin.mem_cIcc_of_ne h x]
    simp only [btw]
    split
    · next h' =>
      constructor
      · intro h₁
        by_contra h₂
        simp at h₂
        have h₃ := lt_or_ge x a
        rcases h₃ with h₃ | h₃
        · have : (x - a).val = n + 1 - a.val + x.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + x.val < n + 1 := by
              have h₃ := Fin.val_fin_lt.mpr h₃
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [Fin.sub_val_of_le (le_of_lt (lt_trans h₃ h'))] at h₁
          rw [this] at h₁
          rw [Fin.sub_val_of_le (le_of_lt h')] at h₁
          rw [add_assoc, Nat.add_sub_cancel' (le_of_lt (Fin.val_fin_lt.mpr (lt_trans h₃ h')))] at h₁
          omega
        · have h₂ := h₂ h₃
          have : a ≤ x := h₃
          have := Fin.sub_val_of_le this
          rw [this] at h₁
          have : (b - x).val = n + 1 - x.val + b.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - x.val + b.val < n + 1 := by
              have h₃ := Fin.val_fin_lt.mpr h₂
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this] at h₁
          rw [Fin.sub_val_of_le (le_of_lt h')] at h₁
          omega
      · intro h₁
        rw [Fin.sub_val_of_le h₁.1]
        rw [Fin.sub_val_of_le h₁.2]
        rw [Fin.sub_val_of_le (le_of_lt h')]
        omega
    · next h' =>
      have h' := le_of_not_lt h'
      have h : ¬ b = a := fun a₁ ↦ h (id (Eq.symm a₁))
      have h' := lt_of_le_of_ne h' h
      simp [h']
      constructor
      · intro h₁
        by_contra h₂
        simp at h₂
        have : (x - a).val = n + 1 - a.val + x.val := by
          rw [sub_def]
          dsimp
          have : n + 1 - a.val + x.val < n + 1 := by
            have h₃ := Fin.val_fin_lt.mpr h₂.1
            omega
          rw [Nat.mod_eq_of_lt this]
        rw [this] at h₁
        have : (b - x).val = n + 1 - x.val + b.val := by
          rw [sub_def]
          dsimp
          have : n + 1 - x.val + b.val < n + 1 := by
            have h₃ := Fin.val_fin_lt.mpr h₂.2
            omega
          rw [Nat.mod_eq_of_lt this]
        rw [this] at h₁
        have : (b - a).val = n + 1 - a.val + b.val := by
          rw [sub_def]
          dsimp
          have : n + 1 - a.val + b.val < n + 1 := by
            have h₃ := Fin.val_fin_lt.mpr h'
            omega
          rw [Nat.mod_eq_of_lt this]
        rw [this] at h₁
        omega
      · intro h₁
        rcases h₁ with h₁ | h₁
        · rw [Fin.sub_val_of_le h₁]
          have : (b - a).val = n + 1 - a.val + b.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + b.val < n + 1 := by
              have h₃ := Fin.val_fin_lt.mpr h'
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          have : b < x := lt_of_lt_of_le h' h₁
          have : (b - x).val = n + 1 - x.val + b.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - x.val + b.val < n + 1 := by
              have h₃ := Fin.val_fin_lt.mpr this
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          omega
        · rw [Fin.sub_val_of_le h₁]
          have : (b - a).val = n + 1 - a.val + b.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + b.val < n + 1 := by
              have h₃ := Fin.val_fin_lt.mpr h'
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          have : x < a := lt_of_le_of_lt h₁ h'
          have : (x - a).val = n + 1 - a.val + x.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + x.val < n + 1 := by
              have h₃ := Fin.val_fin_lt.mpr this
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          omega

theorem Fin.val_sub_le_iff_btw {a x b : Fin (n + 1)} (ne : a ≠ b) : btw a x b ↔ (x - a).val ≤ (b - a).val := by
  simp only [btw]
  split
  · next h =>
    constructor
    · intro h₁
      rw [Fin.sub_val_of_le h₁.1]
      rw [Fin.sub_val_of_le (le_of_lt h)]
      omega
    · intro h₁
      rw [Fin.sub_val_of_le (le_of_lt h)] at h₁
      by_contra h₂
      simp at h₂
      rcases (lt_or_ge x a) with h₃ | h₃
      · have : (x - a).val = n + 1 - a.val + x.val := by
          rw [sub_def]
          dsimp
          have : n + 1 - a.val + x.val < n + 1 := by
            have h₃ := Fin.val_fin_lt.mpr h₃
            omega
          rw [Nat.mod_eq_of_lt this]
        rw [this] at h₁
        omega
      · rw [Fin.sub_val_of_le h₃] at h₁
        omega
  · next h =>
    have h := le_of_not_lt h
    have h := lt_or_eq_of_le h
    rcases h with h | h
    · simp [h]
      constructor
      · intro h₁
        rcases h₁ with h₁ | h₁
        · rw [Fin.le_def]
          rw [Fin.sub_val_of_le h₁]
          have : (b - a).val = n + 1 - a.val + b.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + b.val < n + 1 := by
              have h₁ := Fin.val_fin_lt.mpr h
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          omega
        · rw [Fin.le_def]
          have : x < a := lt_of_le_of_lt h₁ h
          have : (x - a).val = n + 1 - a.val + x.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + x.val < n + 1 := by
              have h₁ := Fin.val_fin_lt.mpr this
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          have : (b - a).val = n + 1 - a.val + b.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + b.val < n + 1 := by
              have h₁ := Fin.val_fin_lt.mpr h
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          omega
      · intro h₁
        by_contra h₂
        simp at h₂
        rw [Fin.le_def] at h₁
        have : (x - a).val = n + 1 - a.val + x.val := by
          rw [sub_def]
          dsimp
          have : n + 1 - a.val + x.val < n + 1 := by
            have h₁ := Fin.val_fin_lt.mpr h₂.1
            omega
          rw [Nat.mod_eq_of_lt this]
        rw [this] at h₁
        have : (b - a).val = n + 1 - a.val + b.val := by
          rw [sub_def]
          dsimp
          have : n + 1 - a.val + b.val < n + 1 := by
            have h₁ := Fin.val_fin_lt.mpr h
            omega
          rw [Nat.mod_eq_of_lt this]
        rw [this] at h₁
        omega
    · exact False.elim (ne (id (Eq.symm h)))

instance __aux_continuous_segment_decidable (a : Fin (n + 1)) (length : ℕ) : DecidablePred (fun x => ∃ m, 0 ≤ m ∧ m ≤ length ∧ x = a + m) := fun x => by
  if h : (x - a).val ≤ length then
    refine isTrue ?_
    use (x - a).val
    simp
    exact h
  else
    refine isFalse ?_
    simp
    intro m hm
    have h' := lt_of_not_ge h
    have := lt_of_le_of_lt hm h'
    intro h₁
    rw [h₁] at this
    simp at this
    have h₂ : m < n + 1 := by
      have := lt_of_le_of_lt hm h'
      have : (x - a).val < n + 1 := by
        exact (x - a).isLt
      omega
    have h₃ := Nat.mod_eq_of_lt h₂
    rw [h₃] at this
    omega

def Fin.continuous_segment (a : Fin (n + 1)) (length : ℕ) : Finset (Fin (n + 1)) :=
  {x | ∃ m, 0 ≤ m ∧ m ≤ length ∧ x = a + m}.toFinset

theorem Fin.cIcc_eq_continuous_segment {a b : Fin (n + 1)} : Fin.cIcc a b = Fin.continuous_segment a (b - a).val := by
  simp only [cIcc, Fin.continuous_segment]
  if h : a = b then
    simp [h]
  else
    simp [h]
    ext x
    simp only [btw]
    split
    · next h' =>
      simp
      constructor
      · intro h₁
        use (x - a).val
        rw [Fin.sub_val_of_le h₁.1]
        rw [Fin.sub_val_of_le (le_of_lt h')]
        simp
        have := Fin.le_def.mp (le_of_lt h')
        rw [Nat.sub_add_cancel this]
        simp [h₁.2]
        apply Fin.val_inj.mp
        rw [Fin.val_add]
        have : 0 ≤ x.val - a.val ∧ x.val - a.val ≤ n := by
          constructor
          · simp
          · simp
            trans n
            · exact Fin.is_le x
            · simp
        simp [this]
        rw [Nat.add_sub_cancel' (Fin.le_def.mp h₁.1)]
        have := Fin.isLt x
        rw [Nat.mod_eq_of_lt this]
      · intro h₁
        rcases h₁ with ⟨m, hm, h₁⟩
        rw [h₁]
        constructor
        · rw [Fin.le_def]
          rw [Fin.val_add]
          have : m < n + 1 := lt_of_le_of_lt hm (Fin.isLt (b - a))
          simp [this]
          have : a.val + m ≤ a.val + (b - a).val := add_le_add_left hm a.val
          rw [Fin.sub_val_of_le (le_of_lt h')] at this
          rw [Nat.add_sub_cancel' (Fin.le_def.mp (le_of_lt h'))] at this
          have := lt_of_le_of_lt this (Fin.isLt b)
          rw [Nat.mod_eq_of_lt this]
          simp
        · rw [Fin.le_def]
          rw [Fin.val_add]
          have : m < n + 1 := lt_of_le_of_lt hm (Fin.isLt (b - a))
          simp [this]
          have : a.val + m ≤ a.val + (b - a).val := add_le_add_left hm a.val
          rw [Fin.sub_val_of_le (le_of_lt h')] at this
          rw [Nat.add_sub_cancel' (Fin.le_def.mp (le_of_lt h'))] at this
          have this' := lt_of_le_of_lt this (Fin.isLt b)
          rw [Nat.mod_eq_of_lt this']
          exact this
    · next h' =>
      have h' := le_of_not_lt h'
      have h' : b < a := by exact lt_of_le_of_ne h' fun a_1 ↦ h (id (Eq.symm a_1))
      simp [h']
      constructor
      · intro h₁
        rcases h₁ with h₁ | h₁
        · use (x - a).val
          rw [Fin.sub_val_of_le h₁]
          have : (b - a).val = n + 1 - a.val + b.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + b.val < n + 1 := by
              have h₁ := Fin.val_fin_lt.mpr h'
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          simp
          rw [add_assoc, add_comm b.val a.val, ← add_assoc, Nat.sub_add_cancel (le_of_lt (Fin.isLt a))]
          have : n + 1 ≤ n + 1 + b.val := by omega
          simp [le_trans (le_of_lt (Fin.isLt x)) this]
          apply Fin.val_inj.mp
          rw [Fin.val_add]
          have : 0 ≤ x.val - a.val ∧ x.val - a.val ≤ n := by
            constructor
            · simp
            · simp
              trans n
              · exact Fin.is_le x
              · simp
          simp [this]
          rw [Nat.add_sub_cancel' (Fin.le_def.mp h₁)]
          have := Fin.isLt x
          rw [Nat.mod_eq_of_lt this]
        · use (x - a).val
          have : x < a := lt_of_le_of_lt h₁ h'
          have : (x - a).val = n + 1 - a.val + x.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + x.val < n + 1 := by
              have h₁ := Fin.val_fin_lt.mpr this
              omega
            rw [Nat.mod_eq_of_lt this]
          nth_rw 1 [this]
          have : (b - a).val = n + 1 - a.val + b.val := by
            rw [sub_def]
            dsimp
            have : n + 1 - a.val + b.val < n + 1 := by
              have h₁ := Fin.val_fin_lt.mpr h'
              omega
            rw [Nat.mod_eq_of_lt this]
          rw [this]
          simp
          exact h₁
      · intro h₁
        rcases h₁ with ⟨m, hm, h₁⟩
        rw [h₁]
        repeat rw [Fin.le_def]
        repeat rw [Fin.val_add]
        have : m < n + 1 := lt_of_le_of_lt hm (Fin.isLt (b - a))
        simp [this]
        if h₂ : a.val + m < n + 1 then
          left
          rw [Nat.mod_eq_of_lt h₂]
          omega
        else
          right
          rw [Nat.mod_eq_sub_mod (Nat.ge_of_not_lt h₂)]
          have : a.val + m - (n + 1) < n + 1 := by
            have g₁ := Fin.isLt a
            omega
          rw [Nat.mod_eq_of_lt this]
          trans a.val + (b - a).val - (n + 1)
          · omega
          · have : (b - a).val = n + 1 - a.val + b.val := by
              rw [sub_def]
              dsimp
              have : n + 1 - a.val + b.val < n + 1 := by
                have h₁ := Fin.val_fin_lt.mpr h'
                omega
              rw [Nat.mod_eq_of_lt this]
            rw [this]
            omega

theorem Fin.mem_continuous_segment {a : Fin (n + 1)} {length : ℕ} (x : Fin (n + 1)) : x ∈ a.continuous_segment length ↔ ∃ n, 0 ≤ n ∧ n ≤ length ∧ x = a + n := by
  simp [Fin.continuous_segment]

theorem Fin.cIcc_card_eq {a b : Fin (n + 1)} : (Fin.cIcc a b).card = (b - a).val + 1 := by
  rw [Fin.cIcc_eq_continuous_segment]
  simp [Fin.continuous_segment]
  let f : (i : ℕ) → i < (b - a).val + 1 → Fin (n + 1) :=
    fun i _ => a + i
  refine Finset.card_eq_of_bijective f ?_ ?_ ?_
  · intro x
    simp
    intro m hm h
    use m
    have : m < (b - a).val + 1 := Nat.lt_add_one_of_le hm
    use this
    simp [f]
    rw [h]
  · intro i hi
    simp [f]
    use i
    exact ⟨Nat.le_of_lt_add_one hi , rfl⟩
  · intro i j hi hj h
    simp [f] at h
    have : i = (i : Fin (n + 1)).val := by
      have hi := Nat.le_of_lt_add_one hi
      have hi := lt_of_le_of_lt hi (Fin.isLt (b - a))
      simp
      rw [Nat.mod_eq_of_lt hi]
    rw [this]
    have : j = (j : Fin (n + 1)).val := by
      have hj := Nat.le_of_lt_add_one hj
      have hj := lt_of_le_of_lt hj (Fin.isLt (b - a))
      simp
      rw [Nat.mod_eq_of_lt hj]
    rw [this]
    exact Fin.val_inj.mpr h

theorem Fin.cIcc_eq_univ {a b : Fin (n + 1)} : Fin.cIcc a b = Finset.univ ↔ a = b + 1 := by
  constructor
  · intro h
    simp only [Fin.cIcc] at h
    split at h
    · next h' =>
      have := Finset.eq_univ_iff_forall.mp h
      simp at this
      have := this (b + 1)
      rw [this]
    · next h' =>
      have := Finset.eq_univ_iff_forall.mp h
      simp only [btw] at this
      split at this
      · next h₁ =>
        simp at this
        have g₁ : a ≤ 0 := (this 0).1
        simp at g₁
        have g₂ : Fin.last n ≤ b := (this (Fin.last n)).2
        simp at g₂
        rw [g₁, g₂]
        simp
      · next h₁ =>
        have h₁ := le_of_not_lt h₁
        have h₁ := lt_of_le_of_ne h₁ (fun a₁ ↦ h' (id (Eq.symm a₁)))
        simp [h₁] at this
        if g₁ : b = Fin.last n then
          have h₂ := Fin.le_last a
          rw [← g₁] at h₂
          have h₁ := not_le_of_lt h₁
          contradiction
        else
          have g₂ : ¬ (b + 1) ≤ b := by
            simp [g₁]
          have := this (b + 1)
          simp [g₂] at this
          have this' := add_one_le_of_lt h₁
          exact eq_of_le_of_le this this'
  · intro h
    rw [Finset.eq_univ_of_card (Fin.cIcc a b)]
    rw [Fin.cIcc_card_eq]
    rw [h]
    simp

theorem Fin.cIcc_self_eq_univ_iff_fin_one {a : Fin (n + 1)} : Fin.cIcc a a = Finset.univ ↔ n = 0 := by
  constructor
  · intro h
    simp [cIcc] at h
    have := Finset.eq_univ_iff_forall.mp h
    simp at this
    have h₁ := this (Fin.last n)
    have h₂ := this 0
    rw [← h₁] at h₂
    apply Fin.last_eq_zero_iff.mp h₂.symm
  · intro h
    subst h
    simp [cIcc]
    exact fin_one_eq_zero a

theorem Fin.cIcc_eq_univ_of_fin_one {a b : Fin (n + 1)} (h : n = 0) : Fin.cIcc a b = Finset.univ := by
  subst h
  simp [cIcc]
  simp [fin_one_eq_zero]

theorem Fin.cIcc_subset_right {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ Fin.cIcc a b → Fin.cIcc x b ⊆ Fin.cIcc a b := by
  intro h
  simp only [cIcc] at *
  split at h
  · next h' =>
    simp at *
    subst h'
    simp [h]
  · next h' =>
    simp [btw] at h
    split at h
    · next h₁ =>
      simp only [btw]
      split
      · next h₂ =>
        simp
        exact h
      · next h₂ =>
        have h₂ := lt_of_le_of_ne h.2 h₂
        simp [h₂]
        intro t ht
        simp at *
        exact ⟨le_trans h.1 ht.1, ht.2⟩
    · next h₁ =>
      simp only [btw]
      have h₁ : b < a := lt_of_le_of_ne (le_of_not_lt h₁) fun a₁ ↦ h' (id (Eq.symm a₁))
      have h := h h₁
      split
      · next h₂ =>
        simp
        exact h
      · next h₂ =>
        if h₃ : x < b then
          simp [h₃]
          intro t ht
          simp at *
          right
          exact ht.2
        else
          have h₃' := lt_of_le_of_ne (le_of_not_lt h₃) fun a₁ ↦ h₂ (id (Eq.symm a₁))
          simp [h₃, h₃']
          intro t ht
          simp at *
          rcases ht with ht | ht
          · have h₃' := not_le_of_lt h₃'
            simp [h₃'] at h
            left
            exact le_trans h ht
          · right
            exact ht

theorem Fin.cIcc_subset_left {a b : Fin (n + 1)} {x : Fin (n + 1)} : x ∈ Fin.cIcc a b → Fin.cIcc a x ⊆ Fin.cIcc a b := by
  intro h
  simp only [cIcc] at *
  split at h
  · next h' =>
    simp at *
    subst h'
    simp [h]
  · next h' =>
    simp [btw] at h
    split at h
    · next h₁ =>
      simp [h']
      split
      · next h₂ =>
        simp
        exact left_btw a b
      · next h₂ =>
        intro t ht
        simp at *
        simp [btw] at *
        simp [h₁]
        have := lt_of_le_of_ne h.1 h₂
        simp [this] at ht
        exact ⟨ht.1, le_trans ht.2 h.2⟩
    · next h₁ =>
      have h₁' := lt_of_le_of_ne (le_of_not_lt h₁) fun a₁ ↦ h' (id (Eq.symm a₁))
      have h := h h₁'
      split
      · next h₂ =>
        subst h₂
        simp
        exact left_btw a b
      · next h₂ =>
        intro t ht
        simp [btw] at ht
        simp [btw]
        simp [h₁, h₁']
        rcases h with h | h
        · have h := lt_of_le_of_ne h h₂
          simp [h] at ht
          left
          exact ht.1
        · have := lt_of_le_of_lt h h₁'
          simp [this] at ht
          have := not_lt_of_lt this
          simp [this] at ht
          rcases ht with ht | ht
          · left
            exact ht
          · right
            exact le_trans ht h

theorem Fin.cIcc_sdiff_endpoint_left {a b : Fin (n + 1)} (h : a ≠ b) : Fin.cIcc a b \ {a} = Fin.cIcc (a + 1) b := by
  sorry
