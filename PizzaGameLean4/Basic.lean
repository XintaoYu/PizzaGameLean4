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

theorem Fin.le_add_one {a : Fin (n + 1)} (h : a < Fin.last n) : a

theorem Fin.add_one_mem_cIcc {a : Fin (n + 1)} : ∀ b, a ≠ b → a + 1 ∈ Fin.cIcc a b := by
  intro b h
  simp [cIcc, h]
  simp only [btw]
  split
  · next h' =>
    constructor
    · have : a < Fin.last n := lt_of_lt_of_le h' (Fin.le_last b)

      sorry
    · sorry
  · next h' =>
    sorry

theorem Fin.sub_one_mem_cIcc {a : Fin (n + 1)} : ∀ b, a ≠ b → a - 1 ∈ Fin.cIcc b a := by
  sorry
