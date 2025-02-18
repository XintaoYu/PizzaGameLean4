import Mathlib

--NOTE : it seems that we can replace n with n + 1 and NeZero n ; it is equivalent to n > 1 and there will be much lesser cases to deal with
variable {n : ℕ} [NeZero n]

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
        sorry
    · next h =>
      sorry
  btw_antisymm := sorry
  btw_total := sorry
