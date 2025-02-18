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
    else True
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

          sorry
        · next h₁ =>
          sorry
      · sorry
    · sorry
  sbtw_trans_left := sorry
  btw_antisymm := sorry
  btw_total := sorry
