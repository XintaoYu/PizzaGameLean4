import Mathlib

--NOTE : it seems that we can replace n with n + 1 and NeZero n ; it is equivalent to n > 1 and there will be much lesser cases to deal with
variable {n : ℕ} [NeZero n] -- n no of slices

/-- Successor deFined for `Fin n`. -/
def succ' (i : Fin n) := ite (i < n - 1) (i + 1 : Fin n) 0

/-- Predecessor deFined for `Fin n`. -/
def pred' (i : Fin n) := ite (0 < i) (i - 1 : Fin n) (n - 1)

/-- Neighborhood for a point `i`. -/
def nbr (i : Fin n) : Finset (Fin n) := {i, succ' i, pred' i}

/-- Neighbors of a point `i`. -/
def nbrs (i : Fin n) : Finset (Fin n) := {succ' i, pred' i}

/-- Interior of a set. -/
def int' (S : Finset (Fin n)) : Finset (Fin n) := Set.toFinset ({i | nbrs i ⊆ S})

/-- Boundary of a set. -/
def bdry (S : Finset (Fin n)) := S \ (int' (S))

lemma succ'_eq_add_one (x : Fin n) : succ' x = x + 1 := by
  rw [succ']
  split_ifs with h
  · rfl
  · cases' n
    · exact (Subsingleton.eq_zero (x + 1)).symm
    · next n _ =>
        have := Fin.le_last x
        simp only [CharP.cast_eq_zero, zero_sub, not_lt] at *
        rw [Fin.le_def] at *
        rw [Fin.coe_neg_one] at h
        rw [Fin.val_last] at this
        have h2 := le_antisymm this h
        conv_rhs at h2 => { rw [← Fin.val_last n] }
        rw [← Fin.ext_iff] at h2
        rw [h2]
        simp only [Fin.last_add_one]

lemma pred'_eq_add_one (x : Fin n) : pred' x = x - 1 := by
  rw [pred']
  split_ifs with h
  · rfl
  · cases' n
    · simp
      refine neg_eq_of_add_eq_zero_left ?_
      ring_nf
      exact Subsingleton.eq_zero x
    · refine sub_left_inj.mpr ?_
      simp only [CharP.cast_eq_zero]
      push_neg at h
      apply Eq.symm
      exact Fin.le_zero_iff.mp h

lemma pred'_lt_self {x : Fin n} (hx : 0 < x) : pred' x < x := by
  rw [pred']
  simp [hx]
  by_contra hg
  have h₁ : x ≤ x - 1 := by
    exact Fin.not_lt.mp hg
  cases n with
  | zero =>
    absurd Fin.pos x
    decide
  | succ d => -- n = d + 1
    absurd (Fin.pos_iff_ne_zero' x).mp hx
    exact Fin.le_sub_one_iff.mp h₁

lemma one_lt_of_ne_univ_and_nonempty (S : Finset (Fin n)) (hS : S ≠ Finset.univ ∧ S.Nonempty) : 1 < n := by
  --Proof of Contrary Evidence
  by_contra g
  --classification discussion
  have g₁ : n = 0 ∨ n = 1 := by
    refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
    exact Nat.not_lt.mp g
  cases g₁ with
  | inl h =>
    --When n=0, it is only necessary to prove S is empty
    have : n ≠ 0 := by
      apply Finset.nonempty_range_iff.mp
      simp [hS.2]
      exact NeZero.ne n
    exact this h
  | inr h =>
    --When n=1, it is necessary to first prove that S.card is equal to n
    have h₁ : 0 < S.card := by
      apply Finset.card_pos.mpr hS.2
    have h₃ : S.card ≤ n := by
      exact card_finset_fin_le S
    have h₄ : S.card ≤ 1 := by
      simp [h] at h₃
      exact h₃
    have h₅ : S.card = 1 := by
      exact Nat.le_antisymm h₄ h₁
    have h₆ : S.card = n := by
      simp [h, h₅]
    --Then we can use the theorem Finset.eq_univ_of_card to prove S is equal to Finset.univ
    have h₂ : S = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [h₆]
      exact (Fintype.card_fin n).symm
    have h₇ : S ≠ Finset.univ := by
      exact hS.1
    exact h₇ h₂

-- a lot of implicit typeclass inference problems are stuck here because p is not defined and where p is inferred Lean infers the argument to be Finset.decidableMem, but for a general prop it is Classical.decPred

lemma req8 {p : Finset (Fin n) → (Fin n → Prop)} (hp : ∀ x S, p S x ↔ x ∈ S) {S : Finset (Fin n)} (hS : S.Nonempty) : 0 ∈ @Fin.find _ (p S) (Classical.decPred _) ∨ 0 ∈ @Fin.find _ (p Sᶜ) (Classical.decPred _) := by
  haveI : DecidablePred (p Sᶜ) := (Classical.decPred _)
  by_cases h : 0 ∈ Fin.find (p S)
  · exact Or.inl h
  · refine' Or.inr _
    obtain ⟨y, hy⟩ := hS
    have h1 : y.val < n := Fin.prop y
    have h2 : (p S) y := by
      rw [hp y]
      apply hy
    have h3 := @Fin.nat_find_mem_find _ _ (Classical.decPred _) (⟨y.val, h1, h2⟩)
    rw [@Fin.mem_find_iff _ _ (Classical.decPred _) _, hp]
    simp only [Finset.mem_compl, Fin.zero_le', implies_true, forall_const, and_true]
    intro h0
    rw [← hp] at h0
    have h4 := ((@Fin.mem_find_iff _ _ (Classical.decPred _) _).1 h3).2 0 h0
    simp only [Fin.le_zero_iff'] at h4
    rw [h4] at h3
    apply h h3

--proofs somewhat follow from proof of req8
lemma req9 {p : Finset (Fin n) → (Fin n → Prop)} (hp : ∀ x S, p S x ↔ x ∈ S) {S : Finset (Fin n)} (h0 : 0 ∈ @Fin.find _ (p S) (Classical.decPred _)) {i : Fin n} (hi : i ∈ @Fin.find _ (p Sᶜ) (Classical.decPred _)) : 0 < i := by
  by_contra h
  simp only [not_lt, Fin.le_zero_iff'] at h
  rw [h] at hi
  rw [@Fin.mem_find_iff _ _ (Classical.decPred _) _, hp, Finset.mem_compl] at *
  apply hi.1 h0.1

lemma req10 {p : Finset (Fin n) → (Fin n → Prop)} (hp : ∀ x S, p S x ↔ x ∈ S) {S : Finset (Fin n)} (h0 : 0 ∈ @Fin.find _ (p Sᶜ) (Classical.decPred _)) {i : Fin n} (hi : i ∈ @Fin.find _ (p S) (Classical.decPred _)) : 0 < i := by
  by_contra h
  simp only [not_lt, Fin.le_zero_iff'] at h
  rw [h] at hi
  rw [@Fin.mem_find_iff _ _ (Classical.decPred _) _, hp, Finset.mem_compl] at *
  apply h0.1 hi.1

lemma bdry_compl_Nonempty (S : Finset (Fin n)) (hS : S ≠ Finset.univ ∧ S.Nonempty) : (bdry Sᶜ).Nonempty := by
  by_contra h
  rw [bdry, int'] at h
  simp only [nbrs, Finset.subset_iff, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Set.toFinset_setOf, Finset.not_nonempty_iff_eq_empty,
    Finset.sdiff_eq_empty_iff_subset, Finset.mem_filter, Finset.mem_univ, true_and] at h
  set p : Finset (Fin n) → (Fin n → Prop) := λ S x => x ∈ S --with hp
  have hp : ∀ x S, p S x ↔ x ∈ S := λ x S => by rfl
  cases' req8 hp hS.2 with h' h'
  · have h1 : Sᶜ.Nonempty := by
      refine (Finset.compl_ne_univ_iff_nonempty Sᶜ).mp ?_
      simp
      exact hS.1
    have h1' := h1
    obtain ⟨yc, hyc⟩ := h1'
    have h2 : yc.val < n := by
      exact Fin.prop yc
    have h3 : p Sᶜ yc := hyc
    have h4 := @Fin.nat_find_mem_find _ _ (Classical.decPred _) (⟨yc.val, h2, h3⟩)
    have h5 := (@Fin.mem_find_iff _ _ (Classical.decPred _) _).1 h4
    rw [hp] at h5
    simp only [Finset.mem_compl] at h5
    have h0 : 0 ∈ Fin.find (p S) := by convert h'
    rw [← compl_compl S] at h0
    have h6 := req9 hp h' h4
    have h7 := @Fin.find_min _ _ (Classical.decPred _) _ h4 _ (pred'_lt_self h6)
    change ¬_ ∈ Sᶜ at h7
    have h8 := @Fin.find_spec _ (p Sᶜ) (Classical.decPred _) _ h4
    change _ ∈ Sᶜ at h8
    specialize h h8
    apply h7
    apply h.2
  · obtain ⟨y, hy⟩ := hS.2
    have h2 : y.val < n := Fin.prop y
    have h3 : p S y := hy
    have h4 := @Fin.nat_find_mem_find _ _ (Classical.decPred _) (⟨y.val, h2, h3⟩)
    have h5 := (@Fin.mem_find_iff _ _ (Classical.decPred _) _).1 h4
    rw [hp] at h5
    have h6 := req10 hp h' h4
    have h7 := @Fin.find_min _ _ (Classical.decPred _) _ h4 _ (pred'_lt_self h6)
    change ¬_ ∈ S at h7
    have h8 := (h (Finset.mem_compl.2 h7)).1
    rw [succ'_eq_add_one, pred'_eq_add_one] at h8
    simp only [sub_add_cancel, Finset.mem_compl] at h8
    apply h8
    have h9 := @Fin.find_spec _ (p S) (Classical.decPred _) _ h4
    apply (hp _ _).1 h9

lemma sub_one_val_succ_lt {i : Fin n} (h1 : i.val.succ < n) (h2 : i ≠ 0) : (i - 1).val.succ < n := by
  apply lt_trans _ h1
  rw [Nat.succ_lt_succ_iff]
  simp only [Fin.val_fin_lt]
  cases' n
  · simp at *
  · simp
    apply Fin.pos_of_ne_zero h2


variable (n)
-- lemma nat_prop {i : ℕ} (h0 : i ≠ 0) (hi : i < n) : i.pred.succ < n := by
--   rw [Nat.succ_pred h0]
--   assumption

noncomputable local instance : Fintype ({i : ℕ | i ≠ 0 ∧ Even i ∧ i < n}) := by
  apply Set.Finite.fintype
  apply Set.finite_iff_bddAbove.mpr
  refine' ⟨n, _⟩
  rw [mem_upperBounds]
  simp
  intros x _ _ h3
  apply le_of_lt h3

lemma req11 (a b : ENNReal) (h : a + b = 1) : a ≥ 1/2 ∨ b ≥ 1/2 := by
  apply or_iff_not_imp_left.mpr
  intro h₁
  by_contra h₂
  have h₃ : a < 1/2 := by exact not_le.mp h₁
  have h₄ : b < 1/2 := by exact not_le.mp h₂
  have h₅ : a + b < 1/2 + 1/2 := by exact ENNReal.add_lt_add h₃ h₄
  have h₆ : (1/2 : ENNReal) + 1/2 = 1 := by exact ENNReal.add_halves 1
  rw [h₆] at h₅
  have h₇ : ¬ a + b = 1 := by exact ne_of_lt h₅
  exact h₇ h

/-- Defines the rules of the game, where a specific choice is made in every even turn (corresponding to the first player),
 and a random choice is made from the boundary for every odd turn (corresponding to the second player). -/
structure game' :=
(toFun : Fin (n + 1) → Fin (n + 1))
(rule_even : ∀ (i : Fin (n + 1)) (h1 : i.val.succ < n + 1) (h2 : Even i.val) (h3 : 0 < i.val), toFun i ∈ bdry (Finset.image toFun (Finset.Iic (i - 1)))ᶜ)
(nempty : ∀ (i : Fin (n + 1)) (h1 : i.val.succ < n + 1), (bdry (Finset.image toFun (Finset.Iic i))ᶜ).Nonempty)
(rule_odd : ∀ (i : Fin (n + 1)) (h1 : i.val.succ < n + 1) (h2 : Odd i.val) (h3 : 0 < i.val), toFun i = (nempty (i - 1) (sub_one_val_succ_lt h1 (by
  intro h
  rw [h] at h3
  simp at h3))).choose)

/-- Subset of peices eaten by first player. -/
noncomputable def first_player_share_at_level' (g : game' n) : Finset (Fin (n + 1)) :=
{g.toFun 0} ∪ Finset.biUnion (Set.toFinset ({i : ℕ | i ≠ 0 ∧ Even i ∧ i < n + 1})) (λ i => {g.toFun i})

open scoped BigOperators
-- trying with another form of f
lemma req2' (f : PMF (Fin n)) (S : Set (Fin n)) : (PMF.toMeasure f) S ≥ 1/2 ∨ (PMF.toMeasure f) Sᶜ ≥ 1/2 := by
  apply req11 _ _
  simp only [PMF.toMeasure_apply_fintype, ← Finset.sum_add_distrib,
    Set.indicator_self_add_compl_apply]
  rw [← tsum_fintype, PMF.tsum_coe]

--instance : MeasurableSpace (Fin n) := sorry

/-lemma req2 (f : MeasureTheory.FiniteMeasure (Fin n)) (S : Set (Fin n)) : f S ≥ 1/2 * f Set.univ ∨ f Sᶜ ≥ 1/2 * f Set.univ := by
  have g : f S + f Sᶜ = f Set.univ := by
    sorry
  apply or_iff_not_imp_left.mpr
  intro h₁
  by_contra h₂
  have g₁ : f S < 1/2 * f Set.univ := by exact not_le.mp h₁
  have g₂ : f Sᶜ < 1/2 * f Set.univ := by exact not_le.mp h₂
  have g₃ : f S + f Sᶜ < 1/2 * f Set.univ + 1/2 * f Set.univ := by exact add_lt_add g₁ g₂
  have g₄ : 1/2 * f Set.univ + 1/2 * f Set.univ = f Set.univ := by
    ext
    rw [NNReal.coe_add]
    rw [NNReal.coe_mul]
    simp
    ring
  rw [g₄] at g₃
  sorry-/

/-- This function tells us the pizza piece picked up at a given time.
    It takes as input `k`, the piece picked up at time 0. At time `i + 1`,
    the piece picked up is a random choice from the boundary of the complement
    of the set of pieces picked up before time `i + 1`. -/
noncomputable
def req_fun' (k : Fin (n + 1)) : Fin (n + 1) → Fin (n + 1)
  | ⟨0, _⟩ => k
  | ⟨i + 1, hi⟩ =>
    if Even i then (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
      (lt_of_le_of_lt Finset.card_biUnion_le (by simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin,
          smul_eq_mul, mul_one, Fintype.card_fin, hi])),
        Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton,
          Finset.singleton_nonempty])⟩).choose else
          (if succ' (req_fun' k i) ∈ Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' k j}) ∧ pred' (req_fun' k i) ∈ (Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' k j}))ᶜ then pred' (req_fun' k i)
            else (if pred' (req_fun' k i) ∈ Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' k j}) ∧ succ' (req_fun' k i) ∈ (Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' k j}))ᶜ then succ' (req_fun' k i) else
            (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
      (lt_of_le_of_lt Finset.card_biUnion_le (by simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin,
          smul_eq_mul, mul_one, Fintype.card_fin, hi])),
        Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton,
          Finset.singleton_nonempty])⟩).choose))
    decreasing_by
      all_goals simp_wf
      all_goals rw [Fin.lt_def]
      all_goals simp [Fin.val_nat_cast, Nat.mod_eq_of_lt (lt_trans (Fin.is_lt _) hi), Fin.is_lt _, Nat.mod_eq_of_lt (lt_trans Nat.le.refl hi), Nat.mod_eq_of_lt (lt_trans (Fin.is_lt _) (lt_trans Nat.le.refl hi)), lt_trans (Fin.is_lt _) Nat.le.refl]

lemma req_fun'_zero (k : Fin (n + 1)) : req_fun' n k 0 = k := rfl

lemma req_fun'_succ_even {k : Fin (n + 1)} {i : ℕ} (hi : i + 1 < n + 1) (heven : Even i) : req_fun' n k ⟨i + 1, hi⟩ = (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' n k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
      (lt_of_le_of_lt Finset.card_biUnion_le (by
        simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one, Fintype.card_fin, hi])),
        Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton, Finset.singleton_nonempty])⟩).choose := if_pos heven

lemma req_fun'_succ_odd (k : Fin (n + 1)) {i : ℕ} (hi : i + 1 < n + 1) (hodd : Odd i) : req_fun' n k ⟨i + 1, hi⟩ = if succ' (req_fun' n k i) ∈ Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' n k j}) ∧ pred' (req_fun' n k i) ∈ (Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' n k j}))ᶜ then pred' (req_fun' n k i)
            else (if pred' (req_fun' n k i) ∈ Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' n k j}) ∧ succ' (req_fun' n k i) ∈ (Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' n k j}))ᶜ then succ' (req_fun' n k i) else
            (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' n k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
      (lt_of_le_of_lt Finset.card_biUnion_le (by simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin,
          smul_eq_mul, mul_one, Fintype.card_fin, hi])),
        Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton,
          Finset.singleton_nonempty])⟩).choose) := if_neg (Nat.odd_iff_not_even.1 hodd)

lemma req_fun'_succ_odd' (k : ℕ) {i : ℕ} (hi : i + 1 < n + 1) (hodd : Odd i) : req_fun' n k (i + 1 : ℕ) = if succ' (req_fun' n k i) ∈ Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' n k j}) ∧ pred' (req_fun' n k i) ∈ (Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' n k j}))ᶜ then pred' (req_fun' n k i)
            else (if pred' (req_fun' n k i) ∈ Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' n k j}) ∧ succ' (req_fun' n k i) ∈ (Finset.biUnion Finset.univ (λ j : Fin i => {req_fun' n k j}))ᶜ then succ' (req_fun' n k i) else
            (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' n k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
      (lt_of_le_of_lt Finset.card_biUnion_le (by simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin,
          smul_eq_mul, mul_one, Fintype.card_fin, hi])),
        Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton,
          Finset.singleton_nonempty])⟩).choose) := by
  rw [← req_fun'_succ_odd n k hi hodd]
  congr
  rw [Fin.ext_iff, Fin.val_nat_cast, Nat.mod_eq_of_lt hi]

lemma req_fun'_spec_even (k : Fin (n + 1)) {i : ℕ} (hi : i + 1 < n + 1) (heven : Even i) : req_fun' n k ⟨i + 1, hi⟩ ∈ bdry (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' n k j}))ᶜ := by
  rw [req_fun'_succ_even n hi heven]
  apply Classical.choose_spec (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => Set.toFinset {req_fun' n k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
      (lt_of_le_of_lt Finset.card_biUnion_le (by
        simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one, Fintype.card_fin, hi])),
        Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton, Finset.singleton_nonempty])⟩)

lemma req13 {i : ℕ} (hi : i + 1 < n + 1) : Finset.biUnion Finset.univ (fun j : Fin (i + 1) ↦ {req_fun' n k ↑↑j}) = Finset.image (fun j ↦ req_fun' n k j) (Finset.Iic ({ val := i + 1, isLt := hi } - 1)) := by
  ext x
  refine' ⟨λ h => _, λ h => _⟩
  { simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and] at h
    --simp only [Set.toFinset_singleton, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and] at h
    cases' h with b hb
    rw [hb]
    simp only [Finset.mem_image, Finset.mem_Iic]
    refine' ⟨b, _, rfl⟩
    rw [Fin.le_def]
    have h3 : (i + 1 : Fin (n + 1)) = ⟨i + 1, hi⟩ := by
      ext
      simp only
      rw [Fin.val_add]
      simp only [Fin.val_nat_cast, Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod]
      apply Nat.mod_eq_of_lt hi
    rw [← h3]
    simp only [add_sub_cancel, Fin.val_nat_cast]
    rw [Nat.mod_eq_of_lt (lt_trans b.prop hi), Nat.mod_eq_of_lt (lt_trans (by simp only [lt_add_iff_pos_right,
      zero_lt_one]) hi)]
    apply Nat.le_of_lt_succ b.prop }
  { simp only [Finset.mem_image, Finset.mem_Iic] at h
    cases' h with b hb
    simp only [Set.toFinset_singleton, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and]
    refine' ⟨b, _⟩
    have h3 : (i + 1 : Fin (n + 1)) = ⟨i + 1, hi⟩ := by
      ext
      simp only
      rw [Fin.val_add]
      simp only [Fin.val_nat_cast, Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod]
      apply Nat.mod_eq_of_lt hi
    rw [← h3] at hb
    simp only [add_sub_cancel, Fin.val_nat_cast] at hb
    rw [← hb.2]
    congr
    simp only [Fin.val_nat_cast]
    rw [Fin.le_def] at hb
    simp only [Fin.val_nat_cast] at hb
    rw [Nat.mod_eq_of_lt (lt_trans (by simp only [lt_add_iff_pos_right,
      zero_lt_one]) hi)] at hb
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hb.1 (by simp only [lt_add_iff_pos_right,
      zero_lt_one]))]
    ext
    simp only [Fin.val_nat_cast]
    rw [Nat.mod_eq_of_lt b.prop] }

lemma req14 (x : Fin (n + 1)) : pred' x ≠ x := by
  rw [pred'_eq_add_one]
  simp only [ne_eq, sub_eq_self, Fin.one_eq_zero_iff, add_left_eq_self, NeZero.ne,
    not_false_eq_true]

lemma req15 (x : Fin (n + 1)) : succ' x ≠ x := by
  rw [succ'_eq_add_one]
  simp only [ne_eq, add_right_eq_self, Fin.one_eq_zero_iff, add_left_eq_self, NeZero.ne,
    not_false_eq_true]

lemma req_fun'_spec_odd (k : Fin (n + 1)) {i : ℕ} (hi : i + 1 < n + 1) (hodd : Odd i) : req_fun' n k ⟨i + 1, hi⟩ ∈ bdry (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' n k j}))ᶜ := by
  cases' i with i i
  · simp only [Nat.zero_eq, Nat.odd_iff_not_even, even_zero, not_true_eq_false] at hodd
  · rw [req_fun'_succ_odd n k hi hodd]
    split
    next h =>
    { rw [bdry, Finset.mem_sdiff]
      refine' ⟨_, _⟩
      · rw [req13 n hi, req13 n (lt_trans Nat.le.refl hi)] at *
        rw [Finset.Iic_eq_cons_Iio, Finset.cons_eq_insert, Finset.image_insert, Finset.mem_compl]
        intro h'
        rw [Finset.mem_insert] at h'
        cases' h' with h' h'
        · apply req14 n (req_fun' n k ↑(i + 1))
          rw [h']
          congr 1
          rw [sub_eq_of_eq_add]
          norm_cast
          ext
          rw [Fin.val_nat_cast, Nat.mod_eq_of_lt hi] -- why was simp messing this up so bad
        · rw [Finset.mem_compl] at h
          apply h.2
          apply Finset.mem_of_subset _ h'
          intro x hx
          simp only [Finset.mem_image, Finset.mem_Iio] at hx
          cases' hx with a ha
          simp only [Finset.mem_image, Finset.mem_Iic]
          refine' ⟨a, _, ha.2⟩
          rw [Fin.le_def]
          rw [Fin.lt_def] at ha
          apply Nat.le_of_lt_succ
          convert ha.1
          -- non-obvious proof, make separate lemma?
          rw [Nat.succ_eq_add_one, ← Fin.val_add_one_of_lt _, sub_add_cancel, Fin.coe_sub, Fin.val_one', Nat.one_mod_of_ne_one _, add_tsub_cancel_right, add_assoc, add_comm 1 n, Nat.add_mod_right, Nat.mod_eq_of_lt (lt_trans _ hi)]
          · apply Nat.succ_lt_succ (Nat.lt_succ_of_le le_rfl)
          · simp only [ne_eq, add_left_eq_self, NeZero.ne n, not_false_eq_true]
          · apply lt_trans (Fin.sub_one_lt_iff.2 (Fin.lt_def.2 _)) (Fin.lt_def.2 _)
            · simp only [Fin.val_zero, add_pos_iff, zero_lt_one, or_true]
            · simp only [Fin.val_last]
              apply Nat.lt_of_succ_lt_succ hi
      · intro h'
        simp only [Nat.cast_add, Nat.cast_one, int'._eq_1, nbrs, Set.mem_setOf_eq] at h'
        rw [Set.mem_toFinset] at h'
        simp only [Set.mem_setOf_eq] at h'
        rw [succ'_eq_add_one, pred'_eq_add_one, Finset.subset_iff] at h'
        simp only [sub_add_cancel, Finset.mem_insert, Finset.mem_singleton, Finset.mem_compl,
          Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists, forall_eq_or_imp, forall_eq] at h'
        apply h'.1 (i + 1 : ℕ)
        congr
        rw [Fin.val_cast_of_lt]
        · simp only [Nat.cast_add, Nat.cast_one]
        · simp only [lt_add_iff_pos_right, zero_lt_one] }
    next h =>
    { split
      next h1 =>
      { rw [bdry, Finset.mem_sdiff, int']
        refine' ⟨_, _⟩
        · rw [req13 n hi, req13 n (lt_trans Nat.le.refl hi)] at *
          rw [Finset.Iic_eq_cons_Iio, Finset.cons_eq_insert, Finset.image_insert, Finset.mem_compl]
          intro h'
          rw [Finset.mem_insert] at h'
          cases' h' with h' h'
          · apply req15 n (req_fun' n k ↑(i + 1))
            rw [h']
            congr 1
            rw [sub_eq_of_eq_add]
            norm_cast
            ext
            rw [Fin.val_nat_cast, Nat.mod_eq_of_lt hi] -- why was simp messing this up so bad
          · rw [Finset.mem_compl] at h1
            apply h1.2
            apply Finset.mem_of_subset _ h'
            intro x hx
            simp only [Finset.mem_image, Finset.mem_Iio] at hx
            cases' hx with a ha
            simp only [Finset.mem_image, Finset.mem_Iic]
            refine' ⟨a, _, ha.2⟩
            rw [Fin.le_def]
            rw [Fin.lt_def] at ha
            apply Nat.le_of_lt_succ
            convert ha.1
            -- non-obvious proof, make separate lemma?
            rw [Nat.succ_eq_add_one, ← Fin.val_add_one_of_lt _, sub_add_cancel, Fin.coe_sub, Fin.val_one', Nat.one_mod_of_ne_one _, add_tsub_cancel_right, add_assoc, add_comm 1 n, Nat.add_mod_right, Nat.mod_eq_of_lt (lt_trans _ hi)]
            · apply Nat.succ_lt_succ (Nat.lt_succ_of_le le_rfl)
            · simp only [ne_eq, add_left_eq_self, NeZero.ne n, not_false_eq_true]
            · apply lt_trans (Fin.sub_one_lt_iff.2 (Fin.lt_def.2 _)) (Fin.lt_def.2 _)
              · simp only [Fin.val_zero, add_pos_iff, zero_lt_one, or_true]
              · simp only [Fin.val_last]
                apply Nat.lt_of_succ_lt_succ hi
        · intro h'
          rw [Set.mem_toFinset] at h'
          simp only [Nat.cast_add, Nat.cast_one, nbrs, Set.mem_setOf_eq] at h'
          rw [succ'_eq_add_one, pred'_eq_add_one, succ'_eq_add_one, add_sub_cancel] at h'
          have h2 : (req_fun' n k (i + 1 : Fin (n + 1))) ∈ ({req_fun' n k (i + 1 : Fin (n + 1)) + 1 + 1, req_fun' n k (i + 1 : Fin (n + 1))} : Finset (Fin (n + 1))) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
          have h3 := h' h2
          rw [Finset.mem_compl] at h3
          apply h3
          simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and]
          refine' ⟨i + 1, _⟩
          congr
          rw [Fin.val_add_one_of_lt (Fin.lt_def.2 _)]
          · simp only [Fin.val_nat_cast, Nat.cast_add, Nat.cast_one, add_left_inj]
            rw [Nat.mod_eq_of_lt (Nat.lt_succ.2 (Nat.le_succ _))]
          · simp only [Fin.val_nat_cast, Fin.val_last]
            rw [Nat.mod_eq_of_lt (Nat.lt_succ.2 (Nat.le_succ _)), Nat.lt_succ] }
      next h1 =>
      { apply Classical.choose_spec (bdry_compl_Nonempty (Finset.biUnion Finset.univ (λ j : Fin (i.succ + 1) => Set.toFinset {req_fun' n k j})) ⟨(Finset.card_lt_iff_ne_univ _).1
          (lt_of_le_of_lt Finset.card_biUnion_le (by
          simp only [Set.toFinset_singleton, Finset.card_singleton, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one, Fintype.card_fin, hi])),
            Finset.Nonempty.biUnion Finset.univ_nonempty (λ x _ => by simp only [Set.toFinset_singleton, Finset.singleton_nonempty])⟩) } }

lemma req_fun'_spec (k : Fin (n + 1)) {i : ℕ} (hi : i + 1 < n + 1) : req_fun' n k ⟨i + 1, hi⟩ ∈ bdry (Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' n k j}))ᶜ := by
  by_cases hodd : Even i
  · apply req_fun'_spec_even _ _ _ hodd
  · rw [← Nat.odd_iff_not_even] at hodd
    apply req_fun'_spec_odd _ _ _ hodd

-- put it up and replace all instances of bUnion with this
def S (k : Fin (n + 1)) (i : ℕ) : Finset (Fin (n + 1)) := Finset.biUnion Finset.univ (λ j : Fin (i + 1) => {req_fun' n k j})

lemma Fin.le_sub_one_of_lt {b x : Fin (n + 1)} (hb : b ≠ 0) (h : x < b) : x ≤ b - 1 := by
  rw [Fin.le_def, Fin.coe_sub_one, if_neg hb]
  apply Nat.le_sub_one_of_lt h

lemma Fin.lt_of_le_add_one {a x : Fin (n + 1)} (ha : a ≠ Fin.last n) (h : a + 1 ≤ x) : a < x := by
  by_contra h'
  push_neg at h'
  have htrans := le_trans h h'
  simp only [Fin.add_one_le_iff] at htrans
  apply ha htrans

lemma Fin.lt_iff_le_add_one {a x : Fin (n + 1)} (ha : a ≠ Fin.last n) : a + 1 ≤ x ↔ a < x := ⟨λ h => Fin.lt_of_le_add_one _ ha h, λ h => Fin.add_one_le_of_lt h⟩

lemma Fin.lt_sub_of_le_sub_one {b x : Fin (n + 1)} (hb : b ≠ 0) (h : x ≤ b - 1) : x < b := by
  rw [Fin.le_def, Fin.coe_sub_one, if_neg hb, ← Nat.pred_eq_sub_one, Nat.le_pred_iff_lt (Nat.pos_of_ne_zero _), ← Fin.lt_def] at h
  · assumption
  · contrapose hb
    push_neg at *
    rw [Fin.ext_iff, hb, Fin.val_zero]

lemma Fin.lt_sub_iff_le_sub_one {b x : Fin (n + 1)} (hb : b ≠ 0) : x ≤ b - 1 ↔ x < b :=
  ⟨λ h => Fin.lt_sub_of_le_sub_one _  hb h, λ h => Fin.le_sub_one_of_lt _ hb h⟩

lemma Fin.nat_succ_succ_cast {i : ℕ} (hi : i.succ + 1 < n + 1) : (⟨i + 1 + 1, hi⟩ : Fin (n + 1)) - 1 = ↑i + 1 := by
  have hi' : i < n := by
    simp only [add_lt_add_iff_right] at hi
    apply lt_trans (Nat.lt_succ.2 (le_refl _)) hi
  have hi'' : i < n.succ := lt_trans hi' (Nat.lt_succ.2 (le_refl _))
  apply sub_eq_of_eq_add
  rw [Fin.ext_iff, Fin.val_add_one_of_lt (Fin.lt_def.2 _), Fin.val_add_one_of_lt (Fin.lt_def.2 _)]
  · simp only [Fin.val_nat_cast, add_left_inj]
    rw [Nat.mod_eq_of_lt hi'']
  · simp only [Fin.val_nat_cast, Fin.val_last]
    rw [Nat.mod_eq_of_lt hi'']
    apply hi'
  · simp only [Fin.val_last]
    rw [Fin.val_add_one_of_lt (Fin.lt_def.2 _)]
    · simp only [Fin.val_nat_cast]
      rw [Nat.mod_eq_of_lt hi'']
      simp only [add_lt_add_iff_right] at hi
      apply hi
    · simp only [Fin.val_nat_cast, Fin.val_last]
      rw [Nat.mod_eq_of_lt hi'']
      apply hi'

lemma Fin.cast_succ_val {i : ℕ} (hi : i.succ < n + 1) : i + 1 = ↑((i : Fin (n + 1)) + 1) := by
  have hi' : i < n := by
    rw [Nat.succ_eq_add_one] at hi
    simp only [add_lt_add_iff_right] at hi
    apply hi
  have hi'' : i < n.succ := lt_trans hi' (Nat.lt_succ.2 (le_refl _))
  rw [Fin.val_add_one_of_lt (Fin.lt_def.2 _)]
  · simp only [Fin.val_nat_cast, Nat.mod_eq_of_lt hi'']
  · simp only [Fin.val_nat_cast, Nat.mod_eq_of_lt hi'', Fin.val_last, hi']

lemma S_eq (k : Fin (n + 1)) {i : ℕ} (hi : i.succ + 1 < n + 1) : S n k (i + 1) = {req_fun' n k i.succ} ∪ S n k i := by
--  have hn : n + 1 ≠ 1 := by simp only [ne_eq, add_left_eq_self, NeZero.ne, not_false_eq_true]
  have h1 : (⟨i + 1 + 1, hi⟩ : Fin (n + 1)) - 1 = ↑i + 1 := Fin.nat_succ_succ_cast n hi
  have h2 : i + 1 = ↑((i : Fin (n + 1)) + 1) := Fin.cast_succ_val n (by
  simp only [add_lt_add_iff_right] at hi
  apply lt_trans hi (Nat.lt_succ.2 (le_refl _)) )
  ext x
  rw [S, req13 n hi, S, req13 n (lt_trans Nat.le.refl hi)]
  rw [Finset.Iic_eq_cons_Iio, Finset.cons_eq_insert, Finset.image_insert, Finset.mem_insert]
  -- need 2 small lemmas to vastly simplify this: one regarding the vals and the second regarding Finset.Iio _ = Finset.Iic _
  simp only [Finset.mem_image, Finset.mem_Iio, Nat.cast_succ, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_Iic]
  refine' ⟨λ h => _, λ h => _⟩
  · cases' h with h h
    · left
      rw [h]
      congr
    · right
      cases' h with a ha
      refine' ⟨a, _, ha.2⟩
      rw [h1] at ha
      apply Fin.le_sub_one_of_lt
      · intro h
        rw [Fin.ext_iff] at h
        simp only [Fin.val_zero, add_eq_zero, one_ne_zero, and_false] at h
      · convert ha.1 -- convert reads assumptions
  · cases' h with h h
    · left
      rw [h]
      symm
      congr -- congr reads assumptions as well
    · right
      cases' h with a ha
      refine' ⟨a, _, ha.2⟩
      rw [h1]
      convert Fin.lt_sub_of_le_sub_one n _ ha.1
      · rw [h2]
      · intro h
        rw [Fin.ext_iff] at h
        simp only [Fin.val_zero, add_eq_zero, one_ne_zero, and_false] at h

-- -- this proof has been used somewhere else as well, reduce duplication and make lemma
-- example (k : Fin (n + 1)) (j : ℕ) (hj : j + 1 < n + 1) (hn : n ≠ 1) : ∃ x ∈ bdry (S n k j), req_fun' n k j.succ = succ' x ∨ req_fun' n k j.succ = pred' x := by
--   have h := req_fun'_spec n k hj
--   rw [bdry, Finset.mem_sdiff, int'] at h
--   simp [nbrs] at h
--   have h' : succ' (req_fun' n k j + 1) ∈ S n k j ∨ pred' (req_fun' n k j + 1) ∈ S n k j := by
--     sorry
--   cases' h' with h' h'
--   · have h2 : succ' (req_fun' n k j + 1) ∈ bdry (S n k j) := sorry
--     refine' ⟨succ' (req_fun' n k j + 1), h2, Or.inr _⟩
--     sorry
--   · sorry --same proof as above

lemma S_nonempty (k : Fin (n + 1)) (j : ℕ) : (S n k j).Nonempty := by
  rw [S]
  simp only [Finset.biUnion_nonempty, Finset.mem_univ, Finset.singleton_nonempty, and_self,
    exists_const]

lemma S_compl_nonempty (k : Fin (n + 1)) {j : ℕ} (hj : j + 1 < n + 1) : (S n k j)ᶜ.Nonempty := by
  rw [S, ← Finset.compl_ne_univ_iff_nonempty]
  simp only [compl_compl, ne_eq]
  intro h
  rw [← Finset.card_eq_iff_eq_univ] at h
  simp only [Fintype.card_fin] at h
  have := @Finset.card_biUnion_le _ _ _ Finset.univ (fun j_1 : Fin (j + 1) ↦ {req_fun' n k ↑↑j_1})
  rw [h] at this
  simp only [Finset.card_singleton, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one, ← not_lt] at this
  apply this hj

lemma bdry_Icc (a b : Fin n) (ha : 0 < a) (hab : a ≤ b) : bdry (Finset.Icc a b) = {a, b} := by
  rw [bdry, int']
  ext x
  simp only [nbrs, Set.mem_setOf_eq, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  refine' ⟨λ h => _, λ h => _⟩
  · by_contra h'
    apply h.2
    -- make a lemma about negation of Set.mem_toFinset?
    rw [Set.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    push_neg at h'
    have h1 : a < x ∧ x < b := ⟨lt_of_le_of_ne h.1.1 h'.1.symm, lt_of_le_of_ne h.1.2 h'.2⟩
    have h2 : succ' x ∈ Finset.Icc a b ∧ pred' x ∈ Finset.Icc a b := by
    { cases' n with n n
      · simp only [Nat.zero_eq, Finset.mem_Icc, le_of_subsingleton, and_self]
      · refine' ⟨Finset.mem_Icc.2 (⟨_, _⟩), Finset.mem_Icc.2 (⟨_, _⟩)⟩
        · rw [succ'_eq_add_one]
          apply le_trans (le_of_lt h1.1) _
          by_cases hx : x = Fin.last n
          · rw [hx, ← Fin.not_le, ← Fin.not_le] at h1
            exfalso
            apply h1.2 (Fin.le_last _)
          · by_contra h2
            rw [Fin.not_le] at h2
            have h3 := le_of_lt h2
            simp only [Fin.add_one_le_iff] at h3
            apply hx h3
        · rw [succ'_eq_add_one]
          apply Fin.add_one_le_of_lt h1.2
        · rw [pred'_eq_add_one, Fin.le_def, Fin.coe_sub_one]
          by_cases hx : x = 0
          · exfalso
            rw [hx] at h1
            simp only [Fin.not_lt_zero, false_and] at h1
          · rw [if_neg hx]
            apply Nat.le_sub_one_of_lt (Fin.lt_def.1 h1.1)
        · rw [pred'_eq_add_one]
          apply le_trans _ (le_of_lt h1.2)
          by_cases hx : x = 0
          · exfalso
            rw [hx] at h1
            simp only [Fin.not_lt_zero, false_and] at h1
          · rw [Fin.le_def, Fin.coe_sub_one, if_neg hx]
            simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le] }
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    cases' hy with hy hy
    · rw [hy]
      apply h2.1
    · rw [hy]
      apply h2.2
  · cases' h with h h
    · rw [h]
      simp only [le_refl, hab, and_self, true_and]
      intro h'
      rw [Set.mem_toFinset] at h'
      simp only [Set.mem_setOf_eq] at h'
      have h1 : a ≤ pred' a := by
        rw [Finset.subset_iff] at h'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc, forall_eq_or_imp,
          forall_eq] at h'
        apply h'.2.1
      cases' n with n n
      · apply NeZero.ne 0
        rfl
      · rw [pred'_eq_add_one, Fin.le_sub_one_iff] at h1
        rw [h1] at ha
        simp only [lt_self_iff_false] at ha
    · rw [h]
      simp only [hab, le_refl, and_self, true_and]
      intro h'
      rw [Set.mem_toFinset] at h'
      simp only [Set.mem_setOf_eq] at h'
      have h1 : succ' b ≤ b := by
        rw [Finset.subset_iff] at h'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc, forall_eq_or_imp,
          forall_eq] at h'
        apply h'.1.2
      have h2 : a ≤ succ' b := by
        rw [Finset.subset_iff] at h'
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc, forall_eq_or_imp,
          forall_eq] at h'
        apply h'.1.1
      cases' n with n n
      · apply NeZero.ne 0
        rfl
      · rw [succ'_eq_add_one, Fin.add_one_le_iff] at h1
        rw [h1, succ'_eq_add_one, Fin.last_add_one] at h2
        simp only [Fin.le_zero_iff] at h2
        rw [h2] at ha
        simp only [lt_self_iff_false] at ha

-- very similar to proof of corresponding lemma for pred'
--example (a b : Fin n) : Finset.Icc a (succ' b) = Finset.Icc a b ∪ {succ' b} := sorry

lemma mem_bdry (S : Finset (Fin n)) (x : Fin n) : x ∈ bdry S ↔ x ∈ S ∧ (succ' x ∈ Sᶜ ∨ pred' x ∈ Sᶜ) := by
  refine' ⟨λ h => _, λ h => _⟩
  · rw [bdry, Finset.mem_sdiff] at h
    simp only [int'._eq_1, Set.mem_setOf_eq] at h
    refine' ⟨h.1, _⟩
    by_contra h'
    apply h.2
    rw [Set.mem_toFinset]
    simp only [nbrs, Set.mem_setOf_eq]
    push_neg at h'
    simp only [Finset.mem_compl, not_not] at h'
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    cases' hy with hy hy
    · rw [hy]
      apply h'.1
    · rw [hy]
      apply h'.2
  · rw [bdry, Finset.mem_sdiff]
    refine' ⟨h.1, _⟩
    intro h'
    simp only [int'._eq_1, nbrs, Set.mem_setOf_eq] at h'
    rw [Set.mem_toFinset] at h' -- why does this not work with simp?
    simp only [Set.mem_setOf_eq] at h'
    cases' h.2 with h h;
    any_goals
      apply Finset.mem_compl.1 h (Finset.mem_of_subset h' _)
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

lemma mem_bdry_compl (S : Finset (Fin (n + 1))) {x : Fin (n + 1)} (hx : x ∈ bdry Sᶜ) : succ' x ∈ bdry S ∨ pred' x ∈ bdry S := by
  rw [mem_bdry, compl_compl] at hx
  cases' hx.2 with h h
  · left
    rw [mem_bdry]
    refine' ⟨h, Or.inr _⟩
    rw [succ'_eq_add_one, pred'_eq_add_one, add_sub_cancel]
    apply hx.1
  · right
    rw [mem_bdry]
    refine' ⟨h, Or.inl _⟩
    rw [succ'_eq_add_one, pred'_eq_add_one, sub_add_cancel]
    apply hx.1

lemma succ'_eq_iff_eq_pred' (x y : Fin n) : succ' x = y ↔ x = pred' y := by
  rw [succ'_eq_add_one, pred'_eq_add_one]
  refine' ⟨λ h => _, λ h => _⟩
  · rw [← h]
    simp only [add_sub_cancel]
  · rw [h]
    simp only [sub_add_cancel]

lemma pred'_eq_iff_eq_succ' (x y : Fin n) : pred' x = y ↔ x = succ' y := by
  rw [succ'_eq_add_one, pred'_eq_add_one]
  refine' ⟨λ h => _, λ h => _⟩
  · rw [← h]
    simp only [sub_add_cancel]
  · rw [h]
    simp only [add_sub_cancel]

lemma pred'_ne_succ' (x : Fin (n + 1)) (hn : n ≠ 1) : pred' x ≠ succ' x := by
  intro h
  rw [succ'_eq_add_one, pred'_eq_add_one] at h
  have h' := add_eq_of_eq_sub h.symm
  rw [add_assoc] at h'
  simp only [add_right_eq_self] at h'
  rw [Fin.ext_iff, Fin.val_add_one] at h'
  have hne : n + 1 ≠ 1 := by
    intro h1
    simp only [add_left_eq_self] at h1
    apply NeZero.ne n h1
  split_ifs at h'
  · next h1 =>
    { rw [← Fin.cast_nat_eq_last, Fin.ext_iff] at h1
      simp only [Fin.val_one', Fin.cast_nat_eq_last, Fin.val_last] at h1
      rw [Nat.one_mod_of_ne_one hne] at h1
      apply hn h1.symm }
  · next h1 =>
    { simp only [Fin.val_one', Fin.val_zero, add_eq_zero, one_ne_zero, and_false] at h' }

lemma succ'_ne_self (x : Fin (n + 1)) : succ' x ≠ x := by
  intro hx
  rw [succ'_eq_add_one] at hx
  simp only [add_right_eq_self, Fin.one_eq_zero_iff, add_left_eq_self] at hx
  apply NeZero.ne n hx

lemma pred'_ne_self (x : Fin (n + 1)) : pred' x ≠ x := by
  intro hx
  rw [pred'_eq_add_one] at hx
  simp only [sub_eq_self, Fin.one_eq_zero_iff, add_left_eq_self] at hx
  apply NeZero.ne n hx

lemma bdry_Icc_compl (a b : Fin (n + 1)) (ha : 0 < a) (hab : a ≤ b) : bdry (Finset.Icc a b)ᶜ = {pred' a, succ' b} := by
  ext y
  refine' ⟨λ h => _, λ h => _⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    have hy := mem_bdry_compl n _ h
    rw [bdry_Icc _ _ _ ha hab] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [succ'_eq_iff_eq_pred', succ'_eq_iff_eq_pred', pred'_eq_iff_eq_succ', pred'_eq_iff_eq_succ'] at hy
    cases' hy with hy hy
    · cases' hy with hy hy
      · rw [hy]
        simp only [true_or]
      · by_cases hb : a = b
        · rw [← hb] at hy
          rw [hy]
          simp only [true_or]
        · exfalso
          rw [bdry, Finset.mem_sdiff, Finset.mem_compl] at h
          apply h.1
          rw [hy, pred'_eq_add_one]
          simp only [Finset.mem_Icc]
          --cases' n with n n
          --· simp only [Nat.zero_eq, le_of_subsingleton, and_self]
          · rw [Fin.le_def, Fin.coe_sub_one, Fin.le_def, Fin.coe_sub_one]
            by_cases hb1 : b = 0
            · exfalso
              rw [hb1] at hab
              simp only [Fin.le_zero_iff] at hab
              rw [hab] at ha
              simp only [lt_self_iff_false] at ha
            · rw [if_neg hb1]
              refine' ⟨Nat.le_sub_one_of_lt (Fin.lt_def.1 (lt_of_le_of_ne hab hb)), Nat.sub_le _ _⟩
    · cases' hy with hy hy
      · by_cases hb : a = b
        · rw [hb] at hy
          rw [hy]
          simp only [or_true]
        · exfalso
          rw [bdry, Finset.mem_sdiff, Finset.mem_compl] at h
          apply h.1
          rw [hy, succ'_eq_add_one]
          simp only [Finset.mem_Icc]
          --cases' n with n n
          --· simp only [Nat.zero_eq, le_of_subsingleton, and_self]
          · --rw [Fin.le_def, Fin.le_def]
            have hab' := lt_of_le_of_ne hab hb
            by_cases ha1 : a = Fin.last n
            · exfalso
              rw [ha1] at hab
              apply hb
              rw [Fin.last_le_iff] at hab
              rw [ha1, hab]
            · have ha2 := lt_of_le_of_ne (Fin.le_last _) ha1
              refine' ⟨le_of_lt (Fin.lt_add_one_iff.2 ha2), _⟩
              rw [Fin.le_def, Fin.val_add_one_of_lt ha2, Nat.add_one_le_iff, ← Fin.lt_def]
              assumption
      · rw [hy]
        simp only [or_true]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    cases' h with h h
    · rw [h, mem_bdry, compl_compl, succ'_eq_add_one, pred'_eq_add_one]
      simp only [Finset.mem_compl, Finset.mem_Icc, not_and, not_le, sub_add_cancel, le_refl, hab,
        and_self, true_or, and_true]
      cases' n with n n
      · exfalso
        apply NeZero.ne 0
        rfl
      · intro h'
        rw [Fin.le_sub_one_iff] at h'
        exfalso
        rw [h'] at ha
        simp only [lt_self_iff_false] at ha
    · rw [h, mem_bdry, compl_compl, succ'_eq_add_one, pred'_eq_add_one, add_sub_cancel]
      simp only [Finset.mem_compl, Finset.mem_Icc, not_and, not_le, sub_add_cancel, le_refl, hab,
        and_self, or_true, and_true]
      --cases' n with n n
      /-· exfalso
        apply NeZero.ne 0
        rfl-/
      · intro h'
        rw [Fin.lt_add_one_iff]
        by_cases hb : b = Fin.last n
        · rw [hb] at h'
          simp only [Fin.last_add_one, Fin.le_zero_iff] at h'
          rw [h'] at ha
          simp only [lt_self_iff_false] at ha
        apply lt_of_le_of_ne (Fin.le_last _) hb

lemma pred'_le_self (a : Fin n) (ha : 0 < a) : pred' a ≤ a := by
  rw [pred'_eq_add_one]
  cases' n with n n
  · simp only [Nat.zero_eq, le_of_subsingleton]
  · rw [Fin.le_def, Fin.coe_sub_one, if_neg (Fin.pos_iff_ne_zero.1 ha)]
    simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]

lemma self_le_succ' (a : Fin (n + 1)) (ha : a ≠ Fin.last n) : a ≤ succ' a := by
  rw [succ'_eq_add_one]
  by_contra h
  apply ha
  rw [← Fin.add_one_le_iff]
  push_neg at h
  apply le_of_lt h

lemma pred'_one : pred' (1 : Fin n) = 0 := by rw [pred'_eq_add_one, sub_self]

lemma pred'_union_Icc (a b : Fin n) (ha : 0 < a) (hab : a ≤ b) : {pred' a} ∪ Finset.Icc a b = Finset.Icc (pred' a) b := by
  ext x
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
  refine' ⟨λ h => _, λ h => _⟩
  · cases' h with h h
    · rw [h]
      simp only [le_refl, true_and]
      apply le_trans (pred'_le_self n a ha) hab
    · refine' ⟨le_trans (pred'_le_self n a ha) h.1, h.2⟩
  · by_cases hx : x = pred' a
    · apply Or.inl hx
    · refine' Or.inr ⟨_, h.2⟩
      rw [le_iff_lt_or_eq] at h
      cases' n with n n
      · simp only [Nat.zero_eq, le_of_subsingleton]
      cases' h.1 with h h
      · rw [Fin.le_def]
        rw [pred'_eq_add_one, Fin.lt_def, Fin.coe_sub_one, if_neg (Fin.pos_iff_ne_zero.1 ha)] at h
        apply Nat.le_of_pred_lt h
      · exfalso
        apply hx
        rw [h]

lemma Icc_union_succ' {a b : Fin (n + 1)} (hb : b ≠ Fin.last n) (hab : a ≤ b) : Finset.Icc a b ∪ {succ' b} = Finset.Icc a (succ' b) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
  refine' ⟨λ h => _, λ h => _⟩
  · cases' h with h h
    · refine' ⟨h.1, le_trans h.2 (self_le_succ' _ _ hb)⟩
    · rw [h]
      simp only [le_refl, and_true, le_trans hab (self_le_succ' n _ hb)]
  · by_cases hx : x = succ' b
    · apply Or.inr hx
    · refine' Or.inl ⟨h.1, _⟩
      rw [le_iff_lt_or_eq, le_iff_lt_or_eq] at h
      cases' h.2 with h h
      · rw [Fin.le_def]
        rw [succ'_eq_add_one, Fin.lt_def, Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) hb)] at h
        apply Nat.le_of_lt_succ h
      · exfalso
        apply hx
        rw [h]

-- there is a typeclass inference problem / dimaond here
/-example (a : Fin n) (s : Finset (Fin n)) (hs : s.Nonempty) : Finset.min' (insert a s) (Finset.insert_nonempty a s) = min (Finset.min' s hs) a := by
  rw [← Finset.min'_insert a s hs]
  congr 3-/

lemma min'_pos_of_zero_mem_compl {T : Finset (Fin (n + 1))} (hT : T.Nonempty) (zero_mem : 0 ∈ Tᶜ) : 0 < Finset.min' T hT := by
  apply Fin.pos_of_ne_zero _
  intro h
  rw [← h, Finset.mem_compl] at zero_mem
  apply zero_mem (Finset.min'_mem _ _)

-- generalize
lemma min'_le_max' {T : Finset (Fin (n + 1))} (hT : T.Nonempty) : Finset.min' T hT ≤ Finset.max' T hT := Finset.min'_le _ _ (Finset.max'_mem _ _)

lemma S_eq_Icc_of_zero_in_compl (k : Fin (n + 1)) (j : ℕ) (hj : j + 1 < n + 1) (h : 0 ∈ (S n k j)ᶜ) : S n k j = Finset.Icc (Finset.min' (S n k j) (S_nonempty n k j)) (Finset.max' (S n k j) (S_nonempty n k j)) := by
  induction j with
  | zero =>
      dsimp [S]
      simp only [Fin.coe_fin_one, Nat.cast_zero, Finset.singleton_biUnion, Finset.min'_singleton,
        Finset.max'_singleton, Finset.Icc_self]
  | succ j hd =>
      have h0 : 0 ∈ (S n k j)ᶜ := by
        rw [S_eq _ _ hj] at h
        simp only [Nat.cast_succ, Finset.compl_union, Finset.mem_inter, Finset.mem_singleton] at h
        apply h.2
      have hmin : 0 < Finset.min' (S n k j) (S_nonempty _ _ _) := min'_pos_of_zero_mem_compl n (S_nonempty _ _ _) h0
      have min_le_max : Finset.min' (S n k j) (S_nonempty _ _ _) ≤ Finset.max' (S n k j) (S_nonempty _ _ _) := min'_le_max' _ _
      specialize hd (lt_trans Nat.le.refl hj) h0
      have css : req_fun' n k j.succ = pred' (Finset.min' (S n k j) (S_nonempty _ _ _)) ∨ req_fun' n k j.succ = succ' (Finset.max' (S n k j) (S_nonempty _ _ _)) := by
        have h1 : req_fun' n k j.succ ∈ bdry (S n k j)ᶜ := by
          rw [S]
          convert req_fun'_spec n k (lt_trans Nat.le.refl hj)
          simp only [Nat.cast_succ]
          rw [← Fin.cast_succ_val n (lt_trans (Nat.lt_succ.2 (le_refl _)) hj)]
        rw [hd] at h1
        rw [bdry_Icc_compl n _ _ hmin min_le_max] at h1
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1
        apply h1
      cases' css with css css
      · conv_lhs => rw [S_eq n k hj]
        rw [hd, css, pred'_union_Icc _ _ _ hmin min_le_max]
        congr 1
        · conv_rhs => {
          congr
          rw [S_eq n k hj, ← Finset.insert_eq] }
          symm
          have h1 :  Finset.min' (insert (req_fun' n k ↑(Nat.succ j)) (S n k j)) (Finset.insert_nonempty _ _) = min (Finset.min' (S n k j) (S_nonempty _ _ _)) (req_fun' n k ↑(Nat.succ j)) := by
            convert Finset.min'_insert _ _ _ -- need to solve typeclass inference problem / diamond in Finset.min'_insert
          rw [h1, css]
          apply min_eq_right (pred'_le_self (n + 1) _ hmin)
        · -- same as above
          conv_rhs => {
          congr
          rw [S_eq n k hj, ← Finset.insert_eq] }
          symm
          have h1 :  Finset.max' (insert (req_fun' n k ↑(Nat.succ j)) (S n k j)) (Finset.insert_nonempty _ _) = max (Finset.max' (S n k j) (S_nonempty _ _ _)) (req_fun' n k ↑(Nat.succ j)) := by
            convert Finset.max'_insert _ _ _ -- need to solve typeclass inference problem / diamond in Finset.min'_insert
          rw [h1, css]
          apply max_eq_left (le_trans (pred'_le_self (n + 1) _ hmin) min_le_max)
      · -- same as above
        by_cases hmax : Finset.max' (S n k j) (S_nonempty _ _ _) = Fin.last n
        · rw [hmax, succ'_eq_add_one, Fin.last_add_one] at css
          rw [← css, Finset.mem_compl] at h
          exfalso
          apply h
          rw [S]
          simp only [Nat.cast_succ, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton,
            true_and]
          refine' ⟨j + 1, _⟩
          congr
          rw [← Fin.cast_succ_val _ (Nat.lt_succ.2 (le_refl _))]
          simp only [Nat.cast_add, Nat.cast_one]
        conv_lhs => rw [S_eq n k hj]
        rw [hd, css, Finset.union_comm, Icc_union_succ' _ hmax min_le_max]
        congr 1
        · conv_rhs => {
          congr
          rw [S_eq n k hj, ← Finset.insert_eq] }
          symm
          have h1 :  Finset.min' (insert (req_fun' n k ↑(Nat.succ j)) (S n k j)) (Finset.insert_nonempty _ _) = min (Finset.min' (S n k j) (S_nonempty _ _ _)) (req_fun' n k ↑(Nat.succ j)) := by
            convert Finset.min'_insert _ _ _ -- need to solve typeclass inference problem / diamond in Finset.min'_insert
          rw [h1, css]
          apply min_eq_left (le_trans min_le_max (self_le_succ' _ _ hmax)) --(pred'_le_self (n + 1) _ hmin)
        · -- same as above
          conv_rhs => {
          congr
          rw [S_eq n k hj, ← Finset.insert_eq] }
          symm
          have h1 :  Finset.max' (insert (req_fun' n k ↑(Nat.succ j)) (S n k j)) (Finset.insert_nonempty _ _) = max (Finset.max' (S n k j) (S_nonempty _ _ _)) (req_fun' n k ↑(Nat.succ j)) := by
            convert Finset.max'_insert _ _ _ -- need to solve typeclass inference problem / diamond in Finset.min'_insert
          rw [h1, css]
          apply max_eq_right (self_le_succ' _ _ hmax)

-- also use in above lemma
lemma Finset_eq_Icc_of_eq_Icc {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] {S : Finset α} (nonempty : Finset.Nonempty S) {a b : α} (hs : S = Finset.Icc a b) (hab : a ≤ b) : S = Finset.Icc (Finset.min' S nonempty) (Finset.max' S nonempty) := by
  have : Finset.min' S nonempty = a ∧ Finset.max' S nonempty = b := by
    have ha : a ∈ S := by
      rw [hs]
      simp only [Finset.mem_Icc, le_refl, true_and, hab]
    have hb : b ∈ S := by
      rw [hs]
      simp only [Finset.mem_Icc, le_refl, true_and, hab]
    have hmin := Finset.min'_mem S nonempty
    conv at hmin =>
    { congr
      · skip
      · rw [hs] }
    rw [Finset.mem_Icc] at hmin
    have hmax := Finset.max'_mem S nonempty
    conv at hmax =>
    { congr
      · skip
      · rw [hs] }
    rw [Finset.mem_Icc] at hmax
    refine' ⟨le_antisymm (Finset.min'_le _ _ ha) hmin.1, le_antisymm hmax.2 (Finset.le_max' _ _ hb)⟩
  rw [this.1, this.2, hs]

-- maybe can just write = Finset.Icc min' max'
lemma Icc_erase_bdry_eq_Icc {a b c : Fin (n + 1)} (hpos : 0 < a) (hle : a ≤ b) (hc : c ∈ bdry (Finset.Icc a b)) : (Finset.Icc a b).erase c = Finset.Icc (succ' a) b ∨ (Finset.Icc a b).erase c = Finset.Icc a (pred' b) := by
  rw [bdry_Icc _ _ _ hpos hle] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  cases' hc with hc hc
  · rw [hc, succ'_eq_add_one]
    by_cases ha : a = Fin.last n
    · right
      rw [ha] at hle
      simp only [Fin.last_le_iff] at hle
      rw [ha, hle, pred'_eq_add_one]
      ext x
      simp only [Finset.Icc_self, Finset.erase_singleton, Finset.not_mem_empty, Finset.mem_Icc,
        Fin.last_le_iff, false_iff, not_and, not_le]
      intro hx
      rw [hx]
      simp only [Fin.sub_one_lt_iff, Fin.last_pos']
    · left
      ext x
      simp only [Finset.Icc_erase_left, Finset.mem_Ioc, Finset.mem_Icc, and_congr_left_iff]
      intro
      rw [Fin.lt_iff_le_add_one _ ha]
  · right
    rw [hc, pred'_eq_add_one]
    ext x
    simp only [Finset.Icc_erase_right, Finset.mem_Ico, Finset.mem_Icc, and_congr_right_iff]
    by_cases h' : b = 0
    · rw [h'] at hle
      simp only [Fin.le_zero_iff] at hle
      rw [hle] at hpos
      simp only [lt_self_iff_false] at hpos
    · intro
      rw [Fin.lt_sub_iff_le_sub_one _ h']

lemma S_compl_succ (k : Fin (n + 1)) {j : ℕ} (hj : j.succ + 1 < n + 1) : (S n k j.succ)ᶜ = (S n k j)ᶜ.erase (req_fun' n k (Nat.succ j)) := by
  rw [S_eq _ _ hj]
  ext x
  simp only [Nat.cast_succ, Finset.mem_erase, ne_eq, Finset.mem_compl, Finset.compl_union,
    Finset.mem_inter, Finset.mem_singleton]

lemma Fin.eq_one_of_le_one_and_pos {i : Fin (n + 1)} (hpos : 0 < i) (hone : i ≤ 1) : i = 1 := by
  apply le_antisymm hone _
  conv =>
    { congr
      rw [← zero_add 1] }
  apply Fin.add_one_le_of_lt hpos

lemma Fin.last_eq_neg_one : Fin.last n = -1 := by
  apply eq_neg_of_add_eq_zero_left
  simp only [last_add_one]

lemma Fin.one_le_of_ne_zero {x : Fin (n + 1)} (hx : x ≠ 0) : 1 ≤ x := by
  rw [← zero_add (1 : Fin (n + 1))]
  apply Fin.add_one_le_of_lt (Fin.pos_of_ne_zero hx)

lemma congr_compl {T1 T2 : Finset (Fin (n + 1))} (h : T1ᶜ = T2ᶜ) : T1 = T2 := by
  rw [← compl_compl T1, ← compl_compl T2, h]

lemma zero_compl_eq_Icc_one_last : {(0 : Fin (n + 1))}ᶜ = Finset.Icc 1 (Fin.last n) := by
  rw [← Finset.Icc_self]
  apply congr_compl
  rw [compl_compl]
  ext x
  simp only [Finset.Icc_self, Finset.mem_singleton, Finset.mem_compl, Finset.mem_Icc, not_and,
    not_le]
  refine' ⟨λ h1 h2 => _, λ h => _⟩
  · rw [h1] at h2
    simp only [Fin.le_zero_iff, Fin.one_eq_zero_iff, add_left_eq_self] at h2
    exfalso
    apply NeZero.ne n h2
  · by_cases hx : x = 0
    · rw [hx]
    · have h1 : 1 ≤ x := by
        rw [← zero_add (1 : Fin (n + 1))]
        apply Fin.add_one_le_of_lt (Fin.pos_of_ne_zero hx)
      specialize h h1
      exfalso
      rw [← not_le] at h
      apply h (Fin.le_last _)

--use and move up
lemma S_card_le (k : ℕ) (i : ℕ) : (S n k i).card ≤ i + 1 := by
  rw [S]
  apply le_trans Finset.card_biUnion_le _
  simp only [Finset.card_singleton, Finset.sum_const, Finset.card_fin, smul_eq_mul,
    mul_one, le_refl]

-- move up and use
lemma req_fun'_spec' (k : ℕ) {i : ℕ} (hi : i + 1 < (n + 1)) : req_fun' n k (i + 1) ∈ bdry (S n k i)ᶜ := by
  have := req_fun'_spec n k hi
  rw [S]
  convert this
  rw [← Fin.cast_succ_val _ hi]

 -- needed for surjectivity
lemma req_fun'_inj (k : ℕ) : Function.Injective (req_fun' n k) := by
  intros x y h
  by_contra ne
  by_cases lt : x < y
  · by_cases hzero : y = 0
    · -- contradiction
      rw [hzero] at lt
      simp only [Fin.not_lt_zero] at lt
    have hy : (y - 1).val + 1 < n + 1 := by
      rw [← Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) _), sub_add_cancel]
      · apply Fin.is_lt _
      · intro heq
        rw [sub_eq_iff_eq_add, Fin.last_add_one] at heq
        apply hzero heq
    have rf_bdry := req_fun'_spec' n k hy
    rw [bdry, Finset.mem_sdiff] at rf_bdry
    have h1 := rf_bdry.1
    rw [S] at h1
    simp only [Fin.cast_val_eq_self, sub_add_cancel, Finset.mem_compl, Finset.mem_biUnion,
      Finset.mem_univ, Finset.mem_singleton, true_and, not_exists] at h1
    apply h1 x
    rw [← h]
    congr
    rw [Fin.val_nat_cast, Nat.mod_eq_of_lt _, Fin.cast_val_eq_self]
    · rw [Fin.lt_def] at lt
      apply lt_of_lt_of_le lt _
      have : y = y - 1 + 1 := by simp only [sub_add_cancel]
      conv =>
        { congr
          rw [this] }
      rw [Fin.val_add_one]
      split_ifs
      · next h2 =>
        { have h3 := eq_add_of_sub_eq h2
          rw [Fin.last_add_one] at h3
          rw [h3]
          simp only [zero_sub, Fin.coe_neg_one, zero_le] }
      · simp only [le_refl]
  · -- same as above with x and y interchanged
    by_cases hzero : x = 0
    · -- contradiction
      rw [hzero] at lt
      simp only [not_lt, Fin.le_zero_iff] at lt
      apply ne
      rw [hzero, lt]
    have hy : (x - 1).val + 1 < n + 1 := by
      rw [← Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) _), sub_add_cancel]
      · apply Fin.is_lt _
      · intro heq
        rw [sub_eq_iff_eq_add, Fin.last_add_one] at heq
        apply hzero heq
    have rf_bdry := req_fun'_spec' n k hy
    rw [bdry, Finset.mem_sdiff] at rf_bdry
    have h1 := rf_bdry.1
    rw [S] at h1
    simp only [Fin.cast_val_eq_self, sub_add_cancel, Finset.mem_compl, Finset.mem_biUnion,
      Finset.mem_univ, Finset.mem_singleton, true_and, not_exists] at h1
    apply h1 y
    rw [h]
    congr
    rw [Fin.val_nat_cast, Nat.mod_eq_of_lt _, Fin.cast_val_eq_self]
    · rw [Fin.lt_def] at lt
      apply lt_of_lt_of_le (lt_of_le_of_ne (not_lt.1 lt) _) _
      · contrapose ne
        push_neg at *
        rw [← Fin.ext_iff] at ne
        rw [ne]
      have : x = x - 1 + 1 := by simp only [sub_add_cancel]
      conv =>
        { congr
          rw [this] }
      rw [Fin.val_add_one]
      split_ifs
      · next h2 =>
        { have h3 := eq_add_of_sub_eq h2
          rw [Fin.last_add_one] at h3
          rw [h3]
          simp only [zero_sub, Fin.coe_neg_one, zero_le] }
      · simp only [le_refl]

lemma req_fun'_surj (k : ℕ) : Function.Surjective (req_fun' n k) := by
  apply Function.Injective.surjective_of_fintype (Equiv.refl _) (req_fun'_inj n k)

lemma S_card_eq (k : ℕ) {i : ℕ} (hi : i + 1 < n + 1) : (S n k i).card = i + 1 := by
  rw [S, Finset.card_biUnion]
  · simp only [Finset.card_singleton, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]
  · intros x _ y _ h
    simp only [Finset.disjoint_singleton_right, Finset.mem_singleton]
    apply Function.Injective.ne (req_fun'_inj _ _)
    contrapose h
    push_neg at *
    rw [Fin.ext_iff, Fin.val_nat_cast, Fin.val_nat_cast, Nat.mod_eq_of_lt (lt_trans (Fin.is_lt _) hi), Nat.mod_eq_of_lt (lt_trans (Fin.is_lt _) hi), ← Fin.ext_iff] at h
    rw [h]

lemma S_card_eq' (k : Fin (n + 1)) {i : ℕ} (hi : i + 1 < n + 1) : (S n k i).card = i + 1 := by
  have := S_card_eq n k hi
  simp only [Fin.cast_val_eq_self] at this
  rw [this]

-- first prove S_compl_nonempty which states that Sᶜ is nonempty
-- always try to show first that Sᶜ = Finset.Icc _ _  and then use Finset_eq_Icc_of_eq_Icc
lemma S_compl_eq_Icc_of_zero_in_self (k : Fin (n + 1)) (j : ℕ) (hj : j + 1 < n + 1) (h : 0 ∈ (S n k j)) : (S n k j)ᶜ = Finset.Icc (Finset.min' (S n k j)ᶜ (S_compl_nonempty n k hj)) (Finset.max' (S n k j)ᶜ (S_compl_nonempty n k hj)) := by
  have hn : n + 1 ≠ 1 := by simp only [ne_eq, add_left_eq_self, NeZero.ne, not_false_eq_true]
  induction j with
  | zero =>
      dsimp [S]
      simp only [Fin.isValue, Fin.coe_fin_one, Nat.cast_zero, Finset.singleton_biUnion]
      rw [S] at h
      simp only [Nat.zero_eq, Fintype.univ_ofSubsingleton, Fin.zero_eta, Fin.isValue,
        Fin.coe_fin_one, Nat.cast_zero, Finset.singleton_biUnion, Finset.mem_singleton] at h
      have compl_eq : ({req_fun' n k 0}ᶜ : Finset (Fin (n + 1))) = Finset.Icc (1 : Fin (n + 1)) (Fin.last n) := by
        rw [← h]
        apply zero_compl_eq_Icc_one_last _
      apply Finset_eq_Icc_of_eq_Icc _ compl_eq
      rw [Fin.le_def]
      simp only [Fin.val_one', Fin.val_last]
      rw [Nat.one_mod_of_ne_one]
      · rw [Nat.succ_le]
        apply Nat.pos_of_ne_zero (NeZero.ne _)
      · simp only [ne_eq, add_left_eq_self, NeZero.ne, not_false_eq_true]
  | succ j hd =>
      have succ_lt : Nat.succ j < n + 1 := lt_trans (Nat.lt_succ.2 (le_refl _)) hj
      have h_succ := S_compl_succ n k hj
      rw [S_eq _ _ hj] at h
      simp only [Finset.mem_union, Finset.mem_singleton] at h
      have rfun_bdry : req_fun' n k j.succ ∈ bdry (S n k j)ᶜ := by
        convert req_fun'_spec n k succ_lt
        simp only [Nat.cast_succ]
        rw [← Fin.cast_succ_val _ succ_lt]
      cases' h with h h
      · have zero_not_mem : ¬ 0 ∈ (S n k j) := by
          rw [h, ← Finset.mem_compl]
          rw [bdry, Finset.mem_sdiff] at rfun_bdry
          apply rfun_bdry.1
        rw [← Finset.mem_compl] at zero_not_mem
        have hS := S_eq_Icc_of_zero_in_compl n k j succ_lt zero_not_mem
        have hmin : 0 < Finset.min' (S n k j) (S_nonempty _ _ _) := min'_pos_of_zero_mem_compl n (S_nonempty _ _ _) zero_not_mem
        have min_le_max : Finset.min' (S n k j) (S_nonempty _ _ _) ≤ Finset.max' (S n k j) (S_nonempty _ _ _) := min'_le_max' _ _
        -- make separate lemma?
        have h' : Finset.min' (S n k j) (S_nonempty n k j) = 1 ∨ Finset.max' (S n k j) (S_nonempty n k j) = Fin.last n := by
          have := mem_bdry_compl n _ rfun_bdry
          rw [hS, bdry_Icc _ _ _ hmin min_le_max, ← h, succ'_eq_add_one, pred'_eq_add_one] at this
          simp only [zero_add, Finset.mem_insert, Finset.mem_singleton, zero_sub] at this
          cases' this with this this
          · cases' this with this this
            · left
              rw [this]
            · rw [← this] at min_le_max
              have hone := Fin.eq_one_of_le_one_and_pos n hmin min_le_max
              left
              rw [hone]
          · cases' this with this this
            · right
              rw [← this, ← Fin.last_eq_neg_one, Fin.last_le_iff] at min_le_max
              rw [min_le_max]
            · right
              rw [← this, ← Fin.last_eq_neg_one]
        cases' h' with h' h'
        · -- also make separate lemma?
          have hS_succ : S n k (Nat.succ j) = Finset.Icc 0 (Finset.max' (S n k j) (S_nonempty n k j)) := by
            rw [h'] at hmin
            rw [h'] at min_le_max
            rw [S_eq _ _ hj, ← h]
            conv_lhs => rw [← pred'_one, hS, h', pred'_union_Icc _ _ _ hmin min_le_max, pred'_one]
          have hS_compl : (S n k (Nat.succ j))ᶜ = Finset.Icc (succ' (Finset.max' (S n k j) (S_nonempty n k j))) (Fin.last n) := by
            conv_lhs => rw [hS_succ]
            ext x
            simp only [Finset.mem_compl, Finset.mem_Icc, Fin.zero_le, true_and, not_le,
              Finset.max'_lt_iff, succ'_eq_add_one, Fin.le_last, and_true]
            refine' ⟨λ h => Fin.add_one_le_of_lt (h _ (Finset.max'_mem _ (S_nonempty _ _ _))), λ h => _⟩
            intro y hy
            rw [hS, Finset.mem_Icc] at hy
            apply lt_of_le_of_lt hy.2 (Fin.lt_of_le_add_one _ _ h)
            intro hmax
            rw [hmax] at hS_succ
            have hcard :  Finset.card (S n k (Nat.succ j)) = Finset.card (Finset.Icc 0 (Fin.last n)) := by rw [hS_succ]
            rw [Fin.card_Icc] at hcard
            -- make separate lemma
            have hS_card : (S n k (Nat.succ j)).card ≤ j.succ + 1 := by
              rw [S]
              apply le_trans Finset.card_biUnion_le _
              simp only [Finset.card_singleton, Finset.sum_const, Finset.card_fin, smul_eq_mul,
                mul_one, le_refl]
            rw [hcard] at hS_card
            simp only [Fin.val_last, Fin.val_zero, tsub_zero, add_le_add_iff_right] at hS_card
            rw [← not_lt] at hS_card
            apply hS_card (Nat.lt_of_add_lt_add_right hj)
          apply Finset_eq_Icc_of_eq_Icc _ hS_compl (Fin.le_last _)
        · -- similar to above
          have hS_succ : S n k (Nat.succ j) = {0} ∪ Finset.Icc (Finset.min' (S n k j) (S_nonempty n k j)) (Fin.last n) := by
            --rw [h'] at hmin
            rw [h'] at min_le_max
            rw [S_eq _ _ hj, ← h]
            conv_lhs => rw [hS, h']
          have hS_compl : (S n k (Nat.succ j))ᶜ = Finset.Icc 1 (pred' (Finset.min' (S n k j) (S_nonempty n k j))) := by
            rw [hS_succ]
            ext x
            simp only [Finset.compl_union, Finset.mem_inter, Finset.mem_compl, Finset.mem_singleton,
              Finset.mem_Icc, Fin.le_last, and_true, not_le, Finset.lt_min'_iff, pred'_eq_add_one]
            rw [Fin.lt_sub_iff_le_sub_one]
            refine' ⟨λ h => ⟨Fin.one_le_of_ne_zero _ h.1, _⟩, λ h => ⟨_, _⟩⟩
            · apply h.2 _ (Finset.min'_mem _ _)
            · intro hzero
              rw [hzero] at h
              simp only [Fin.le_zero_iff, Fin.one_eq_zero_iff, add_left_eq_self, Fin.zero_le,
                and_true] at h
              apply NeZero.ne n h.1
            · intro y hy
              apply lt_of_lt_of_le h.2 _
              rw [hS] at hy
              simp only [Finset.mem_Icc] at hy
              apply hy.1
            · intro hzero
              rw [← hzero, Finset.mem_compl] at zero_not_mem
              apply zero_not_mem (Finset.min'_mem _ _)
          apply Finset_eq_Icc_of_eq_Icc _ hS_compl
          rw [pred'_eq_add_one]
          -- contradiction follows from : if min' = 1 then S n k j.succ is the whole set
          rw [← zero_add (1 : Fin (n + 1))]
          apply Fin.add_one_le_of_lt (Fin.pos_of_ne_zero _)
          intro heq
          rw [sub_eq_zero, zero_add] at heq
          rw [heq, h'] at hS
          have hS_card_le := S_card_le n k j
          rw [Fin.cast_val_eq_self, hS, Fin.card_Icc, Fin.val_last, Fin.val_one', Nat.one_mod_of_ne_one hn, Nat.add_sub_cancel, ← not_lt] at hS_card_le
          apply hS_card_le
          simp only [add_lt_add_iff_right] at hj
          apply hj
      · have hd1 := hd (lt_trans Nat.le.refl hj) h -- specialize is really slow
        have min'_ne_max' : Finset.min' (S n k j)ᶜ (S_compl_nonempty _ _ succ_lt) ≠ Finset.max' (S n k j)ᶜ (S_compl_nonempty _ _ succ_lt) := by
          intro heq
          have hS_compl_card : (S n k j)ᶜ.card = 1 := by
            rw [hd1, heq, Finset.Icc_self, Finset.card_singleton]
          rw [Finset.card_compl, S_card_eq' n k succ_lt, Fintype.card_fin, Nat.sub_eq_iff_eq_add _, ← Nat.sub_eq_iff_eq_add' _] at hS_compl_card
          rw [Nat.succ_eq_add_one, ← hS_compl_card] at hj
          simp only [Fintype.card_fin, add_tsub_cancel_right, lt_self_iff_false] at hj
          · simp only [Fintype.card_fin, le_add_iff_nonneg_left, zero_le]
          · apply le_of_lt succ_lt
        --have rf_bdry : req_fun' n k j.succ ∈ bdry (S n k j)ᶜ := by sorry
        rw [hd1] at rfun_bdry
        have hmin : 0 < Finset.min' (S n k j)ᶜ (S_compl_nonempty _ _ succ_lt) := min'_pos_of_zero_mem_compl _ _ (by
          rw [compl_compl]
          apply h )
        have min_le_max : Finset.min' (S n k j)ᶜ (S_compl_nonempty _ _ succ_lt) ≤ Finset.max' (S n k j)ᶜ (S_compl_nonempty _ _ succ_lt) := min'_le_max' _ _
        have hS_succ := Icc_erase_bdry_eq_Icc n hmin min_le_max rfun_bdry
        rw [← hd1, ← h_succ] at hS_succ
        cases' hS_succ with hss hss
        · apply Finset_eq_Icc_of_eq_Icc _ hss
          -- this is same as saying min' < max' ; if not, then card of (S n k j)ᶜ is 1 => j = n => contradicts hj
          rw [succ'_eq_add_one]
          apply Fin.add_one_le_of_lt (lt_of_le_of_ne min_le_max min'_ne_max')
        · apply Finset_eq_Icc_of_eq_Icc _ hss
          -- same reasoning as above
          rw [pred'_eq_add_one]
          apply Fin.le_sub_one_of_lt _ _ (lt_of_le_of_ne min_le_max min'_ne_max')
          intro heq
          rw [heq, Fin.le_zero_iff] at min_le_max
          rw [min_le_max] at hmin
          simp only [lt_self_iff_false] at hmin

-- proof is very easy now using the explicit form of S n k j
-- lemma bdry_card (k : Fin (n + 1)) {i : ℕ} (hi : i + 1 < n + 1) : (bdry (S n k i)).card = 2 := by
--   revert hi
--   apply Nat.strongInductionOn i
--   intro j hj
--   cases' j with j j
--   · sorry
--   · intro h
--     refine Finset.card_eq_two.mpr ?succ.a
--     obtain ⟨x, y, hxy, h1⟩ := Finset.card_eq_two.1 (hj j Nat.le.refl (lt_trans Nat.le.refl h))
--     --rw [S_eq n k h, bdry]
--     --rw [Finset.ext_iff, bdry, int'] at h1
--     --simp [nbrs] at h1
--     by_cases hx : x = succ' (req_fun' n k i.succ) ∨ x = pred' (req_fun' n k i.succ)
--     · refine' ⟨req_fun' n k j.succ, y, _, _⟩
--       · sorry -- easy to prove
--       · sorry
--     · sorry

/-- Constructing a game where only the first point is given, and the others are chosen randomly. -/
noncomputable
def construct_game' (k : Fin (n + 1)) : game' n :=
⟨λ j => req_fun' n k j,
  λ i h1 h2 h3 => by
    simp only
    match i with
    | ⟨0, _⟩ => simp only [Nat.reduceSucc, lt_self_iff_false] at *
    | ⟨i + 1, hi⟩ =>
      apply Finset.mem_of_subset _ (req_fun'_spec n k hi)
      rw [req13],
  λ i h1 => by
    apply bdry_compl_Nonempty _ _
    simp only [ne_eq, Finset.image_nonempty, Finset.nonempty_Iic, and_true]
    intro h
    have hcard : (Finset.image (fun j ↦ req_fun' n k j) (Finset.Iic i)).card = (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [h]
    simp only [Finset.card_fin] at hcard
    have h2 := @Finset.card_image_le _ _ (Finset.Iic i) (λ (j : Fin (n + 1)) ↦ req_fun' n k j) _
    rw [hcard, Fin.card_Iic] at h2
    have : (n + 1) < (n + 1) := lt_of_le_of_lt h2 h1
    simp at *,
  λ i h1 h2 h3 => by
    match i with
    | ⟨0, _⟩ => simp only [lt_self_iff_false] at h3
    | ⟨i + 1, hi⟩ =>
      simp only
      rw [req_fun'_succ_even n hi _]
      --simp only [req_fun'_succ n]
      congr
      rw [req13]
      rw [Nat.even_iff, ← Nat.succ_mod_two_eq_one_iff, ← Nat.odd_iff]
      apply h2 ⟩

-- lemma req12 {i : ℕ} (hi : i + 1 < n) (heven : Even i) : ∀ x ∈ bdry (Finset.image (fun j ↦ req_fun' n k j) (Finset.Iic ({ val := i + 1, isLt := hi } - 1))ᶜ), x.val % 2 = (k.val  + 1) % 2 := by
--   intro x hx
--   sorry

/-lemma req15 (k : ℕ) (hn : n ≠ 1) {i : ℕ} (hi : i + 1 < n) (hs : succ' (req_fun' n k i.succ) ∈ S n k i) (hp : pred' (req_fun' n k i.succ) ∈ S n k i) (h : req_fun' n k i.succ ∈ (S n k i)ᶜ) : False := by
  have : succ' (req_fun' n k i.succ) ∈ bdry (S n k i) ∧ pred' (req_fun' n k i.succ) ∈ bdry (S n k i) := sorry -- easy to prove
  by_cases mem_zero : 0 ∈ (S n k i)ᶜ
  · rw [S_eq_Icc_of_zero_in_compl n k hn _ hi mem_zero, bdry_Icc] at this
    have h2 : pred' (req_fun' n k i.succ) ≤ succ' (req_fun' n k i.succ) := by
      apply le_trans (pred'_le_self _ _ _) _
      rw [succ'_eq_add_one, pred'_eq_add_one]

    sorry
  · sorry-/

lemma pred'_le_succ' {x : Fin (n + 1)} (h : x ≠ 0 ∧ x ≠ Fin.last n) : pred' x ≤ succ' x := le_trans (pred'_le_self _ _ (Fin.pos_of_ne_zero h.1)) (self_le_succ' _ _ h.2)

lemma succ'_le_pred' {x : Fin (n + 1)} (h : succ' x ≤ pred' x) : x = 0 ∨ x = Fin.last n := by
  by_cases h1x : x = 0
  · left
    assumption
  · by_cases h2x : x = Fin.last n
    · right
      assumption
    · by_cases hn : n = 1
      · subst n
        revert x
        rw [Fin.forall_fin_two]
        simp only [Fin.isValue, succ'_eq_add_one, zero_add, not_true_eq_false, Fin.ext_iff,
          Fin.val_zero, Fin.val_last, zero_ne_one, not_false_eq_true, or_false, forall_true_left,
          IsEmpty.forall_iff, implies_true, CharTwo.add_self_eq_zero, Fin.zero_le, one_ne_zero,
          Fin.val_one, or_true, and_self]
      have hps := pred'_le_succ' _ ⟨h1x, h2x⟩
      have ht := le_antisymm h hps
      exfalso
      apply pred'_ne_succ' _ x hn ht.symm

lemma Fin.Icc_compl {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ last n) : (Finset.Icc a b)ᶜ = (Finset.Icc 0 (pred' a)) ∪ (Finset.Icc (succ' b) (Fin.last n)) := by
  ext x
  simp only [Finset.mem_compl, Finset.mem_Icc, not_and, not_le, Finset.mem_union, zero_le, true_and]
  refine' ⟨λ h => _, λ h => λ h' => _⟩
  · by_cases hx : x < a
    · left
      rw [pred'_eq_add_one]
      apply Fin.le_sub_one_of_lt _ _ hx
      intro h
      rw [h] at hx
      simp only [not_lt_zero] at hx
    · rw [not_lt] at hx
      specialize h hx
      right
      rw [succ'_eq_add_one]
      simp only [le_last, and_true]
      apply Fin.add_one_le_of_lt h
  · simp only [pred'_eq_add_one, succ'_eq_add_one, le_last, and_true] at h
    cases' h with h h
    · exfalso
      apply ha
      rw [← Fin.le_sub_one_iff]
      apply le_trans h' h
    · apply Fin.lt_of_le_add_one _ hb h

lemma S_card (k : ℕ) {i : ℕ} (hi : i + 1 < n + 1) : (S n k i).card ≤ n + 1 := by
  rw [S_card_eq _ _ hi]
  apply le_of_lt hi

-- move up
lemma mem_of_mem_bdry {T : Finset (Fin n)} {x : Fin n} (hx : x ∈ bdry T) : x ∈ T := by
  rw [bdry] at hx
  simp only [Finset.mem_sdiff] at hx
  apply hx.1

lemma req_fun'_bdry (hn : n ≠ 1) (k : ℕ) {i : ℕ} (hi : i + 1 < (n + 1)) : req_fun' n k i ∈ bdry (S n k i) := by
  -- make separate lemma
  have h_add_one_ne_one : n + 1 ≠ 1 := by
    simp only [ne_eq, add_left_eq_self]
    apply NeZero.ne _
  by_contra h
  rw [bdry] at h
  simp only [Finset.mem_sdiff, not_and, not_not] at h
  have h_mem : req_fun' n k i ∈ S n k i := by
    rw [S]
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and]
    refine' ⟨i, _⟩
    congr
    simp only [Fin.cast_nat_eq_last, Fin.val_last]
  specialize h h_mem
  rw [int'] at h
  simp only [nbrs, Set.mem_setOf_eq, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ,
    true_and] at h
  by_cases h_one : i = 0
  · -- because req_fun' is in the interior
    have h1 : (S n k i).card ≥ 3 := by
      have h2 : {succ' (req_fun' n ↑k ↑i), pred' (req_fun' n ↑k ↑i), req_fun' n ↑k ↑i} ⊆ S n (↑k) i := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        cases' hx with hx hx
        · rw [hx]
          apply h
          simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
        · cases' hx with hx hx
          · rw [hx]
            apply h
            simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
          · rw [hx]
            apply h_mem
      --have h3 : (({succ' (req_fun' n ↑k ↑i), pred' (req_fun' n ↑k ↑i)}) : Finset (Fin (n + 1))).card = 2 := by
      have h3 : (({succ' (req_fun' n ↑k ↑i), pred' (req_fun' n ↑k ↑i), req_fun' n ↑k ↑i}) : Finset (Fin (n + 1))).card = 3 := by
        rw [Finset.card_eq_three]--, Finset.card_union, Finset.card_singleton]
        refine' ⟨succ' (req_fun' n ↑k ↑i), pred' (req_fun' n ↑k ↑i), req_fun' n ↑k ↑i, (pred'_ne_succ' _ _ hn).symm, succ'_ne_self _ _, pred'_ne_self _ _, rfl⟩
      rw [← h3]
      apply Finset.card_le_card h2
    -- because i < 1
    have h2 : (S n k i).card ≤ 1 := by
      rw [S_card_eq _ _ hi]
      simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero, h_one]
    exfalso
    rw [← not_lt] at h2
    apply h2 (lt_of_lt_of_le _ h1)
    norm_num
  by_cases hn : n = 1 -- this comes from pred'_ne_succ'
  · rw [hn, Nat.add_lt_add_iff_right] at hi
    simp only [Nat.lt_one_iff] at hi
    apply h_one hi
  simp only [not_le] at h_one
  have hi' : (i - 1) + 1 < n + 1 := by
    apply lt_trans _ hi
    simp only [add_lt_add_iff_right, Nat.sub_one_lt_of_le (Nat.pos_of_ne_zero h_one) le_rfl]
  have h_succ : i = (i - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.succ_le.2 (Nat.pos_of_ne_zero h_one))]
  have succ_mem : {succ' (req_fun' n ↑k ↑i), pred' (req_fun' n ↑k ↑i)} ⊆ S n (↑k) (i - 1) := by
    have h2 : S n k (i - 1) = S n k i \ {req_fun' n k i} := by
      rw [h_succ] at hi
      conv_rhs =>
        { congr
          rw [h_succ, S_eq _ _ hi, Nat.succ_eq_add_one, ← h_succ] }
      symm
      rw [Finset.union_sdiff_left, Finset.sdiff_eq_self, Finset.subset_empty]
      refine' Finset.inter_singleton_of_not_mem (λ h => _)
      have h2 := req_fun'_spec n k hi'
      rw [bdry, Finset.mem_sdiff, Finset.mem_compl] at h2
      apply h2.1
      rw [S] at h
      convert h
      rw [← h_succ]
      rw [← h_succ] at hi'
      simp only [Fin.val_nat_cast, Nat.mod_eq_of_lt hi']
    rw [h2, Finset.subset_sdiff]
    refine' ⟨h, _⟩
    simp only [succ'_eq_add_one, pred'_eq_add_one, Finset.disjoint_singleton_right, Finset.mem_insert, self_eq_add_right,
      Fin.one_eq_zero_iff, add_left_eq_self, Finset.mem_singleton]
    intro h
    cases' h with h h
    · apply NeZero.ne n h
    · have := add_eq_of_eq_sub h
      simp only [add_right_eq_self, Fin.one_eq_zero_iff, add_left_eq_self] at this
      apply NeZero.ne n this
  have hi'' : ((i - 1 : ℕ) : Fin (n + 1)) + 1 = i := by
    rw [Nat.cast_sub (Nat.pos_of_ne_zero h_one)]
    simp only [Nat.reduceSucc, Nat.cast_one, sub_add_cancel]
  by_cases hzero : 0 ∈ (S n k (i - 1))
  · have hS_compl := S_compl_eq_Icc_of_zero_in_self n k _ hi' hzero
    have hmin : 0 < Finset.min' (S n k (i - 1))ᶜ (S_compl_nonempty _ _ hi') := min'_pos_of_zero_mem_compl _ _ (by rwa [compl_compl])
    have min_le_max : Finset.min' (S n k (i - 1))ᶜ (S_compl_nonempty _ _ hi') ≤ Finset.max' (S n k (i - 1))ᶜ (S_compl_nonempty _ _ hi') := min'_le_max' _ _
    have rf_bdry := mem_of_mem_bdry _ (req_fun'_spec' n k hi')
    have hreq : req_fun' n k i ≠ 0 := by
      intro heq
      rw [Finset.mem_compl] at rf_bdry
      apply rf_bdry
      rw [Nat.cast_sub (Nat.pos_of_ne_zero h_one)]
      simp only [Nat.reduceSucc, Nat.cast_one, sub_add_cancel, heq, hzero]
    have hS_compl_eq : (S n k (i - 1))ᶜ = {req_fun' n k i} := by
      rw [hi''] at rf_bdry
      rw [hS_compl, Finset.Icc_eq_singleton_iff, le_antisymm_iff, le_antisymm_iff]
      refine' ⟨⟨Finset.min'_le _ _ rf_bdry, _⟩, _, Finset.le_max' _ _ rf_bdry⟩
      · by_contra h_contra
        rw [not_le] at h_contra
        have h_contra := Fin.le_sub_one_of_lt n hreq h_contra
        rw [← pred'_eq_add_one] at h_contra
        have hpred : pred' (req_fun' n k i) ∈ (S n k (i - 1))ᶜ := by
          rw [hS_compl, Finset.mem_Icc]
          rw [hS_compl, Finset.mem_Icc] at rf_bdry
          refine' ⟨h_contra, le_trans (pred'_le_self _ (req_fun' n k i) (Fin.pos_of_ne_zero hreq)) rf_bdry.2⟩
        rw [Finset.mem_compl] at hpred
        apply hpred (succ_mem _)
        simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
      · by_contra h_contra
        rw [not_le] at h_contra
        have h_contra1 := Fin.add_one_le_of_lt h_contra
        rw [← succ'_eq_add_one] at h_contra1
        have hpred : succ' (req_fun' n k i) ∈ (S n k (i - 1))ᶜ := by
          rw [hS_compl, Finset.mem_Icc]
          rw [hS_compl, Finset.mem_Icc] at rf_bdry
          refine' ⟨le_trans rf_bdry.1 (self_le_succ' _ (req_fun' n k i) _), h_contra1⟩
          intro h
          rw [h, ← not_le] at h_contra
          apply h_contra (Fin.le_last _)
        rw [Finset.mem_compl] at hpred
        apply hpred (succ_mem _)
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    have hS_card := Finset.card_compl (S n k (i - 1))
    rw [hS_compl_eq] at hS_card
    simp only [Finset.card_singleton, Fintype.card_fin] at hS_card
    have hS_card : (S n (↑k) (i - 1)).card = (n + 1) - 1 := by
      have hS_card := (hS_card.symm)
      rw [Nat.sub_eq_iff_eq_add' (S_card _ _ hi')] at hS_card
      symm
      rw [Nat.sub_eq_iff_eq_add _, ← hS_card]
      simp only [le_add_iff_nonneg_left, zero_le]
    have hS_card_le := S_card_le n k (i - 1)
    rw [hS_card] at hS_card_le
    -- using hi'
    have hi_eq_n : i = n := by
      rw [← h_succ, Nat.lt_succ] at hi'
      rw [← h_succ, Nat.add_sub_cancel] at hS_card_le
      apply le_antisymm hi' hS_card_le
    rw [hi_eq_n] at hi
    simp only [lt_self_iff_false] at hi
  · have hS := S_eq_Icc_of_zero_in_compl n k _ hi' (Finset.mem_compl.2 hzero)
    have rf_bdry := mem_of_mem_bdry _ (req_fun'_spec' n k hi')
    have hsucc : succ' (req_fun' n k i) ∈ bdry (S n k (i - 1)) := by
      rw [mem_bdry]
      refine' ⟨_, _⟩
      · apply succ_mem
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
      · right
        rw [succ'_eq_add_one, pred'_eq_add_one, add_sub_cancel]
        conv => {
          congr
          rw [h_succ, Nat.cast_add, Nat.cast_one] }
        apply rf_bdry
    have hpred : pred' (req_fun' n k i) ∈ bdry (S n k (i - 1)) := by
      -- almost same proof as previous one
      rw [mem_bdry]
      refine' ⟨_, _⟩
      · apply succ_mem
        simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
      · left
        rw [succ'_eq_add_one, pred'_eq_add_one, sub_add_cancel]
        conv => {
          congr
          rw [h_succ, Nat.cast_add, Nat.cast_one] }
        apply rf_bdry
    have hmin : 0 < Finset.min' (S n k (i - 1)) (S_nonempty _ _ _) := min'_pos_of_zero_mem_compl _ _ (Finset.mem_compl.2 hzero)
    have min_le_max : Finset.min' (S n k (i - 1)) (S_nonempty _ _ _) ≤ Finset.max' (S n k (i - 1)) (S_nonempty _ _ _) := min'_le_max' _ _
    rw [hS, bdry_Icc _ _ _ hmin min_le_max] at hsucc
    rw [hS, bdry_Icc _ _ _ hmin min_le_max] at hpred
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsucc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpred
    cases' hsucc with hsucc hsucc
    · cases' hpred with hpred hpred
      · rw [← hpred] at hsucc
        apply pred'_ne_succ' _ (req_fun' n ↑k ↑i) hn hsucc.symm
      · rw [← hsucc, ← hpred] at min_le_max
        have hx := succ'_le_pred' _ min_le_max
        cases' hx with hx hx
        · rw [hx] at hsucc
          rw [hx] at hpred
          rw [← hsucc, ← hpred, succ'_eq_add_one, pred'_eq_add_one] at hS
          simp only [zero_add, zero_sub] at hS
          have hS_card_le := S_card_le n k (i - 1)
          rw [hS] at hS_card_le
          simp only [Fin.card_Icc, Fin.coe_neg_one, Fin.val_one', tsub_le_iff_right] at hS_card_le
          rw [← h_succ, Nat.one_mod_of_ne_one h_add_one_ne_one, ← not_lt] at hS_card_le
          apply hS_card_le hi
        · rw [hx] at hsucc
          rw [hx] at hpred
          rw [← hsucc, ← hpred, succ'_eq_add_one, pred'_eq_add_one, Fin.last_add_one] at hS
          --simp? at hS
          have hS_card_le := S_card_le n k (i - 1)
          rw [hS] at hS_card_le
          simp only [Fin.card_Icc, Fin.coe_neg_one, Fin.val_one', tsub_le_iff_right] at hS_card_le
          rw [← h_succ, Fin.coe_sub] at hS_card_le
          simp only [Fin.val_last, Fin.val_one', Fin.val_zero, add_zero] at hS_card_le
          rw [Nat.one_mod_of_ne_one h_add_one_ne_one] at hS_card_le
          · rw [← Nat.add_sub_assoc] at hS_card_le
            · rw [add_comm n (n + 1), Nat.add_sub_assoc (Nat.one_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne _))), Nat.add_mod_left (n + 1), Nat.mod_eq_of_lt (Nat.sub_one_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.le_succ _)), Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne _))), ← not_lt] at hS_card_le
              apply hS_card_le
              apply Nat.add_lt_add_iff_right.1 hi
            · simp only [le_add_iff_nonneg_left, zero_le]
    · cases' hpred with hpred hpred
      · have hmem_S : req_fun' n k i ∈ S n k (i - 1) := by
          rw [hS, ← hpred, ← hsucc]
          simp only [Finset.mem_Icc]
          refine' ⟨pred'_le_self _ (req_fun' n k i) _, self_le_succ' _ (req_fun' n k i) _⟩
          · apply Fin.pos_of_ne_zero
            intro h1
            rw [h1] at hpred
            rw [h1] at hsucc
            rw [← hsucc, ← hpred, succ'_eq_add_one, pred'_eq_add_one] at min_le_max
            simp only [zero_sub, zero_add] at min_le_max
            rw [← Fin.last_eq_neg_one, Fin.last_le_iff, Fin.ext_iff] at min_le_max
            simp only [Fin.val_one', Fin.val_last] at min_le_max
            rw [Nat.one_mod_of_ne_one h_add_one_ne_one] at min_le_max
            apply hn min_le_max.symm
          · intro h1
            rw [h1] at hpred
            rw [h1] at hsucc
            rw [← hsucc, ← hpred, succ'_eq_add_one, pred'_eq_add_one, Fin.last_add_one] at hS
            have he : S n k (i - 1) = ∅ := by
              rw [hS, Finset.Icc_eq_empty_iff]
              intro h2
              rw [Fin.le_zero_iff, sub_eq_zero, Fin.ext_iff, Fin.val_one', Fin.val_last, Nat.one_mod_of_ne_one h_add_one_ne_one] at h2
              apply hn h2
            rw [Finset.eq_empty_iff_forall_not_mem] at he
            specialize he (succ' (req_fun' n ↑k ↑i))
            apply he (succ_mem _)
            simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
        have rf_bdry := mem_of_mem_bdry _ (req_fun'_spec' n k hi')
        rw [hi''] at rf_bdry
        apply Finset.mem_compl.1 rf_bdry hmem_S
      · rw [← hpred] at hsucc
        apply pred'_ne_succ' _ (req_fun' n k i) hn hsucc.symm

example {T : Finset (Fin n)} : Tᶜᶜ = T := by simp only [compl_compl]

--example (a b : ℕ) (h : a + 1 = b + 1) : a = b := by simp only [add_left_inj] at h

/-example (a b : Fin (n + 1)) : (a - b).val = a.val - b.val := by
  rw [Fin.sub_def]
  simp only
  rw [Nat.add_mod, Nat.mod_eq_of_lt (Fin.is_lt _)]
  symm
  rw[Nat.sub_eq_iff_eq_add _] -/

lemma sub_one_mod_two (hn : Odd n) (x : Fin (n + 1)) : (x - 1).val % 2 = (x + 1) % 2 := by
  have h_add_one_ne_one : n + 1 ≠ 1 := by
    simp only [ne_eq, add_left_eq_self]
    apply NeZero.ne _
  have hn' : Even (n + 1) := by rwa [Nat.even_iff, Nat.succ_mod_two_eq_zero_iff, ← Nat.odd_iff]
  rw [Fin.sub_def]
  simp only [Fin.val_one']--, Nat.succ_eq_add_one, ← add_assoc, Nat.add_mod, ← h d (Nat.lt_succ.2 le_rfl) hd', ← add_left_inj (1 % 2), ← Nat.add_mod, ← Nat.add_mod, Fin.val_sub, Nat.add_mod, Nat.mod_eq_of_lt (Fin.is_lt _)]--, Fin.val_one' (n + 1), Nat.one_mod_of_ne_one _, Nat.one_mod_of_ne_one _, h d (Nat.lt_succ _) hd']
  rw [Nat.mod_mod_of_dvd _ ((Nat.dvd_iff_mod_eq_zero _ _).2 (Nat.even_iff.1 hn')), Nat.add_mod, Nat.one_mod_of_ne_one h_add_one_ne_one, Nat.add_sub_cancel, Nat.odd_iff.1 hn]
  conv_rhs => { rw [Nat.add_mod] }

lemma req_fun'_parity_of_zero_mem_S (hn : Odd n) (ne_one : n ≠ 1) (k : ℕ) {d : ℕ} (hi : d.succ + 1 < (n + 1)) (h : ∀ m < Nat.succ d, m + 1 < n + 1 → ↑(req_fun' n ↑k ↑m) % 2 = (k + m) % 2) (hzero : 0 ∈ S n k d) : (req_fun' n k (d + 1)).val % 2 = (k + d.succ) % 2 := by
  have h_add_one_ne_one : n + 1 ≠ 1 := by
    simp only [ne_eq, add_left_eq_self]
    apply NeZero.ne _
  have hn' : Even (n + 1) := by rwa [Nat.even_iff, Nat.succ_mod_two_eq_zero_iff, ← Nat.odd_iff]
  have succ_d_cast : ((d + 1 : ℕ) : Fin (n + 1)) = d + 1 := by simp only [Nat.cast_add,
          Nat.cast_one]
  have hd' : Nat.succ d < n + 1 := lt_trans (Nat.lt_succ.2 (le_refl _)) hi
  rw [Nat.succ_eq_add_one, ← add_assoc, Nat.add_mod, ← h d (Nat.lt_succ.2 le_rfl) hd', ← Nat.add_mod]
  have hS_compl := S_compl_eq_Icc_of_zero_in_self n k _ hd' hzero
  have hmin : 0 < Finset.min' (S n k d)ᶜ (S_compl_nonempty _ _ hd') := min'_pos_of_zero_mem_compl _ _ (by rwa [compl_compl])
  have min_le_max : Finset.min' (S n k d)ᶜ (S_compl_nonempty _ _ hd') ≤ Finset.max' (S n k d)ᶜ (S_compl_nonempty _ _ hd') := min'_le_max' _ _
  have rf_bdry := req_fun'_bdry n ne_one k hd'
  have rf_bdry_compl := req_fun'_spec' n k hd'
  rw [hS_compl, bdry_Icc _ _ _ hmin min_le_max] at rf_bdry_compl
  rw [← compl_compl (S n k d), hS_compl, bdry_Icc_compl _ _ _ hmin min_le_max] at rf_bdry
  simp only [Finset.mem_insert, Finset.mem_singleton] at rf_bdry
  simp only [Finset.mem_insert, Finset.mem_singleton] at rf_bdry_compl
  cases' rf_bdry with rf_bdry rf_bdry
  · cases' rf_bdry_compl with rf_bdry_compl rf_bdry_compl
    · rw [← rf_bdry_compl, ← succ'_eq_iff_eq_pred'] at rf_bdry
      rw [← rf_bdry, succ'_eq_add_one, Fin.val_add, Nat.add_mod, Nat.mod_eq_of_lt (Fin.is_lt _)]
      simp only [Fin.val_one', dvd_refl, Nat.mod_mod_of_dvd, Nat.add_mod_mod]
      rw [Nat.mod_mod_of_dvd _ ((Nat.dvd_iff_mod_eq_zero _ _).2 (Nat.even_iff.1 hn'))]
    · rw [← succ'_eq_iff_eq_pred'] at rf_bdry
      by_cases heven : Even d
      · have hS_card := S_card_eq n k hd'
        have rf_ne_last : req_fun' n k d ≠ Fin.last n := by
          intro heq
          rw [heq, succ'_eq_add_one, Fin.last_add_one] at rf_bdry
          rw [← rf_bdry] at hmin
          simp only [lt_self_iff_false] at hmin
        rw [← compl_compl (S n k d), hS_compl, ← rf_bdry, ← rf_bdry_compl, Finset.card_compl, Fin.card_Icc, succ'_eq_add_one, Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) rf_ne_last), Fintype.card_fin] at hS_card
        simp only [Fintype.card_fin, Nat.succ_sub_succ_eq_sub] at hS_card
        rw [Nat.sub_eq_iff_eq_add (le_trans (Nat.sub_le _ _) (le_of_lt (Fin.is_lt _))), ← Nat.sub_eq_iff_eq_add' (le_of_lt hd')] at hS_card
        have hS_card := hS_card.symm
        rw [Nat.sub_eq_iff_eq_add' _] at hS_card
        · --simp only [Nat.cast_add, Nat.cast_one]
          rw [hS_card, Nat.add_mod, Nat.add_mod _ 1]
          congr 2
          simp only [Nat.succ_sub_succ_eq_sub, Nat.mod_succ]
          rw [← Nat.odd_iff]
          apply Nat.Odd.sub_even (le_of_lt (Nat.succ_lt_succ_iff.1 hd')) hn heven
        · rw [← Fin.le_def]
          apply le_trans (self_le_succ' _ _ rf_ne_last) _
          rw [rf_bdry_compl, rf_bdry]
          apply min_le_max
      · rw [← Nat.odd_iff_not_even] at heven
        rw [← succ_d_cast, req_fun'_succ_odd' n k hd' heven]
        split_ifs
        · rw [pred'_eq_add_one, sub_one_mod_two n hn]
        · rw [succ'_eq_add_one, Fin.val_add, Fin.val_one', Nat.one_mod_of_ne_one h_add_one_ne_one, Nat.mod_mod_of_dvd _ ((Nat.dvd_iff_mod_eq_zero _ _).2 (Nat.even_iff.1 hn'))]
        · next h2 h3 =>
          { rw [Finset.mem_compl] at h2
            rw [Finset.mem_compl] at h3
            push_neg at h2
            push_neg at h3
            exfalso
            have min_mem := Finset.min'_mem _ (S_compl_nonempty _ k hd')
            rw [Finset.mem_compl] at min_mem
            apply min_mem
            rw [← rf_bdry]
            by_cases d_eq_zero : d = 0
            · rw [d_eq_zero] at heven
              simp only [Nat.odd_iff_not_even, even_zero, not_true_eq_false] at heven
            have h4 : (d - 1).succ + 1 < n + 1 := by
              rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero d_eq_zero)]
              apply hd'
            have h6 := Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero d_eq_zero))
            rw [← h6, S_eq _ _ h4]
            apply Finset.mem_union_right
            rw [h6, S, h6]
            apply h3
            have h5 : (d - 1) + 1 < n + 1 := lt_trans (Nat.lt_succ.2 le_rfl) h4
            have  rf_mem_compl := req_fun'_spec' n k h5
            rw [Nat.cast_sub (Nat.one_le_of_lt (Nat.pos_of_ne_zero d_eq_zero)), Nat.cast_one, sub_add_cancel, mem_bdry, compl_compl] at rf_mem_compl
            cases' rf_mem_compl.2 with rf rf
            · exfalso
              -- argument repeated for a second time, maybe make anonther lemma
              apply min_mem
              rw [← rf_bdry]
              rw [← h6, S_eq _ _ h4]
              apply Finset.mem_union_right
              rw [h6]
              apply rf
            · rw [S] at rf
              convert rf
              · rw [h6]
              · rw [h6] }
  · cases' rf_bdry_compl with rf_bdry_compl rf_bdry_compl
    · rw [← pred'_eq_iff_eq_succ'] at rf_bdry
      by_cases heven : Even d
      · have hS_card := S_card_eq n k hd'
        by_cases rf_ne_zero : req_fun' n k d = 0
        · rw [rf_ne_zero, pred'_eq_add_one, zero_sub, ← Fin.last_eq_neg_one _] at rf_bdry
          have hS_card_compl : (S n k d)ᶜ.card = n + 1 - (d + 1) := by
            rw [Finset.card_compl, hS_card]--, hS_compl, Fin.card_Icc]
            simp only [Fintype.card_fin, Nat.succ_sub_succ_eq_sub]
          rw [hS_compl, Fin.card_Icc, ← rf_bdry, ← rf_bdry_compl, Fin.val_last, Nat.sub_eq_iff_eq_add' (le_of_lt (Fin.is_lt _)), ← Nat.sub_eq_iff_eq_add (Nat.sub_le _ _), Nat.sub_sub_self (le_of_lt hd')] at hS_card_compl
          --simp only [Nat.cast_add, Nat.cast_one, Fin.val_zero, zero_add, Nat.mod_succ]
          rw [rf_ne_zero, ← hS_card_compl, Fin.val_zero, zero_add, Nat.mod_succ, Nat.succ_mod_two_eq_one_iff, Nat.even_iff.1 heven]
        have rf_ne_last : req_fun' n k d - 1 ≠ Fin.last n := by
          intro heq
          --have rfb := req_fun'_bdry
          rw [sub_eq_iff_eq_add, Fin.last_add_one] at heq
          apply rf_ne_zero heq
        -- have hS_compl_card : (S n k d)ᶜ.card = n - d := sorry
        -- rw [hS_compl, ← rf_bdry, ← rf_bdry_compl, Fin.card_Icc] at hS_compl_card
        -- rw [hS_compl, Fin.card_Icc, ← rf_bdry, ← rf_bdry_compl, pred'_eq_add_one, Nat.sub_eq_iff_eq_add, ← Nat.sub_eq_iff_eq_add'] at hS_compl_card
        rw [← compl_compl (S n k d), hS_compl, ← rf_bdry, ← rf_bdry_compl, Finset.card_compl, Fin.card_Icc, pred'_eq_add_one, ← Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) rf_ne_last), Fintype.card_fin] at hS_card
        simp only [sub_add_cancel] at hS_card
        --simp only [Fintype.card_fin, Nat.succ_sub_succ_eq_sub] at hS_card
        rw [Nat.sub_eq_iff_eq_add (le_trans (Nat.sub_le _ _) (le_of_lt (Fin.is_lt _))), ← Nat.sub_eq_iff_eq_add' (le_of_lt hd')] at hS_card
        have hS_card := hS_card.symm
        rw [Nat.sub_eq_iff_eq_add' _] at hS_card
        · --simp only [Nat.cast_add, Nat.cast_one]
          rw [hS_card, add_assoc, Nat.add_mod]--, add_assoc] --, Nat.add_mod, Nat.add_mod _ 1]
          conv_lhs => { rw [← add_zero ((req_fun' n (↑k) (↑d + 1))).val] }
          rw [Nat.add_mod]
          congr 2
          simp only [Nat.succ_sub_succ_eq_sub, Nat.mod_succ]
          symm
          rw [Nat.zero_mod, ← Nat.even_iff, Nat.even_add_one, ← Nat.odd_iff_not_even]
          apply Nat.Odd.sub_even (le_of_lt (Nat.succ_lt_succ_iff.1 hd')) hn heven
        · rw [← Fin.le_def]
          apply le_trans _ (pred'_le_self _ _ (Fin.pos_of_ne_zero rf_ne_zero))
          rw [rf_bdry_compl, rf_bdry]
          apply min_le_max
      · rw [← Nat.odd_iff_not_even] at heven
        rw [← succ_d_cast, req_fun'_succ_odd' n k hd' heven]
        split_ifs
        · rw [pred'_eq_add_one, sub_one_mod_two n hn]
        · rw [succ'_eq_add_one, Fin.val_add, Fin.val_one', Nat.one_mod_of_ne_one h_add_one_ne_one, Nat.mod_mod_of_dvd _ ((Nat.dvd_iff_mod_eq_zero _ _).2 (Nat.even_iff.1 hn'))]
        · next h2 h3 =>
          { rw [Finset.mem_compl] at h2
            rw [Finset.mem_compl] at h3
            push_neg at h2
            push_neg at h3
            exfalso

            have max_mem := Finset.max'_mem _ (S_compl_nonempty _ k hd')
            rw [Finset.mem_compl] at max_mem
            apply max_mem

            --have min_mem := Finset.min'_mem _ (S_compl_nonempty _ k hd')
            --rw [Finset.mem_compl] at min_mem
            --apply min_mem

            rw [← rf_bdry]
            by_cases d_eq_zero : d = 0
            · rw [d_eq_zero] at heven
              simp only [Nat.odd_iff_not_even, even_zero, not_true_eq_false] at heven
            have h4 : (d - 1).succ + 1 < n + 1 := by
              rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero d_eq_zero)]
              apply hd'
            have h6 := Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero d_eq_zero))
            rw [← h6, S_eq _ _ h4]
            apply Finset.mem_union_right
            rw [h6, S, h6]
            apply h2
            have h5 : (d - 1) + 1 < n + 1 := lt_trans (Nat.lt_succ.2 le_rfl) h4
            have  rf_mem_compl := req_fun'_spec' n k h5
            rw [Nat.cast_sub (Nat.one_le_of_lt (Nat.pos_of_ne_zero d_eq_zero)), Nat.cast_one, sub_add_cancel, mem_bdry, compl_compl] at rf_mem_compl
            cases' rf_mem_compl.2 with rf rf
            · rw [S] at rf
              convert rf
              · rw [h6]
              · rw [h6]
            · exfalso
              -- argument repeated for a second time, maybe make anonther lemma
              apply max_mem
              rw [← rf_bdry]
              rw [← h6, S_eq _ _ h4]
              apply Finset.mem_union_right
              rw [h6]
              apply rf }
    · -- same as case I above
      rw [← rf_bdry_compl, ← pred'_eq_iff_eq_succ'] at rf_bdry
      rw [← rf_bdry, pred'_eq_add_one, sub_one_mod_two _ hn _]

lemma req_fun'_parity_of_zero_mem_S_compl (hn : Odd n) (ne_one : n ≠ 1) (k : ℕ) {d : ℕ} (hi : d.succ + 1 < (n + 1)) (h : ∀ m < Nat.succ d, m + 1 < n + 1 → ↑(req_fun' n ↑k ↑m) % 2 = (k + m) % 2) (hzero : 0 ∈ (S n k d)ᶜ) : (req_fun' n k (d + 1)).val % 2 = (k + d.succ) % 2 := by
  have h_add_one_ne_one : n + 1 ≠ 1 := by
    simp only [ne_eq, add_left_eq_self]
    apply NeZero.ne _
  have hn' : Even (n + 1) := by rwa [Nat.even_iff, Nat.succ_mod_two_eq_zero_iff, ← Nat.odd_iff]
  have succ_d_cast : ((d + 1 : ℕ) : Fin (n + 1)) = d + 1 := by simp only [Nat.cast_add,
          Nat.cast_one]
  have hd' : Nat.succ d < n + 1 := lt_trans (Nat.lt_succ.2 (le_refl _)) hi
  rw [Nat.succ_eq_add_one, ← add_assoc, Nat.add_mod, ← h d (Nat.lt_succ.2 le_rfl) hd', ← Nat.add_mod]
  have hS_compl := S_eq_Icc_of_zero_in_compl n k _ hd' hzero
  have hmin : 0 < Finset.min' (S n k d) (S_nonempty _ _ _) := min'_pos_of_zero_mem_compl n (S_nonempty _ _ _) hzero
  have min_le_max : Finset.min' (S n k d) (S_nonempty _ _ _) ≤ Finset.max' (S n k d) (S_nonempty _ _ _) := min'_le_max' _ _
  have rf_bdry_compl := req_fun'_bdry n ne_one k hd'
  have rf_bdry := req_fun'_spec' n k hd'
  rw [hS_compl, bdry_Icc _ _ _ hmin min_le_max] at rf_bdry_compl
  rw [hS_compl, bdry_Icc_compl _ _ _ hmin min_le_max] at rf_bdry
  simp only [Finset.mem_insert, Finset.mem_singleton] at rf_bdry
  simp only [Finset.mem_insert, Finset.mem_singleton] at rf_bdry_compl
  cases' rf_bdry with rf_bdry rf_bdry
  · cases' rf_bdry_compl with rf_bdry_compl rf_bdry_compl
    · have rf_ne_last : req_fun' n k (d + 1) ≠ Fin.last n := by
          intro heq
          rw [heq, ← succ'_eq_iff_eq_pred', succ'_eq_add_one, Fin.last_add_one] at rf_bdry
          rw [← rf_bdry] at hmin
          simp only [lt_self_iff_false] at hmin
      rw [← rf_bdry_compl, ← succ'_eq_iff_eq_pred'] at rf_bdry
      rw [← rf_bdry, succ'_eq_add_one, Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) rf_ne_last), add_assoc]-- Nat.add_mod, Nat.mod_eq_of_lt (Fin.is_lt _)]
      simp only [Nat.reduceAdd, Nat.add_mod_right]
    · rw [← succ'_eq_iff_eq_pred'] at rf_bdry
      by_cases heven : Even d
      · have hS_card := S_card_eq n k hd'
        have hS_card_compl : (S n k d)ᶜ.card = n + 1 - (d + 1) := by
            rw [Finset.card_compl, hS_card]--, hS_compl, Fin.card_Icc]
            simp only [Fintype.card_fin, Nat.succ_sub_succ_eq_sub]
        have rf_ne_last : req_fun' n k (d + 1) ≠ Fin.last n := by
          intro heq
          rw [heq, succ'_eq_add_one, Fin.last_add_one] at rf_bdry
          rw [← rf_bdry] at hmin
          simp only [lt_self_iff_false] at hmin
        rw [hS_compl, ← rf_bdry, ← rf_bdry_compl, Fin.card_Icc, succ'_eq_add_one, Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) rf_ne_last)] at hS_card--, Fintype.card_fin] at hS_card
        simp only [Fintype.card_fin, Nat.succ_sub_succ_eq_sub] at hS_card
        rw [Nat.sub_eq_iff_eq_add' (le_trans (self_le_succ' _ _ rf_ne_last) _)] at hS_card--, ← Nat.sub_eq_iff_eq_add' (le_of_lt hd')] at hS_card
        · rw [hS_card, add_assoc, add_assoc, Nat.add_mod]--, Nat.add_mod _ 1]
          simp only [Nat.reduceAdd, Nat.add_mod_right, Nat.add_mod_mod, Nat.mod_add_mod]
          rw [Nat.add_mod, Nat.even_iff.1 heven]
          simp only [add_zero, dvd_refl, Nat.mod_mod_of_dvd]
        · rw [← Fin.le_def]
          rw [rf_bdry_compl, rf_bdry]
          apply min_le_max
      · rw [← Nat.odd_iff_not_even] at heven
        rw [← succ_d_cast, req_fun'_succ_odd' n k hd' heven]
        split_ifs
        · rw [pred'_eq_add_one, sub_one_mod_two n hn]
        · rw [succ'_eq_add_one, Fin.val_add, Fin.val_one', Nat.one_mod_of_ne_one h_add_one_ne_one, Nat.mod_mod_of_dvd _ ((Nat.dvd_iff_mod_eq_zero _ _).2 (Nat.even_iff.1 hn'))]
        · next h2 h3 =>
          { rw [Finset.mem_compl] at h2
            rw [Finset.mem_compl] at h3
            push_neg at h2
            push_neg at h3
            exfalso
            have rf_nz : req_fun' n k d ≠ 0 := by
              intro heq
              rw [Finset.mem_compl] at hzero
              apply hzero
              rw [heq] at rf_bdry_compl
              rw [rf_bdry_compl]
              apply Finset.max'_mem
            have hpred : (pred' (req_fun' n ↑k ↑d)) ∈ S n k d := by
              rw [hS_compl, Finset.mem_Icc, ← rf_bdry_compl]
              refine' ⟨_, pred'_le_self _ (req_fun' n k d) (Fin.pos_of_ne_zero rf_nz)⟩
              rw [pred'_eq_add_one, Fin.lt_sub_iff_le_sub_one _ rf_nz, rf_bdry_compl] -- ← Nat.sub_pos_iff_lt, Nat.le_sub_iff_add_le _]
              apply Finset.min'_lt_max'_of_card
              rw [S_card_eq _ _ hd'] --, hS_compl, Fin.card_Icc]
              simp only [lt_add_iff_pos_left]
              apply Nat.pos_of_ne_zero _
              intro heq
              rw [heq] at heven
              simp only [Nat.odd_iff_not_even, even_zero, not_true_eq_false] at heven
            by_cases d_eq_zero : d = 0
            · rw [d_eq_zero] at heven
              simp only [Nat.odd_iff_not_even, even_zero, not_true_eq_false] at heven
            have h4 : (d - 1).succ + 1 < n + 1 := by
              rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero d_eq_zero)]
              apply hd'
            have h5 : (d - 1) + 1 < n + 1 := lt_trans (Nat.lt_succ.2 le_rfl) h4
            have h6 := Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero d_eq_zero))
            have h7 : ((d - 1 : ℕ) : Fin (n + 1)) + 1 = d := by
              rw [Nat.cast_sub (Nat.pos_of_ne_zero d_eq_zero)]
              simp only [Nat.reduceSucc, Nat.cast_one, sub_add_cancel]
            rw [← h6, S_eq _ _ h4, Finset.mem_union] at hpred
            cases' hpred with hpred hpred
            · rw [pred'_eq_add_one] at hpred
              simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, Finset.mem_singleton, sub_eq_self,
              Fin.one_eq_zero_iff, add_left_eq_self] at hpred
              apply NeZero.ne n hpred
            · rw [S, h6] at hpred
              specialize h3 hpred
              have rf_mem_compl := (mem_bdry _ _ _).1 (req_fun'_bdry n ne_one k hd')
              rw [Finset.mem_compl, Finset.mem_compl] at rf_mem_compl
              cases' rf_mem_compl.2 with rf rf
              · apply rf
                rw [← h6, S_eq _ _ h4]
                apply Finset.mem_union_right
                rw [S, h6]
                apply h3
              · apply rf
                rw [← h6, S_eq _ _ h4]
                apply Finset.mem_union_right
                rw [S, h6]
                apply hpred }
  · cases' rf_bdry_compl with rf_bdry_compl rf_bdry_compl
    · rw [← pred'_eq_iff_eq_succ'] at rf_bdry
      by_cases heven : Even d
      · have hS_card := S_card_eq n k hd'
        by_cases rf_ne_zero : req_fun' n k (d + 1) = 0
        · rw [rf_ne_zero, pred'_eq_add_one, zero_sub, ← Fin.last_eq_neg_one _] at rf_bdry
          have hS_card_compl : (S n k d)ᶜ.card = n + 1 - (d + 1) := by
            rw [Finset.card_compl, hS_card]--, hS_compl, Fin.card_Icc]
            simp only [Fintype.card_fin, Nat.succ_sub_succ_eq_sub]
          rw [hS_compl, Fin.card_Icc, ← rf_bdry, ← rf_bdry_compl, Fin.val_last, Nat.sub_eq_iff_eq_add' (le_of_lt (Fin.is_lt _)), ← Nat.sub_eq_iff_eq_add (le_of_lt hd')] at hS_card
          simp only [Nat.succ_sub_succ_eq_sub] at hS_card
          rw [rf_ne_zero, ← hS_card, Fin.val_zero, Nat.zero_mod]--, Nat.mod_succ, Nat.succ_mod_two_eq_one_iff, Nat.even_iff.1 heven]
          symm
          rw [Nat.succ_mod_two_eq_zero_iff, ← Nat.odd_iff]
          apply Nat.Odd.sub_even (le_of_lt (Nat.succ_lt_succ_iff.1 hd')) hn heven
        have rf_ne_last : req_fun' n k (d + 1) - 1 ≠ Fin.last n := by
          intro heq
          rw [sub_eq_iff_eq_add, Fin.last_add_one] at heq
          apply rf_ne_zero heq
        rw [hS_compl, ← rf_bdry, ← rf_bdry_compl, Fin.card_Icc, pred'_eq_add_one, ← Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) rf_ne_last)] at hS_card
        simp only [sub_add_cancel] at hS_card
        rw [Nat.sub_eq_iff_eq_add' (le_trans _ (pred'_le_self _ _ (Fin.pos_of_ne_zero rf_ne_zero))), add_comm d 1, ← add_assoc] at hS_card
        · rw [hS_card, Nat.add_mod, Nat.even_iff.1 heven]--, add_assoc] --, Nat.add_mod, Nat.add_mod _ 1]
          simp only [add_zero, dvd_refl, Nat.mod_mod_of_dvd]
        · rw [← Fin.le_def]
          rw [rf_bdry_compl, rf_bdry]
          apply min_le_max
      · rw [← Nat.odd_iff_not_even] at heven
        rw [← succ_d_cast, req_fun'_succ_odd' n k hd' heven]
        split_ifs
        · rw [pred'_eq_add_one, sub_one_mod_two n hn]
        · rw [succ'_eq_add_one, Fin.val_add, Fin.val_one', Nat.one_mod_of_ne_one h_add_one_ne_one, Nat.mod_mod_of_dvd _ ((Nat.dvd_iff_mod_eq_zero _ _).2 (Nat.even_iff.1 hn'))]
        · next h2 h3 =>
          { -- can make this a separate lemma ; same steps but will make this proof shorter
            rw [Finset.mem_compl] at h2
            rw [Finset.mem_compl] at h3
            push_neg at h2
            push_neg at h3
            have rf_nz : req_fun' n k d ≠ Fin.last n := by
              intro heq
              rw [heq] at rf_bdry_compl
              rw [← rf_bdry_compl, Fin.last_le_iff] at min_le_max
              have hS_card := S_card_eq n k hd'
              rw [hS_compl, Fin.card_Icc, min_le_max, ← rf_bdry_compl] at hS_card
              simp only [Fin.val_last, add_tsub_cancel_left, self_eq_add_left] at hS_card
              rw [hS_card] at heven
              simp only [Nat.odd_iff_not_even, even_zero, not_true_eq_false] at heven
            have hpred : (succ' (req_fun' n ↑k ↑d)) ∈ S n k d := by
              rw [hS_compl, Finset.mem_Icc, ← rf_bdry_compl]
              refine' ⟨self_le_succ' _ (req_fun' n k d) rf_nz, _⟩
              rw [succ'_eq_add_one, Fin.lt_iff_le_add_one _ rf_nz, rf_bdry_compl] -- ← Nat.sub_pos_iff_lt, Nat.le_sub_iff_add_le _]
              apply Finset.min'_lt_max'_of_card
              rw [S_card_eq _ _ hd'] --, hS_compl, Fin.card_Icc]
              simp only [lt_add_iff_pos_left]
              apply Nat.pos_of_ne_zero _
              intro heq
              rw [heq] at heven
              simp only [Nat.odd_iff_not_even, even_zero, not_true_eq_false] at heven
            exfalso
            by_cases d_eq_zero : d = 0
            · rw [d_eq_zero] at heven
              simp only [Nat.odd_iff_not_even, even_zero, not_true_eq_false] at heven
            have h4 : (d - 1).succ + 1 < n + 1 := by
              rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero d_eq_zero)]
              apply hd'
            have h5 : (d - 1) + 1 < n + 1 := lt_trans (Nat.lt_succ.2 le_rfl) h4
            have h6 := Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero d_eq_zero))
            have h7 : ((d - 1 : ℕ) : Fin (n + 1)) + 1 = d := by
              rw [Nat.cast_sub (Nat.pos_of_ne_zero d_eq_zero)]
              simp only [Nat.reduceSucc, Nat.cast_one, sub_add_cancel]
            rw [← h6, S_eq _ _ h4, Finset.mem_union] at hpred
            cases' hpred with hpred hpred
            · rw [succ'_eq_add_one, Nat.succ_eq_add_one, h6] at hpred
              simp only [Finset.mem_singleton, add_right_eq_self, Fin.one_eq_zero_iff,
                add_left_eq_self] at hpred
              apply NeZero.ne n hpred
            · rw [S, h6] at hpred
              specialize h2 hpred
              have rf_mem_compl := (mem_bdry _ _ _).1 (req_fun'_bdry n ne_one k hd')
              rw [Finset.mem_compl, Finset.mem_compl] at rf_mem_compl
              cases' rf_mem_compl.2 with rf rf
              · apply rf
                rw [← h6, S_eq _ _ h4]
                apply Finset.mem_union_right
                rw [S, h6]
                apply hpred
              · apply rf
                rw [← h6, S_eq _ _ h4]
                apply Finset.mem_union_right
                rw [S, h6]
                apply h2 }
    · -- same as case I above
      rw [← rf_bdry_compl, ← pred'_eq_iff_eq_succ'] at rf_bdry
      rw [← rf_bdry, pred'_eq_add_one, Nat.add_mod, sub_one_mod_two _ hn _]
      simp only [Nat.mod_succ, Nat.mod_add_mod]
      rw [add_assoc]
      simp only [Nat.reduceAdd, Nat.add_mod_right]

lemma req_fun'_parity (hn : Odd n) (ne_one : n ≠ 1) (k : ℕ) {i : ℕ} (hi : i + 1 < (n + 1)) : (req_fun' n k i).val % 2 = (k + i) % 2 := by
  revert hi
  apply Nat.strongInductionOn i
  intro d h hd
  induction d with
  | zero =>
      simp only [Nat.zero_eq, Nat.cast_zero, add_zero]
      rw [req_fun'_zero]
      simp only [Fin.val_nat_cast]
      rw [Nat.mod_mod_of_dvd]
      rwa [Nat.dvd_iff_mod_eq_zero, Nat.succ_mod_two_eq_zero_iff, ← Nat.odd_iff]
  | succ d  =>
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    by_cases hzero : 0 ∈ S n k d
    · apply req_fun'_parity_of_zero_mem_S n hn ne_one k hd h hzero
    · apply req_fun'_parity_of_zero_mem_S_compl n hn ne_one k hd h (Finset.mem_compl.2 hzero)

lemma val_add_one_lt_of_ne_last {z : Fin (n + 1)} (hz : z ≠ Fin.last n) : z.val + 1 < n + 1 := by
  rw [← Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) hz)]
  apply Fin.is_lt _

lemma req_fun'_parity' (hn : Odd n) (ne_one : n ≠ 1) (k : ℕ) (i : Fin (n + 1)) : (req_fun' n k i).val % 2 = (k + i) % 2 := by
  have h_add_one_ne_one : n + 1 ≠ 1 := by
    simp only [ne_eq, add_left_eq_self]
    apply NeZero.ne _
  by_cases h : i.val + 1 < n + 1
  · have := req_fun'_parity n hn ne_one k h
    simp only [Fin.cast_val_eq_self] at this
    rw [this]
  · by_cases h2 : i = 0
    · exfalso
      apply h
      rw [h2]
      simp only [Fin.val_zero, zero_add, lt_add_iff_pos_left, Nat.pos_of_ne_zero (NeZero.ne _)]
    have h3 : i - 1 ≠ Fin.last n := by
      intro heq
      rw [sub_eq_iff_eq_add, Fin.last_add_one] at heq
      apply h2 heq
    have := req_fun'_parity n hn ne_one k (val_add_one_lt_of_ne_last n h3)
    simp only [Nat.cast_zero, Fin.cast_val_eq_self, zero_add] at this
    have h4 := req_fun'_bdry n ne_one k (val_add_one_lt_of_ne_last n h3)
    have h5 := mem_of_mem_bdry _ (req_fun'_spec' n k (val_add_one_lt_of_ne_last n h3))
    simp only [Nat.cast_zero, Fin.cast_val_eq_self, sub_add_cancel] at h5
    rw [mem_bdry] at h4
    simp only [Nat.cast_zero, Fin.cast_val_eq_self, Finset.mem_compl] at h4
    rw [not_lt] at h
    have h'' : i.val + 1 ≤ n + 1 := by
      apply Nat.succ_le_succ (Fin.le_last _)
    have h' : i = n := by
      rw [Nat.succ_le_succ_iff] at *
      rw [Fin.ext_iff]
      simp only [Fin.cast_nat_eq_last, Fin.val_last]
      apply le_antisymm h'' h
    have hS_compl_card : (S n k (i - 1))ᶜ.card = 1 := by
      rw [Finset.card_compl, S_card_eq' _]
      simp only [Fintype.card_fin, h', Fin.val_last, Nat.succ_sub_succ_eq_sub, Fin.cast_nat_eq_last, Fin.val_last]
      rw [Nat.sub_sub_self (Nat.pos_of_ne_zero (NeZero.ne _))]
      · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero _)]
        · rw [h']
          simp only [Fin.cast_nat_eq_last, Fin.val_last, lt_add_iff_pos_right, zero_lt_one]
        rw [h']
        simp only [Fin.cast_nat_eq_last, Fin.val_last, ne_eq]
        apply NeZero.ne _
    rw [Finset.card_eq_one] at hS_compl_card
    cases' hS_compl_card with a ha
    rw [Finset.ext_iff] at ha
    simp only [Finset.mem_singleton] at ha
    have h7 : (i - 1).val = i.val - 1 := by
      rw [Fin.coe_sub_iff_le.2 _]
      simp only [Fin.val_one', Nat.one_mod_of_ne_one h_add_one_ne_one]
      rw [← zero_add (1 : Fin (n + 1)), h']
      apply Fin.add_one_le_of_lt (Fin.pos_of_ne_zero _)
      simp only [Fin.cast_nat_eq_last, ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero, NeZero.ne,
        not_false_eq_true]
    rw [h7] at h5
    have h6 := (ha (req_fun' n k i)).1 h5
    cases' h4.2 with h8 h8
    · rw [← Finset.mem_compl] at h8
      rw [h7] at h8
      have h9 := (ha _).1 h8
      rw [← h6] at h9 -- , succ'_eq_iff_eq_pred'
      rw [← h9, succ'_eq_add_one, Fin.val_add_one] --, Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last _) _), Nat.add_mod, this, ← Nat.add_mod, h7, add_assoc, Nat.sub_add_cancel (Nat.pos_of_ne_zero _)]
      split_ifs
      · next h10 => {
          rw [h10, h7] at this
          have h11 : i.val - 1 + 1 = i.val := by
            rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero _)]
            contrapose h2
            push_neg at *
            rw [Fin.ext_iff, h2, Fin.val_zero]
          simp only [Nat.zero_mod]
          rw [← h11, ← add_assoc, Nat.add_mod, ← this, Fin.val_last, Nat.odd_iff.1 hn] }
      · next h10 => {
          rw [Nat.add_mod, this, Nat.add_mod k, sub_one_mod_two n hn]
          simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_succ]
          rw [← add_assoc, add_assoc _ 1 1]
          simp only [Nat.reduceAdd, Nat.add_mod_right] }
    · rw [← Finset.mem_compl] at h8
      rw [h7] at h8
      have h9 := (ha _).1 h8
      rw [← h6] at h9
      rw [← h9, pred'_eq_add_one, sub_one_mod_two n hn, Nat.add_mod, this]
      rw [Nat.add_mod k, sub_one_mod_two n hn]
      simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_succ]
      rw [← add_assoc, add_assoc _ 1 1]
      simp only [Nat.reduceAdd, Nat.add_mod_right]

theorem main' (hn : Odd n) (f : PMF (Fin (n + 1))) : ∃ g : game' n, (PMF.toMeasure f) (first_player_share_at_level' n g) ≥ 1/2 := --(f : Finset (Fin n) → Set.Icc (0 : ℝ) 1)
by
  have h_add_one_ne_one : n + 1 ≠ 1 := by
    simp only [ne_eq, add_left_eq_self]
    apply NeZero.ne _
  set S := {i : Fin (n + 1) | Even i.val ∧ i.val < (n + 1)} with hS -- not sure Even means the right thing for Fin n
  cases' req2' (n + 1) f S with h h
  · refine' ⟨construct_game' n 0, _⟩
    have : first_player_share_at_level' n (construct_game' n 0) = S := by
      rw [first_player_share_at_level']
      ext y
      rw [hS]
      simp only [ne_eq, Finset.coe_union, Finset.coe_singleton, Finset.coe_biUnion,
        Set.coe_toFinset, Set.mem_setOf_eq, Set.singleton_union, Set.mem_insert_iff, Set.mem_iUnion,
        Set.mem_singleton_iff, exists_prop, Fin.is_lt, and_true]
      by_cases ne_one : n = 1
      · subst n
        revert y
        rw [Fin.forall_fin_two]
        simp only [Fin.isValue, construct_game', req_fun'_zero, Nat.reduceAdd, Nat.lt_succ, true_or,
          Fin.val_zero, even_zero, one_ne_zero, false_or, Fin.val_one, Nat.not_even_one, iff_false,
          not_exists, not_and, and_imp, true_and]
        intro x h1 h2 h3 _
        rw [Nat.le_one_iff_eq_zero_or_eq_one] at h3
        cases' h3 with h3 h3
        · apply h1 h3
        · rw [h3] at h2
          simp only [Nat.not_even_one] at h2
      refine' ⟨λ hy => _, λ hy => _⟩
      · rw [construct_game'] at hy
        simp only at hy
        · cases' hy with hy hy
          { rw [req_fun'_zero] at hy
            rw [hy]
            simp only [Fin.is_lt, and_true, Set.mem_setOf_eq, Fin.val_zero', even_zero] }
          { obtain ⟨i, h1, h2⟩ := hy
            rw [h2, Nat.even_iff, ← Nat.cast_zero, req_fun'_parity n hn ne_one _, zero_add, ← Nat.even_iff]
            · apply h1.2.1
            -- break into cases i = n - 1 and otherwise : n - 1 is odd so we have a contradiction
            rw [Nat.lt_succ, ← Nat.succ_le_succ_iff] at h1
            apply lt_of_le_of_ne h1.2.2 _
            intro heq
            simp only [Nat.succ.injEq] at heq
            rw [heq, Nat.even_iff_not_odd] at h1
            apply h1.2.1 hn }
      · rw [construct_game']
        simp only
        by_cases hzero : y = 0
        · rw [hzero]
          left
          rw [req_fun'_zero]
        · right
          obtain ⟨z, hz⟩ := req_fun'_surj n 0 y
          refine' ⟨z, ⟨_, ⟨_, Fin.is_lt _⟩⟩, _⟩
          · intro heq
            have h1 : z = 0 := by rw [Fin.ext_iff, heq, Fin.val_zero]
            rw [h1, req_fun'_zero, Nat.cast_zero] at hz
            apply hzero
            rw [hz]
          · rw [Nat.cast_zero] at hz
            have h1 : (req_fun' n (↑0) z).val % 2 = y.val % 2 := by
              rw [hz]
            rw [Nat.even_iff.1 hy] at h1
            rw [← Nat.cast_zero, req_fun'_parity' n hn ne_one, zero_add, ← Nat.even_iff] at h1
            apply h1
          · rw [← hz]
            congr
            ext
            simp only [Fin.val_nat_cast, Nat.mod_eq_of_lt (Fin.is_lt _)]
    rw [this]
    -- now apply transitivity
    apply le_trans (ENNReal.div_le_of_le_mul _) h
    simp only [one_div]
    rw [← ENNReal.mul_le_iff_le_inv (by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]) (by simp only [ne_eq,
      ENNReal.two_ne_top, not_false_eq_true])]
    norm_num
  · refine' ⟨construct_game' n 1, _⟩
    have : first_player_share_at_level' n (construct_game' n 1) = Sᶜ := by
      rw [first_player_share_at_level']
      ext y
      simp only [ne_eq, Finset.coe_union, Finset.coe_singleton, Finset.coe_biUnion,
        Set.coe_toFinset, Set.mem_setOf_eq, Set.singleton_union, Set.mem_insert_iff, Set.mem_iUnion,
        Set.mem_singleton_iff, exists_prop, Fin.is_lt, and_true]
      refine' ⟨λ hy => _, λ hy => _⟩
      · rw [construct_game'] at hy
        simp only at hy
        · cases' hy with hy hy
          { rw [req_fun'_zero] at hy
            rw [hy]
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Fin.val_one']
            intro hmem
            rw [hS] at hmem
            simp [Fin.is_lt, and_true, Set.mem_setOf_eq, Fin.val_one'] at hmem
            rw [Nat.one_mod_of_ne_one _] at hmem
            · simp only [Nat.not_even_one] at hmem
            simp only [ne_eq, add_left_eq_self, NeZero.ne, not_false_eq_true] }
          { obtain ⟨i, h1, h2⟩ := hy
            rw [h2, Set.mem_compl_iff]--, Nat.odd_iff, ← Nat.cast_zero, req_fun'_parity n _ _, zero_add, ← Nat.even_iff]
            intro h3
            rw [Set.mem_setOf_eq, Nat.even_iff] at h3
            -- break into cases i = n - 1 and otherwise : n - 1 is odd so we have a contradiction
            have h5 : i + 1 < n + 1 := by
              rw [Nat.lt_succ, ← Nat.succ_le_succ_iff] at h1
              apply lt_of_le_of_ne h1.2.2 _
              intro heq
              simp only [Nat.succ.injEq] at heq
              rw [heq, Nat.even_iff_not_odd] at h1
              apply h1.2.1 hn
            by_cases ne_one : n = 1
            · subst n
              revert y
              rw [Fin.forall_fin_two]
              exfalso
              apply h1.1
              rw [Nat.succ_lt_succ_iff, Nat.lt_one_iff] at h5
              rw [h5]
            have h4 := req_fun'_parity n hn ne_one 1 h5
            rw [Nat.even_iff, ← Nat.succ_mod_two_eq_one_iff] at h1
            rw [Nat.cast_one, h3.1, add_comm, h1.2.1] at h4
            apply zero_ne_one' ℕ h4 }
      · rw [construct_game']
        simp only
        by_cases hzero : y = 1
        · rw [hzero]
          left
          rw [req_fun'_zero]
        · right
          obtain ⟨z, hz⟩ := req_fun'_surj n 1 y
          refine' ⟨z, ⟨_, ⟨_, Fin.is_lt _⟩⟩, _⟩
          · intro heq
            have h1 : z = 0 := by rw [Fin.ext_iff, heq, Fin.val_zero]
            rw [h1, req_fun'_zero, Nat.cast_one] at hz
            apply hzero
            rw [hz]
          · -- whole thing has been copied from above, changing 0 to 1
            rw [Nat.cast_one] at hz
            have h1 : (req_fun' n (↑1) z).val % 2 = y.val % 2 := by
              rw [hz]
            have hy' : Odd y.val := by
              rw [hS] at hy
              simp only [Fin.is_lt, and_true, Set.mem_compl_iff, Set.mem_setOf_eq] at hy
              rwa [Nat.odd_iff_not_even]
            rw [Nat.odd_iff.1 hy'] at h1
            --conv_lhs at h1 => { rw [← @Nat.cast_one (Fin (n + 1))] }
            rw [← @Nat.cast_one (Fin (n + 1)), req_fun'_parity' n hn _, add_comm, Nat.succ_mod_two_eq_one_iff, ← Nat.even_iff] at h1
            apply h1
            · intro heq
              subst n
              revert y
              rw [Fin.forall_fin_two]
              simp only [Fin.isValue, Set.mem_compl_iff, zero_ne_one, not_false_eq_true,
                Fin.val_zero, Nat.odd_iff_not_even, even_zero, not_true_eq_false,
                IsEmpty.forall_iff, implies_true, forall_true_left, Fin.val_one, odd_one,
                imp_false, and_self]
          · rw [← hz]
            congr
            ext
            simp only [Fin.val_nat_cast, Nat.mod_eq_of_lt (Fin.is_lt _)]
    rw [this]
    -- now apply transitivity
    apply h
  -- a good exercise is to figure out where `n` being even is used
