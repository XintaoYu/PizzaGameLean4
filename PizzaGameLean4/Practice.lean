import Mathlib

variable (R : Type*) [EuclideanDomain R]

instance : CancelCommMonoidWithZero R := inferInstance

instance : DecompositionMonoid R := inferInstance

example : ∀ a : R, Irreducible a ↔ Prime a := by
  intro a
  exact @irreducible_iff_prime R _ _ a

example : Subsingleton (ℤ →+* ℤ) := by
  exact RingHom.Int.subsingleton_ringHom

example : Unique (ℤ →+* ℤ) := by
  exact Unique.mk' (ℤ →+* ℤ)
