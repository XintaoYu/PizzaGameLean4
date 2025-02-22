import Mathlib

variable (R : Type*) [CommRing R] [IsDomain R] [DiscreteValuationRing R]
-- instance : IsNoetherianRing R := inferInstance

-- instance : IsDedekindDomain R := inferInstance

-- instance : IsDedekindRing R := inferInstance

example : Ring.DimensionLEOne R := by
  exact IsDedekindRing.toDimensionLEOne

example : Order.krullDim ℤ = 1 := by
  sorry

example : ringKrullDim R = 1 := by
  unfold ringKrullDim
  sorry
