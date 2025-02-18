import Mathlib

--NOTE : it seems that we can replace n with n + 1 and NeZero n ; it is equivalent to n > 1 and there will be much lesser cases to deal with
variable {n : ℕ} [NeZero n]

def 

structure game where
  toFun : Fin (n + 1) → Fin (n + 1)
  rule : ∀ (i : Fin (n + 1)) (h : 0 < i.val), toFun i ∈

example : 1 + 1 = 2 := rfl
