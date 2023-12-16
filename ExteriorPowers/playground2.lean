import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear

variable {R : Type uR} [Semiring R]  {ι : Type uι} {M : ι → Type v} {N : Type w}
[∀ (i : ι), AddCommGroup (M i)] [AddCommGroup N] [∀ (i : ι), Module R (M i)]
[Module R N] {n : ℕ} [DecidableEq ι]

example (i : ι) (x : (i : ι) → M i) (hx : x = 0) :
Function.update x i 0 = 0 := by
  ext j
  by_cases h : j = i
  . rw [h]
  . sorry
