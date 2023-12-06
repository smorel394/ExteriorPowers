import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic


open Classical


theorem ContinuousMultilinearMap.contDiff {𝕜 : Type*} {ι : Type*} [Fintype ι] {E : ι → Type*} {F : Type*}
[NontriviallyNormedField 𝕜] [(i : ι) → NormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} (M : ContinuousMultilinearMap 𝕜 E F) :
ContDiff 𝕜 n M.toFun := sorry
