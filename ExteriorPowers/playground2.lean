import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Extension.Well


open Filter Asymptotics ContinuousLinearMap Set Metric
open Topology NNReal Asymptotics ENNReal
open NormedField


namespace ContinuousMultilinearMap


variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
{E : ι → Type w₁} {F : Type w₂}
[(i : ι) → NormedAddCommGroup (E i)] [NormedAddCommGroup F] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedSpace 𝕜 F] [DecidableEq ι]


noncomputable def deriv (f : ContinuousMultilinearMap 𝕜 E F)
(x : (i : ι) → E i) : ((i : ι) → E i) →L[𝕜] F :=
Finset.sum Finset.univ (fun (i : ι) => (f.toContinuousLinearMap x i).comp (ContinuousLinearMap.proj i))



@[simp]
lemma deriv_apply (f : ContinuousMultilinearMap 𝕜 E F)
(x y : (i : ι) → E i) :
  f.deriv x y = Finset.sum Finset.univ (fun (i : ι) => f (Function.update x i (y i))) := by
  unfold deriv toContinuousLinearMap
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, LinearMap.coe_toAddHom, Finset.sum_apply,
    Function.comp_apply, ContinuousLinearMap.proj_apply, MultilinearMap.toLinearMap_apply, coe_coe]

@[simp]
lemma deriv_coe_apply (f : ContinuousMultilinearMap 𝕜 E F) (x y: (i : ι) → (E i)):
f.deriv x y = f.toMultilinearMap.linearDeriv x y := by
  simp only [deriv_apply, MultilinearMap.linearDeriv_apply, coe_coe]
  -- Goal: (Finset.sum Finset.univ fun x_1 ↦ f (Function.update x x_1 (y x_1))) =
  --        Finset.sum Finset.univ fun x_1 ↦ f (Function.update x x_1 (y x_1))
  rfl /-Error nmessage: type mismatch
  HEq.rfl
has type
  HEq ?m.22983 ?m.22983 : Prop
but is expected to have type
  (Finset.sum Finset.univ fun x_1 ↦ f (Function.update x x_1 (y x_1))) =
    Finset.sum Finset.univ fun x_1 ↦ f (Function.update x x_1 (y x_1)) : Prop-/
