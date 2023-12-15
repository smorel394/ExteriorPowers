import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ExteriorPowers.MultilinearMap

open Classical

open Filter Asymptotics ContinuousLinearMap Set Metric
open Topology Classical NNReal Asymptotics ENNReal
open NormedField

namespace ContinuousMultilinearMap

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {ι ι' : Type v} [Fintype ι] [LinearOrder ι]
{E : ι → Type w₁} {F : Type w₂}
[(i : ι) → NormedAddCommGroup (E i)] [NormedAddCommGroup F] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedSpace 𝕜 F]


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
lemma deriv_coe (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → (E i)):
(f.deriv x).toLinearMap = f.toMultilinearMap.linearDeriv x := by
  apply LinearMap.ext
  intro y
  erw [deriv_apply]
  rw [MultilinearMap.linearDeriv_apply]
  congr

lemma sub_piecewise_bound (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)
(h : (((i : ι) → (E i)) × ((i : ι) → E i)))
{s : Finset ι} (hs : 2 ≤ s.card) :
‖f (s.piecewise h.1 x) - f (s.piecewise h.2 x)‖ ≤ s.card • (‖f‖ *
‖x‖ ^ sᶜ.card * ‖h‖ ^ (s.card - 1) * ‖h.1 - h.2‖) := by
  set n := s.card
  erw [MultilinearMap.apply_sub _ _ _ _ _ rfl]
  refine le_trans (norm_sum_le _ _) ?_
  have heq : (Finset.univ (α := Fin n)).card = n := by simp only [Finset.card_fin]
  rw [←heq, ←(Finset.sum_const (α := Fin n))]
  apply Finset.sum_le_sum
  intro i _
  refine le_trans (ContinuousMultilinearMap.le_op_norm f _) ?_
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  sorry

lemma sub_piecewise_littleO (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)
{s : Finset ι} (hs : 2 ≤ s.card) :
(fun (h : (((i : ι) → (E i)) × ((i : ι) → E i))) =>
f (s.piecewise h.1 x) - f (s.piecewise h.2 x)) =o[nhds 0] (fun p => p.1 - p.2) := by
  rw [Asymptotics.isLittleO_iff]
  intro C hC
  have hspos : 0 < s.card - 1  := by
    rw [←Nat.pred_eq_sub_one, Nat.lt_pred_iff, ←Nat.succ_le_iff]
    exact hs
  have h0 : 0 ≤ s.card * ‖f‖ * ‖x‖ ^ sᶜ.card :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _)
  have h0' : 0 < s.card * ‖f‖ * ‖x‖ ^ sᶜ.card + 1 :=
    lt_of_lt_of_le (zero_lt_one) (le_add_of_nonneg_left h0)
  have h1 : 0 < C / (s.card * ‖f‖ * ‖x‖ ^ sᶜ.card + 1) := div_pos hC h0'
  apply Filter.Eventually.mp
    (eventually_nhds_norm_smul_sub_lt (1 : 𝕜) (0 : (((i : ι) → (E i)) × ((i : ι) → E i)))
      (ε := Real.rpow (C / (s.card * ‖f‖ * ‖x‖ ^ (sᶜ.card) + 1)) ((Nat.cast (R := ℝ) (s.card - 1))⁻¹))
      (Real.rpow_pos_of_pos h1 _))
  apply Filter.eventually_of_forall
  intro h
  rw [one_smul, sub_zero]
  intro hbound
  refine le_trans (sub_piecewise_bound f x h hs) ?_
  simp only [ge_iff_le, nsmul_eq_mul]
  rw [←mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (h.1 - h.2))
  have h2 := pow_le_pow_of_le_left (norm_nonneg h) (le_of_lt hbound) (s.card - 1)
  erw [Real.rpow_nat_inv_pow_nat (le_of_lt h1) (Ne.symm (ne_of_lt hspos))] at h2
  rw [←mul_assoc, ←mul_assoc]
  refine le_trans (mul_le_mul_of_nonneg_left h2 h0) ?_
  rw [mul_div, _root_.div_le_iff h0']
  linarith


theorem hasStrictFDerivAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)  :
    HasStrictFDerivAt f (f.deriv x) x := by
  simp only [HasStrictFDerivAt]
  simp only [←map_add_left_nhds_zero (x, x), isLittleO_map]
  have h : ((fun p => f p.1 - f p.2 - (deriv f x) (p.1 - p.2)) ∘ fun x_1 => (x, x) + x_1) =
    (fun h => f (x + h.1) - f (x + h.2) - (deriv f x) (h.1 - h.2)) := by
    ext h
    rw [Function.comp_apply, Prod.fst_add, Prod.snd_add]
    simp only
    rw [sub_add_eq_sub_sub, add_comm, add_sub_assoc, sub_self, add_zero]
  rw [h]
  sorry




#exit

theorem ContinuousMultilinearMap.contDiff {𝕜 : Type*} {ι : Type*} [Fintype ι] {E : ι → Type*} {F : Type*}
[NontriviallyNormedField 𝕜] [(i : ι) → NormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} (M : ContinuousMultilinearMap 𝕜 E F) :
ContDiff 𝕜 n M.toFun := sorry
