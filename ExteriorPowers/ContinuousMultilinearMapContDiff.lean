import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Extension.Well
import ExteriorPowers.MultilinearMapBasic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Curry


open Filter Asymptotics ContinuousLinearMap Metric
open Topology NNReal Asymptotics ENNReal
open NormedField BigOperators Finset



variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
{E : ι → Type*} {F : Type*} {n : ℕ}
[(i : ι) → NormedAddCommGroup (E i)] [NormedAddCommGroup F] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedSpace 𝕜 F] [DecidableEq ι]

namespace MultilinearMap

open Finset in
lemma linearDeriv_bound (f : ContinuousMultilinearMap 𝕜 E F) (x y : (i : ι) → E i) :
    ‖f.linearDeriv x y‖ ≤ ‖f‖ * (∑ i, (∏ j in univ.erase i, ‖x j‖)) * ‖y‖ := by
  rw [linearDeriv_apply, mul_sum, sum_mul]
  apply norm_sum_le_of_le
  intro i _
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) (mul_nonneg (norm_nonneg _)
    (prod_nonneg (fun i _ ↦ norm_nonneg _))))
  conv_rhs => congr; rfl; rw [← (Function.update_same i (y i) x)]
  rw [mul_assoc, prod_congr rfl (g := fun j ↦ ‖Function.update x i (y i) j‖)
    (fun _ hj ↦ by simp only; rw [Function.update_noteq (ne_of_mem_erase hj)]),
    prod_erase_mul univ _ (Finset.mem_univ _)]
  apply ContinuousMultilinearMap.le_op_norm

open Finset in
lemma domDomRestrict_bound (f : ContinuousMultilinearMap 𝕜 E F)
    (s : Finset ι) (x : ((i : ↑↑(sᶜ)) → E i)) (z : (i : s) → E i) : ‖f.domDomRestrict s
    (fun ⟨i, hi⟩ => x ⟨i, mem_compl.mpr (Set.not_mem_of_mem_compl hi)⟩) z‖
    ≤ ‖f‖ * (∏ i, ‖x i‖) * (∏ i, ‖z i‖) := by
  rw [domDomRestrict_apply]
  refine le_trans (ContinuousMultilinearMap.le_op_norm _ _) ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← (prod_compl_mul_prod s)]
  refine mul_le_mul ?_ ?_ (prod_nonneg (fun _ _ => norm_nonneg _))
    (prod_nonneg (fun _ _ => norm_nonneg _))
  all_goals (rw [← prod_coe_sort]; apply prod_le_prod (fun _ _ => norm_nonneg _))
  · exact fun ⟨i, hi⟩ _ ↦ by rw [mem_compl] at hi; simp only [mem_coe, hi, dite_false, le_refl]
  · exact fun i _ => by simp only [mem_coe, coe_mem, dite_true]; rfl

end MultilinearMap

namespace ContinuousMultilinearMap

noncomputable def domDomRestrict (f : ContinuousMultilinearMap 𝕜 E F) (s : Finset ι)
    (x : (i : ↑↑sᶜ) → E i) : ContinuousMultilinearMap 𝕜 (fun (i : s) => E i) F :=
  MultilinearMap.mkContinuous (f.toMultilinearMap.domDomRestrict s
  (fun ⟨i, hi⟩ => x ⟨i, mem_compl.mpr (Set.not_mem_of_mem_compl hi)⟩))
  (‖f‖ * (∏ i, ‖x i‖)) (MultilinearMap.domDomRestrict_bound f s x)

@[simp]
lemma domDomRestrict_apply (f : ContinuousMultilinearMap 𝕜 E F) (s : Finset ι)
    (x : (i : ↑↑sᶜ) → E i) (z : (i : s) → E i) :
    f.domDomRestrict s x z = f (fun i => if h : i ∈ s then z ⟨i, h⟩ else
    x ⟨i, Finset.mem_compl.mpr h⟩) := rfl

lemma domDomRestrict_norm_le (f : ContinuousMultilinearMap 𝕜 E F) (s : Finset ι)
    (x : (i : ↑↑sᶜ) → E i) : ‖f.domDomRestrict s x‖ ≤ ‖f‖ * (∏ i, ‖x i‖) :=
  ContinuousMultilinearMap.op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (prod_nonneg
  (fun _ _ ↦ norm_nonneg _))) (fun z ↦ MultilinearMap.domDomRestrict_bound f s x z)

open Finset in
noncomputable def fderiv (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    ((i : ι) → E i) →L[𝕜] F :=
  LinearMap.mkContinuous (f.toMultilinearMap.linearDeriv x)
  (‖f‖ * ∑ i, (∏ j in univ.erase i, ‖x j‖)) (fun y ↦ MultilinearMap.linearDeriv_bound f x y)

@[simp]
lemma fderiv_apply (f : ContinuousMultilinearMap 𝕜 E F) (x y : (i : ι) → E i) :
    f.fderiv x y = ∑ i, f (Function.update x i (y i)) := by
  unfold fderiv
  simp only [mem_univ, not_true_eq_false, LinearMap.mkContinuous_apply,
    MultilinearMap.linearDeriv_apply, coe_coe]

lemma fderiv_norm_le (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    ‖f.fderiv x‖ ≤ ‖f‖ * ∑ i, (∏ j in univ.erase i, ‖x j‖) :=
  ContinuousLinearMap.op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (sum_nonneg (fun _ _ ↦
  (prod_nonneg (fun _ _ ↦ norm_nonneg _))))) (fun z ↦ MultilinearMap.linearDeriv_bound f x z)

open Finset in
noncomputable def toFormalMultilinearSeries [LinearOrder ι]
    (f : ContinuousMultilinearMap 𝕜 E F) : FormalMultilinearSeries 𝕜 ((i : ι) → E i) F :=
  fun n ↦ if h : n = Fintype.card ι then
    (f.compContinuousLinearMap (fun i ↦ ContinuousLinearMap.proj i)).domDomCongr
    (Fintype.equivFinOfCardEq (Eq.symm h))
  else 0

lemma toFormalMultilinearSeries_support [LinearOrder ι] (f : ContinuousMultilinearMap 𝕜 E F)
    {n : ℕ} (hn : (Fintype.card ι).succ ≤ n) :
    f.toFormalMultilinearSeries n = 0 := by
  unfold toFormalMultilinearSeries
  simp only [Ne.symm (ne_of_lt (Nat.lt_of_succ_le hn)), dite_false]

lemma toFormalMultilinearSeries_radius [LinearOrder ι]
    (f : ContinuousMultilinearMap 𝕜 E F) : f.toFormalMultilinearSeries.radius = ⊤ :=
  FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (Fintype.card ι).succ
  (fun n ↦ f.toFormalMultilinearSeries_support (Nat.le_add_left (Fintype.card ι).succ n))

lemma toFormalMultilinearSeries_partialSum [LinearOrder ι]
    (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    f x = f.toFormalMultilinearSeries.partialSum (Fintype.card ι).succ x := by
  unfold toFormalMultilinearSeries FormalMultilinearSeries.partialSum
  rw [Finset.sum_eq_single_of_mem (Fintype.card ι) (by simp only [mem_range, Nat.lt_succ_self])
    (fun _ _ hm ↦ by simp only [hm, dite_false, zero_apply])]
  simp only [dite_true, domDomCongr_apply, compContinuousLinearMap_apply, proj_apply]

lemma toFormalMultilinearSeries_hasSum [LinearOrder ι] (f : ContinuousMultilinearMap 𝕜 E F)
    (x : (i : ι) → E i) : HasSum (fun (n : ℕ) => (f.toFormalMultilinearSeries n)
    fun (_ : Fin n) => x) (f x) := by
  rw [toFormalMultilinearSeries_partialSum]
  apply hasSum_sum_of_ne_finset_zero
  intro _ hn
  simp only [Finset.mem_range, not_lt] at hn
  rw [f.toFormalMultilinearSeries_support (lt_of_lt_of_le (Nat.lt_succ_self _) hn),
    zero_apply]

def hasFPowerSeriesAtOrigin [LinearOrder ι] (f : ContinuousMultilinearMap 𝕜 E F) :
    HasFPowerSeriesOnBall f f.toFormalMultilinearSeries 0 ⊤  where
  r_le := by rw [toFormalMultilinearSeries_radius]
  r_pos := zero_lt_top
  hasSum := fun _ => by rw [zero_add]; exact f.toFormalMultilinearSeries_hasSum _

variable [CompleteSpace F]

lemma analyticAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    AnalyticAt 𝕜 f x := by
  letI : LinearOrder ι := WellFounded.wellOrderExtension emptyWf.wf
  exact HasFPowerSeriesOnBall.analyticAt_of_mem f.hasFPowerSeriesAtOrigin
    (by simp only [emetric_ball_top, Set.mem_univ])

lemma analyticOn (f : ContinuousMultilinearMap 𝕜 E F) :
    AnalyticOn 𝕜 f ⊤ :=
  fun x _ ↦ f.analyticAt x

lemma contDiffAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) {n : ℕ∞} :
    ContDiffAt 𝕜 n f x := AnalyticAt.contDiffAt (f.analyticAt x)

lemma cOS [LinearOrder ι] (f : ContinuousMultilinearMap 𝕜 E F) {k l : ℕ}
    (h : k + l ≠ Fintype.card ι) :
    f.toFormalMultilinearSeries.changeOriginSeries k l = 0 := by
  unfold FormalMultilinearSeries.changeOriginSeries
  apply Finset.sum_eq_zero
  intro s _
  unfold FormalMultilinearSeries.changeOriginSeriesTerm
  rw [AddEquivClass.map_eq_zero_iff]
  unfold toFormalMultilinearSeries
  simp only [h, dite_false]

lemma fderiv_eq (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    _root_.fderiv 𝕜 f x = f.fderiv x := by
  letI : LinearOrder ι := WellFounded.wellOrderExtension emptyWf.wf
  ext y
  have := f.hasFPowerSeriesAtOrigin.changeOrigin (y := x) (r := ⊤) (by simp only [coe_lt_top])
  rw [zero_add] at this
  rw [this.hasFPowerSeriesAt.fderiv_eq, fderiv_apply]
  unfold FormalMultilinearSeries.changeOrigin FormalMultilinearSeries.sum
  rw [tsum_eq_single (Fintype.card ι - 1)]
  · simp only [continuousMultilinearCurryFin1_apply]
    by_cases he : IsEmpty ι
    · simp only [univ_eq_empty, sum_empty]
      letI := he
      rw [Fintype.card_eq_zero, Nat.zero_sub, cOS, ContinuousMultilinearMap.zero_apply,
        ContinuousMultilinearMap.zero_apply]
      rw [Fintype.card_eq_zero, add_zero]
      exact Nat.one_ne_zero
    · unfold FormalMultilinearSeries.changeOriginSeries
      simp only [ContinuousMultilinearMap.sum_apply, continuousMultilinearCurryFin1_apply]
      have heq : Fin.snoc 0 y = (fun _ : Fin (0 + 1) ↦ y) := by
        ext _ _
        unfold Fin.snoc
        simp only [Fin.coe_fin_one, lt_self_iff_false, Fin.castSucc_castLT, Pi.zero_apply,
          cast_eq, dite_eq_ite, ite_false]
      rw [heq, sum_apply, sum_apply]
      have hcard : Fintype.card ι = 1 + (Fintype.card ι - 1) := by
        letI := not_isEmpty_iff.mp he
        rw [← Nat.succ_eq_one_add, ← Nat.pred_eq_sub_one, Nat.succ_pred Fintype.card_ne_zero]
      set I : (i : ι) → i ∈ Finset.univ → {s : Finset (Fin (1 + (Fintype.card ι - 1))) //
          s.card = Fintype.card ι - 1} := by
        intro i _
        refine ⟨Finset.univ.erase (Fintype.equivFinOfCardEq hcard i), ?_⟩
        simp only [mem_univ, not_true_eq_false, card_erase_of_mem, card_fin, ge_iff_le,
          add_le_iff_nonpos_right, nonpos_iff_eq_zero, tsub_eq_zero_iff_le, add_tsub_cancel_left]
      rw [Finset.sum_bij I (fun _ _ ↦ Finset.mem_univ _)]
      · intro i _
        rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply, toFormalMultilinearSeries]
        simp only [ge_iff_le, Eq.symm hcard, dite_true, piecewise_erase_univ, domDomCongr_apply,
          ne_eq, EmbeddingLike.apply_eq_iff_eq, compContinuousLinearMap_apply, proj_apply]
        congr
        ext j
        by_cases hj : j = i
        · rw [hj, Function.update_same, Function.update_same]
        · have hne : Fintype.equivFinOfCardEq hcard j ≠ Fintype.equivFinOfCardEq hcard i := by
            rw [ne_eq, Equiv.apply_eq_iff_eq]
            exact hj
          rw [Function.update_noteq hne, Function.update_noteq hj]
      · intro i j _ _
        simp only [mem_univ, not_true_eq_false, Subtype.mk.injEq,
          Finset.erase_inj _ (Finset.mem_univ _), Equiv.apply_eq_iff_eq, imp_self]
      · intro ⟨s, hs⟩ _
        have h : sᶜ.card = 1 := by
          rw [Finset.card_compl, hs]
          simp only [ge_iff_le, Fintype.card_fin, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
            add_tsub_cancel_right]
        rw [Finset.card_eq_one] at h
        obtain ⟨a, ha⟩ := h
        existsi (Fintype.equivFinOfCardEq hcard).symm a
        existsi Finset.mem_univ _
        simp only [mem_univ, not_true_eq_false, Equiv.apply_symm_apply, Subtype.mk.injEq]
        rw [Finset.erase_eq, ← ha]
        simp only [sdiff_compl, ge_iff_le, le_eq_subset, subset_univ, inf_of_le_right]
  · intro m hm
    rw [cOS f (k := 1) (l := m), ContinuousMultilinearMap.zero_apply]
    by_contra habs
    rw [← Nat.succ_eq_one_add] at habs
    apply_fun Nat.pred at habs
    rw [Nat.pred_succ, Nat.pred_eq_sub_one] at habs
    exact hm habs

end ContinuousMultilinearMap
