import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Extension.Well
import ExteriorPowers.MultilinearMap


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


@[simp]
lemma deriv_coe (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → (E i)):
(f.deriv x).toLinearMap = f.toMultilinearMap.linearDeriv x := by
  apply LinearMap.ext
  intro y
  apply deriv_coe_apply


lemma sub_vs_deriv (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
((fun p => f p.1 - f p.2 - (deriv f x) (p.1 - p.2)) ∘ fun x_1 => (x, x) + x_1) =
    fun h => Finset.sum (Set.Finite.toFinset ((Set.finite_coe_iff (s := {s : Finset ι | 2 ≤ s.card})).mp
    inferInstance)) (fun (s : Finset ι) => f (s.piecewise h.1 x) - f (s.piecewise h.2 x)) := by
  have heq : ((fun p => f p.1 - f p.2 - (deriv f x) (p.1 - p.2)) ∘ fun x_1 => (x, x) + x_1) =
    (fun h => f (x + h.1) - f (x + h.2) - (deriv f x) (h.1 - h.2)) := by
    ext h
    rw [Function.comp_apply, Prod.fst_add, Prod.snd_add]
    simp only
    rw [sub_add_eq_sub_sub, add_comm, add_sub_assoc, sub_self, add_zero]
  rw [heq]
  ext h
  rw [deriv_coe_apply]; erw [MultilinearMap.sub_vs_linearDeriv]; rfl


lemma sub_piecewise_bound (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)
(h : (((i : ι) → (E i)) × ((i : ι) → E i)))
{s : Finset ι} (hs : 2 ≤ s.card) :
‖f (s.piecewise h.1 x) - f (s.piecewise h.2 x)‖ ≤ s.card • (‖f‖ *
‖x‖ ^ sᶜ.card * ‖h‖ ^ (s.card - 1) * ‖h.1 - h.2‖) := by
  letI : LinearOrder ι := WellFounded.wellOrderExtension emptyWf.wf
  set n := s.card
  convert (congr_arg norm (MultilinearMap.apply_sub f.toMultilinearMap h.1 h.2 x s rfl)).trans_le _
  refine le_trans (norm_sum_le _ _) ?_
  have heq : (Finset.univ (α := Fin n)).card = n := by simp only [Finset.card_fin]
  rw [←heq, ←(Finset.sum_const (α := Fin n))]
  apply Finset.sum_le_sum
  intro i _
  refine le_trans (ContinuousMultilinearMap.le_op_norm f _) ?_
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [←(Finset.prod_compl_mul_prod s)]
  set m := s.orderIsoOfFin rfl i
  rw [←(Finset.mul_prod_erase s _ m.2)]
  simp only [m.2, dite_true]
  conv => lhs
          congr
          rfl
          congr
          rw [OrderIso.symm_apply_apply]
          simp only [lt_irrefl i, ite_false, ite_true]
          rfl
  have hle1aux : ∀ (j : ι), j ∈ sᶜ →
    (fun k => ‖if hk : k ∈ s then
          if (OrderIso.symm (Finset.orderIsoOfFin s rfl)) ⟨k, hk⟩ < i then h.1 k
          else
            if (OrderIso.symm (Finset.orderIsoOfFin s rfl)) ⟨k, hk⟩ = i then h.1 k - h.2 k
            else h.2 k
        else x k‖) j ≤ ‖x‖ := by
    intro j hj
    rw [Finset.mem_compl] at hj
    simp only [hj, dite_false]
    apply norm_le_pi_norm
  have hle1 := Finset.prod_le_prod (s := sᶜ) (fun j _ => norm_nonneg _) hle1aux
  rw [Finset.prod_const] at hle1
  have hle2aux : ∀ (j : ι), j ∈ Finset.erase s m →
    (fun k =>  ‖if hk : k ∈ s then
    if (OrderIso.symm (Finset.orderIsoOfFin s rfl)) ⟨k, hk⟩ < i then h.1 k
    else
    if (OrderIso.symm (Finset.orderIsoOfFin s rfl)) ⟨k, hk⟩ = i then h.1 k - h.2 k
    else h.2 k
    else x k‖) j ≤ ‖h‖ := by
    intro j hj
    set hj' := Finset.mem_of_mem_erase hj
    simp only [hj', dite_true]
    by_cases hj'' : (s.orderIsoOfFin rfl).symm ⟨j, hj'⟩ < i
    . simp only [hj'', ite_true]
      refine le_trans ?_ (norm_fst_le h)
      apply norm_le_pi_norm
    . simp only [hj'', ite_false]
      have hj''' : (s.orderIsoOfFin rfl).symm ⟨j, hj'⟩ ≠ i := by
        by_contra habs
        rw [Finset.mem_erase] at hj
        simp only at hj
        rw [←habs] at hj
        simp only [OrderIso.apply_symm_apply, ne_eq, not_true_eq_false, false_and] at hj
      simp only [hj''', ite_false, ge_iff_le]
      refine le_trans ?_ (norm_snd_le h)
      apply norm_le_pi_norm
  have hle2 := Finset.prod_le_prod (s := s.erase m) (fun j _ => norm_nonneg _) hle2aux
  rw [Finset.prod_const, Finset.card_erase_of_mem m.2] at hle2
  refine le_trans (mul_le_mul_of_nonneg_right hle1 (mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))) ?_
  refine mul_le_mul_of_nonneg_left (α := ℝ) ?_ (pow_nonneg (norm_nonneg _) _)
  rw [mul_comm]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  . simp only [Finset.card_fin]
    exact hle2
  . rw [←Pi.sub_apply]
    apply norm_le_pi_norm


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


-- Derivability results.

variable {u : Set ((i : ι) → E i)}

theorem hasStrictFDerivAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    HasStrictFDerivAt f (f.deriv x) x := by
  letI : LinearOrder ι := WellFounded.wellOrderExtension emptyWf.wf
  simp only [HasStrictFDerivAt]
  simp only [←map_add_left_nhds_zero (x, x), isLittleO_map]
  have heq : ((fun p => p.1 - p.2) ∘ fun p => (x, x) + p) = fun p => p.1 - p.2 := by
    apply funext
    intro p
    simp only [Function.comp_apply, Prod.fst_add, Prod.snd_add, add_sub_add_left_eq_sub]
  rw [sub_vs_deriv, heq]
  apply Asymptotics.IsLittleO.sum
  intro s hs
  simp only [Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, not_le, Finset.mem_filter,
    true_and] at hs
  apply sub_piecewise_littleO f x hs

theorem hasFDerivAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    HasFDerivAt f (f.deriv x) x :=
  (f.hasStrictFDerivAt x).hasFDerivAt

theorem hasFDerivWithinAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    HasFDerivWithinAt f (f.deriv x) u x :=
  (f.hasFDerivAt x).hasFDerivWithinAt

theorem differentiableAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    DifferentiableAt 𝕜 f x :=
  (f.hasFDerivAt x).differentiableAt

theorem differentiableWithinAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    DifferentiableWithinAt 𝕜 f u x :=
  (f.differentiableAt x).differentiableWithinAt

protected theorem fderiv (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i) :
    fderiv 𝕜 f x = f.deriv x :=
  HasFDerivAt.fderiv (f.hasFDerivAt x)

protected theorem fderivWithin (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)
    (hxs : UniqueDiffWithinAt 𝕜 u x) : fderivWithin 𝕜 f u x = f.deriv x := by
  rw [DifferentiableAt.fderivWithin (f.differentiableAt x) hxs]
  exact f.fderiv x

theorem differentiable (f : ContinuousMultilinearMap 𝕜 E F) : Differentiable 𝕜 f :=
  fun x => f.differentiableAt x

theorem differentiableOn (f : ContinuousMultilinearMap 𝕜 E F) :
    DifferentiableOn 𝕜 f u :=
  f.differentiable.differentiableOn


#exit

theorem ContinuousMultilinearMap.contDiff {𝕜 : Type*} {ι : Type*} [Fintype ι] {E : ι → Type*} {F : Type*}
[NontriviallyNormedField 𝕜] [(i : ι) → NormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} (M : ContinuousMultilinearMap 𝕜 E F) :
ContDiff 𝕜 n M.toFun := sorry
