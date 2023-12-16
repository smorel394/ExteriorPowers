import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear
import Mathlib.Order.Extension.Well

namespace MultilinearMap

variable {R : Type uR} [Semiring R]  {ι : Type uι} {M : ι → Type v} {N : Type w}
[∀ (i : ι), AddCommGroup (M i)] [AddCommGroup N] [∀ (i : ι), Module R (M i)]
[Module R N] {n : ℕ}

lemma apply_sub [LinearOrder ι]
(f : MultilinearMap R M N) (a b v : (i : ι) → (M i)) (s : Finset ι)
(hs : Finset.card s = n) :
f (s.piecewise a v) - f (s.piecewise b v) = Finset.sum Finset.univ (fun (i : Fin n) =>
f (fun j => if h : j ∈ s then (if (s.orderIsoOfFin hs).symm ⟨j, h⟩ < i then a j
else if (s.orderIsoOfFin hs).symm ⟨j, h⟩ = i then a j - b j else b j) else v j)) := by sorry

end MultilinearMap

namespace ContinuousMultilinearMap



variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
{E : ι → Type w₁} {F : Type w₂}
[(i : ι) → NormedAddCommGroup (E i)] [NormedAddCommGroup F] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedSpace 𝕜 F] [DecidableEq ι]


noncomputable def deriv (f : ContinuousMultilinearMap 𝕜 E F)
(x : (i : ι) → E i) : ((i : ι) → E i) →L[𝕜] F :=
Finset.sum Finset.univ (fun (i : ι) => (f.toContinuousLinearMap x i).comp (ContinuousLinearMap.proj i))

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
  apply mul_le_mul
  . apply le_refl (‖x‖ ^ sᶜ.card)
  /- Error message:
  tactic 'apply' failed, failed to unify
  ‖x‖ ^ Finset.card sᶜ ≤ ‖x‖ ^ Finset.card sᶜ
with
  ‖x‖ ^ Finset.card sᶜ ≤ ‖x‖ ^ Finset.card sᶜ-/

end ContinuousMultilinearMap
