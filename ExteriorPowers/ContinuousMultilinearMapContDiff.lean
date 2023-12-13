import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear
import Mathlib.Analysis.Calculus.ContDiff.Basic


open Classical

namespace ContinuousMultilinearMap

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
{E : ι → Type w₁} {F : Type w₂}
[(i : ι) → NormedAddCommGroup (E i)] [NormedAddCommGroup F] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedSpace 𝕜 F] {n : ℕ}
{G : Fin n → Type w₃} [(i : Fin n) → NormedAddCommGroup (G i)] [(i : Fin n) → NormedSpace 𝕜 (G i)]


lemma multilinearMap_fin_sub (f : MultilinearMap 𝕜 G F) (a b : (i : Fin n) → (G i)) :
f a - f b = Finset.sum Finset.univ (fun i =>
f (fun j => if j < i then a j else if j = i then a j - b j else b j)) := by
  by_cases hzero : n = 0
  . have heq1 : Finset.univ (α := Fin n) = ∅ := by
      ext i
      simp only [Finset.mem_univ, Finset.not_mem_empty, iff_false, not_true_eq_false]
      have h := i.2
      simp_rw [hzero] at h
      simp only [not_lt_zero'] at h
    rw [heq1, Finset.sum_empty]
    have heq2 : a = b := by
      ext i
      exfalso
      have h := i.2
      simp_rw [hzero] at h
      simp only [not_lt_zero'] at h
    rw [heq2, sub_self]
  . have hn := Nat.succ_pred hzero
    have heq : ∀ (i : Fin n),
      (fun j => if j < i then a j else if j = i then a j - b j else b j) =
      Function.update ((Finset.Iic i).piecewise a b) i (a i - b i) := by
      intro i; ext j
      by_cases h : j < i
      . simp only [h, ne_of_lt h, ite_false, ite_true, ne_eq, not_false_eq_true,
        Function.update_noteq, Finset.mem_Iic, le_of_lt h, Finset.piecewise_eq_of_mem]
      . by_cases h' : j = i
        . rw [h']
          simp only [lt_self_iff_false, ite_true, ite_false, Function.update_same]
        . have h'' : ¬(j ≤ i) := by
            rw [not_le, lt_iff_le_and_ne]
            rw [not_lt] at h
            exact ⟨h, Ne.symm h'⟩
          simp only [h, h', ite_false, ne_eq, not_false_eq_true, Function.update_noteq,
            Finset.mem_Iic, h'', Finset.piecewise_eq_of_not_mem]
    rw [Finset.sum_congr (Eq.refl Finset.univ) (fun i _ => by rw [heq i])]
    rw [Finset.sum_congr (Eq.refl Finset.univ) (fun i _ => by rw [MultilinearMap.map_sub f _ i])]
    have h1 : ∀ (i : Fin n), Function.update (Finset.piecewise (Finset.Iic i) a b) i (a i) =
      Finset.piecewise (Finset.Iic i) a b := by
      intro i
      ext j
      by_cases h : j ≤ i
      . simp only [ne_eq, Finset.mem_Iic, h, Finset.piecewise_eq_of_mem]
        by_cases h' : j = i
        . rw [h']
          simp only [Function.update_same]
        . simp only [ne_eq, h', not_false_eq_true, Function.update_noteq, Finset.mem_Iic, h,
          Finset.piecewise_eq_of_mem]
      . simp only [ne_eq, Ne.symm (ne_of_lt (lt_of_not_le h)), not_false_eq_true,
        Function.update_noteq, Finset.mem_Iic, h, Finset.piecewise_eq_of_not_mem]
    have h2 : ∀ (i : Fin n) (hi : i.1 ≠ 0), (Function.update (Finset.piecewise (Finset.Iic i) a b) i (b i) =
      Finset.piecewise (Finset.Iic ⟨i.1.pred, lt_trans (Nat.pred_lt hi) i.2⟩) a b) := by
      intro i hi
      ext j
      by_cases hj : j ≤ i
      . by_cases hj' : j = i
        . rw [hj']
          simp only [Function.update_same, Finset.mem_Iic, not_le]
          have h : i ∉ Finset.Iic ⟨i.1.pred, lt_trans (Nat.pred_lt hi) i.2⟩ := by
            simp only [Finset.mem_Iic, not_le]
            change Nat.pred i < i
            conv_rhs => rw [←(Nat.succ_pred hi)]
            rw [Nat.lt_succ]
          rw [Finset.piecewise_eq_of_not_mem _ _ _ h]
        . simp only [ne_eq, hj', not_false_eq_true, Function.update_noteq, Finset.mem_Iic, hj,
          Finset.piecewise_eq_of_mem, not_le]
          have hj'' : j ∈ Finset.Iic ⟨i.1.pred, lt_trans (Nat.pred_lt hi) i.2⟩ := by
            simp only [Finset.mem_Iic]
            apply Nat.le_pred_of_lt
            rw [lt_iff_le_and_ne]; erw [and_iff_right hj]
            exact fun h => hj' (Fin.eq_of_val_eq h)
          rw [Finset.piecewise_eq_of_mem _ _ _ hj'']
      . have hj' : j ≠ i := Ne.symm (ne_of_lt (lt_of_not_le hj))
        simp only [ne_eq, hj', not_false_eq_true, Function.update_noteq, Finset.mem_Iic, hj,
          Finset.piecewise_eq_of_not_mem, not_le]
        have hj'' : j ∉ Finset.Iic ⟨i.1.pred, lt_trans (Nat.pred_lt hi) i.2⟩ := by
          simp only [Finset.mem_Iic, not_le]
          apply lt_of_not_le
          exact fun h => hj (le_trans h (Nat.pred_le i.1))
        rw [Finset.piecewise_eq_of_not_mem _ _ _ hj'']
    set m₁ : Fin n := ⟨0, by rw [←hn]; exact Nat.zero_lt_succ _⟩
    have h2' : ∀ (i : Fin n), i.1 = 0 → Function.update (Finset.piecewise (Finset.Iic i) a b) i (b i) = b := by
      intro i hi
      rw [Fin.eq_of_val_eq hi (j := m₁)]
      ext j
      by_cases hj : j = m₁
      . rw [hj]
        simp only [id_eq, eq_mpr_eq_cast, Function.update_same]
      . simp only [id_eq, eq_mpr_eq_cast, ne_eq, hj, not_false_eq_true, Function.update_noteq,
        Finset.mem_Iic, not_le]
        have hj' : j ∉ Finset.Iic m₁ := by
          simp only [Finset.mem_Iic, not_le]
          rw [lt_iff_le_and_ne, and_iff_left (Ne.symm hj)]
          apply Nat.zero_le
        rw [Finset.piecewise_eq_of_not_mem _ _ _ hj']
    rw [Finset.sum_congr (Eq.refl Finset.univ) (fun i _ => by rw [h1 i]),
      Finset.sum_sub_distrib]
    set m₂ : Fin n := ⟨n.pred, by conv_rhs => rw [←hn]
                                  rw [Nat.lt_succ]⟩
    have hd1 : Disjoint (Finset.erase Finset.univ m₂) {m₂} := by
      simp only [Finset.mem_univ, not_true_eq_false, Finset.disjoint_singleton_right,
        Finset.mem_erase, ne_eq, and_true, not_false_eq_true]
    have hu1 : Finset.univ (α := Fin n) = Finset.disjUnion (Finset.erase Finset.univ m₂) {m₂} hd1:= by
      simp only [Finset.mem_univ, not_true_eq_false, Finset.disjUnion_eq_union]
      ext i
      simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_union, Finset.mem_erase, ne_eq,
        and_true, Finset.mem_singleton, true_iff]
      apply ne_or_eq
    have hd2 : Disjoint (Finset.erase Finset.univ m₁) {m₁} := by
      simp only [Finset.mem_univ, not_true_eq_false, Finset.disjoint_singleton_right,
        Finset.mem_erase, ne_eq, and_true, not_false_eq_true]
    have hu2 : Finset.univ (α := Fin n) = Finset.disjUnion (Finset.erase Finset.univ m₁) {m₁} hd2:= by
      simp only [Finset.mem_univ, not_true_eq_false, Finset.disjUnion_eq_union]
      ext i
      simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_union, Finset.mem_erase, ne_eq,
        and_true, Finset.mem_singleton, true_iff]
      apply ne_or_eq
    conv => rhs
            congr
            rw [hu1, Finset.sum_disjUnion, Finset.sum_singleton]
            rfl
            rw [hu2, Finset.sum_disjUnion, Finset.sum_singleton]
    have h : Finset.Iic m₂ = Finset.univ := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Nat.le_pred_of_lt i.2
    rw [h, Finset.piecewise_univ]
    rw [h2' m₁ rfl, ←sub_sub]
    have hmem : ∀ (i : Fin n), i ∈ Finset.erase Finset.univ m₁ → i.1 ≠ 0 := by
      intro i hi
      simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_erase, ne_eq, and_true] at hi
      by_contra h
      exact hi (Fin.eq_of_val_eq h (j := m₁))
    have hmem' : ∀ (i : Fin n), i ∈ Finset.erase Finset.univ m₂ → i.1 ≠ n.pred := by
      intro i hi
      simp only [Finset.mem_univ, not_true_eq_false, Finset.mem_erase, ne_eq, and_true] at hi
      by_contra h
      exact hi (Fin.eq_of_val_eq h (j := m₂))
    set I : (i : Fin n) → i ∈ Finset.erase Finset.univ m₁ → Fin n :=
      fun i hi => ⟨i.1.pred, lt_trans (Nat.pred_lt (hmem i hi)) i.2⟩
    have hI : ∀ (i : Fin n) (hi : i ∈ Finset.erase Finset.univ m₁), I i hi ∈ Finset.erase Finset.univ m₂ := by
      intro i hi
      simp only [id_eq, eq_mpr_eq_cast, Finset.mem_univ, not_true_eq_false, Finset.mem_erase, ne_eq,
        Fin.mk.injEq, and_true]
      by_contra h
      apply_fun Nat.succ at h
      rw [hn, Nat.succ_pred (hmem i hi)] at h
      exact ne_of_lt i.2 h
    have hIinj : ∀ (i j : Fin n) (hi : i ∈ Finset.erase Finset.univ m₁) (hj : j ∈ Finset.erase Finset.univ m₁),
      I i hi = I j hj → i = j := by
      intro i j hi hj hij
      simp only [id_eq, eq_mpr_eq_cast, Fin.mk.injEq] at hij
      apply_fun Nat.succ at hij
      rw [Nat.succ_pred (hmem i hi), Nat.succ_pred (hmem j hj)] at hij
      exact Fin.eq_of_val_eq hij
    have hIsurj : ∀ j ∈ Finset.erase Finset.univ m₂, ∃ (i : Fin n) (hi : i ∈ Finset.erase Finset.univ m₁),
      j = I i hi := by
      intro j hj
      have hj' : Nat.succ j.1 < n := by
        conv => rhs; rw [←hn]
        rw [Nat.succ_lt_succ_iff, lt_iff_le_and_ne, and_iff_left (hmem' j hj)]
        exact Nat.le_pred_of_lt j.2
      existsi ⟨j.succ, hj'⟩
      simp only [Fin.val_succ, id_eq, eq_mpr_eq_cast, Nat.pred_succ, Fin.eta, Finset.mem_univ,
        not_true_eq_false, Finset.mem_erase, ne_eq, Fin.mk.injEq, add_eq_zero, one_ne_zero,
        and_false, not_false_eq_true, and_self, exists_const]
    have hIeq : ∀ (i : Fin n) (hi : i ∈ Finset.erase Finset.univ m₁),
      f (Function.update (Finset.piecewise (Finset.Iic i) a b) i (b i)) =
      f (Finset.piecewise (Finset.Iic (I i hi)) a b) := by
      intro i hi
      rw [h2 i (hmem i hi)]
    rw [Finset.sum_bij I hI hIeq hIinj hIsurj (g := fun j => f (Finset.piecewise (Finset.Iic j) a b))]
    conv => rhs
            rw [add_comm, ←add_sub, sub_self, add_zero]





def MultilinearMap.restr_gen (f : MultilinearMap 𝕜 E F) : 0 = 0 := sorry


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




theorem hasStrictFDerivAt (f : ContinuousMultilinearMap 𝕜 E F) (x : (i : ι) → E i)  :
    HasStrictFDerivAt f (f.deriv x) x := by sorry

#exit

theorem ContinuousMultilinearMap.contDiff {𝕜 : Type*} {ι : Type*} [Fintype ι] {E : ι → Type*} {F : Type*}
[NontriviallyNormedField 𝕜] [(i : ι) → NormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
[NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞} (M : ContinuousMultilinearMap 𝕜 E F) :
ContDiff 𝕜 n M.toFun := sorry
