import Mathlib.Tactic
import Mathlib.LinearAlgebra.Multilinear.Basic

open BigOperators

namespace MultilinearMap


variable {R : Type uR} [Semiring R]  {ι : Type uι} {M : ι → Type v} {N : Type w}
[∀ (i : ι), AddCommGroup (M i)] [AddCommGroup N] [∀ (i : ι), Module R (M i)]
[Module R N] [DecidableEq ι]

/-
lemma apply_sub [LinearOrder ι]
(f : MultilinearMap R M N) (a b v : (i : ι) → (M i)) {s : Finset ι}
(hs : Finset.card s = n) :
f (s.piecewise a v) - f (s.piecewise b v) = Finset.sum Finset.univ (fun (i : Fin n) =>
f (fun j => if h : j ∈ s then (if (s.orderIsoOfFin hs).symm ⟨j, h⟩ < i then a j
else if (s.orderIsoOfFin hs).symm ⟨j, h⟩ = i then a j - b j else b j) else v j)) := by
  by_cases hn : n = 0
  . have h : IsEmpty (Fin n) := by rw [← Fintype.card_eq_zero_iff, hn]; exact Fintype.card_fin 0
    have he : Finset.univ (α := Fin n) = ∅ := Finset.univ_eq_empty_iff.mpr h
    have heq : s.piecewise a v = s.piecewise b v := by
      rw [hn, Finset.card_eq_zero] at hs
      rw [hs, Finset.piecewise_empty, Finset.piecewise_empty]
    rw [he, Finset.sum_empty, heq, sub_self]
  . have hn := Nat.succ_pred hn
    have heq : ∀ (i : Fin n), (fun j => if h : j ∈ s then
        (if (s.orderIsoOfFin hs).symm ⟨j, h⟩ < i then a j else
        if (s.orderIsoOfFin hs).symm ⟨j, h⟩ = i then a j - b j else b j) else v j) =
        Function.update (fun j => if h : j ∈ s then
        (if (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ i then a j else b j) else v j)
        ((s.orderIsoOfFin hs) i)
        (a (s.orderIsoOfFin hs i) - b (s.orderIsoOfFin hs i)) := by
      intro i
      ext j
      by_cases h : j ∈ s
      . simp only [h, dite_true]
        by_cases h' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ < i
        . simp only [h', ite_true]
          have h'' : j ≠ s.orderIsoOfFin hs i := by
            by_contra habs
            have habs' : ⟨j, h⟩ = s.orderIsoOfFin hs i := by
              rw [← SetCoe.ext_iff]
              simp only [habs]
            rw [habs'] at h'
            simp only [OrderIso.symm_apply_apply, lt_self_iff_false] at h'
          rw [Function.update_noteq h'']
          simp only [h, le_of_lt h', ite_true, dite_eq_ite]
        . simp only [h', ite_false]
          by_cases h'' : j = s.orderIsoOfFin hs i
          . have h''' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ = i := by
              have haux : ⟨j, h⟩ = s.orderIsoOfFin hs i := by
                rw [← SetCoe.ext_iff]
                simp only
                exact h''
              rw [haux]
              simp only [OrderIso.symm_apply_apply]
            simp only [h''', ite_true, Finset.coe_orderIsoOfFin_apply, ne_eq]
            rw [h'']
            erw [Function.update_same]
            rfl
          . rw [Function.update_noteq h'']
            simp only [h, dite_true]
            have h''' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≠ i := by
              by_contra habs
              rw [← habs] at h''
              simp only [OrderIso.apply_symm_apply, not_true_eq_false] at h''
            have h'''' : ¬((s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ i) := by
              rw [← lt_iff_not_le, lt_iff_le_and_ne]
              rw [lt_iff_not_le, not_not] at h'
              exact ⟨h', Ne.symm h'''⟩
            simp only [h''', ite_false, h'''']
      . have h' : j ≠ s.orderIsoOfFin hs i := by
          by_contra habs
          rw [habs] at h
          simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_mem, not_true_eq_false] at h
        rw [Function.update_noteq h']
        simp only [h, dite_false]
    rw [Finset.sum_congr (Eq.refl Finset.univ) (fun i _ => by rw [heq i]),
      Finset.sum_congr (Eq.refl Finset.univ) (fun i _ => by rw [MultilinearMap.map_sub f]),
      Finset.sum_sub_distrib]
    set m₁ : Fin n := ⟨0, by rw [← hn]; exact Nat.zero_lt_succ _⟩
    set m₂ : Fin n := ⟨n.pred, by conv_rhs => rw [← hn]
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
    have h1 : (Function.update (fun j => if h : j ∈ s then
        if (OrderIso.symm (Finset.orderIsoOfFin s hs)) ⟨j, h⟩ ≤ m₂ then a j else b j
        else v j)
        (((Finset.orderIsoOfFin s hs) m₂)) (a ((Finset.orderIsoOfFin s hs) m₂))) =
        s.piecewise a v := by
      ext j
      by_cases h : j ∈ s
      . simp only [h, Finset.piecewise_eq_of_mem]
        by_cases h' : j = s.orderIsoOfFin hs m₂
        . rw [h', Function.update_same]
        . rw [Function.update_noteq h']
          simp only [h, dite_true]
          have h'' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ m₂ := by
            apply Nat.le_pred_of_lt
            exact ((s.orderIsoOfFin hs).symm ⟨j, h⟩).2
          simp only [h'', ite_true]
      . simp only [h, not_false_eq_true, Finset.piecewise_eq_of_not_mem]
        have h' : j ≠ s.orderIsoOfFin hs m₂ := by
          by_contra habs
          rw [habs] at h
          simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_mem, not_true_eq_false] at h
        rw [Function.update_noteq h']
        simp only [h, dite_false]
    have h2 : (Function.update (fun j => if h : j ∈ s then
        if (OrderIso.symm (Finset.orderIsoOfFin s hs)) ⟨j, h⟩ ≤ m₁ then a j else b j else v j)
        (((Finset.orderIsoOfFin s hs) m₁)) (b ↑((Finset.orderIsoOfFin s hs) m₁))) = s.piecewise b v := by
      ext j
      by_cases h : j ∈ s
      . simp only [h, Finset.piecewise_eq_of_mem]
        by_cases h' : j = s.orderIsoOfFin hs m₁
        . rw [h', Function.update_same]
        . rw [Function.update_noteq h']
          simp only [h, dite_true]
          have h'' : ¬ (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ m₁ := by
            simp only [not_le]
            apply Nat.zero_lt_of_ne_zero
            by_contra habs
            have habs' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ = m₁ := Fin.eq_of_val_eq habs
            rw [← habs', OrderIso.apply_symm_apply] at h'
            simp only [not_true_eq_false] at h'
          simp only [h'', ite_false]
      . have h' : j ≠ s.orderIsoOfFin hs m₁ := by
          by_contra habs
          rw [habs] at h
          simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_mem, not_true_eq_false] at h
        rw [Function.update_noteq h']
        simp only [h, dite_false, not_false_eq_true, Finset.piecewise_eq_of_not_mem]
    rw [h1, h2]
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
        conv => rhs; rw [← hn]
        rw [Nat.succ_lt_succ_iff, lt_iff_le_and_ne, and_iff_left (hmem' j hj)]
        exact Nat.le_pred_of_lt j.2
      existsi ⟨j.succ, hj'⟩
      simp only [Fin.val_succ, id_eq, eq_mpr_eq_cast, Nat.pred_succ, Fin.eta, Finset.mem_univ,
        not_true_eq_false, Finset.mem_erase, ne_eq, Fin.mk.injEq, add_eq_zero, one_ne_zero,
        and_false, not_false_eq_true, and_self, exists_const]
    have hIeq : ∀ (i : Fin n) (hi : i ∈ Finset.erase Finset.univ m₁),
        f (Function.update (fun j => if h : j ∈ s then
        if (OrderIso.symm (Finset.orderIsoOfFin s hs)) ⟨j, h⟩ ≤ i then a j else b j
        else v j)
        (((Finset.orderIsoOfFin s hs) i)) (b ((Finset.orderIsoOfFin s hs) i))) =
        f (Function.update (fun j => if h : j ∈ s then
        if (OrderIso.symm (Finset.orderIsoOfFin s hs)) ⟨j, h⟩ ≤ (I i hi) then a j else b j
        else v j)
        (((Finset.orderIsoOfFin s hs) (I i hi))) (a ((Finset.orderIsoOfFin s hs) (I i hi)))) := by
      intro i hi
      congr
      ext j
      by_cases h : j ∈ s
      . by_cases h' : j = s.orderIsoOfFin hs i
        . have h'' : j ≠ s.orderIsoOfFin hs (I i hi) := by
            by_contra habs
            rw [h'] at habs
            simp only [Finset.coe_orderIsoOfFin_apply, id_eq, eq_mpr_eq_cast, RelEmbedding.inj] at habs
            apply_fun fun x => x.1 at habs
            simp only at habs
            exact Nat.pred_ne_self (hmem i hi) (Eq.symm habs)
          rw [Function.update_noteq h'']
          simp only [h, id_eq, eq_mpr_eq_cast, dite_true]
          have h''' : ¬ (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ I i hi := by
            rw [← lt_iff_not_le]
            simp_rw [h']
            change Nat.pred i < _
            rw [OrderIso.symm_apply_apply, lt_iff_le_and_ne]
            exact ⟨Nat.pred_le _, Nat.pred_ne_self (hmem i hi)⟩
          simp only [h''', ite_false]
          rw [h', Function.update_same]
        . rw [Function.update_noteq h']
          simp only [h, dite_true]
          by_cases h'' : j = s.orderIsoOfFin hs (I i hi)
          . have h''' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ (I i hi) := by
              rw [OrderIso.symm_apply_le]
              change j ≤ _
              rw [h'']
            have h'''' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ i := by
              apply le_trans h'''
              simp only [id_eq, eq_mpr_eq_cast]
              exact Nat.pred_le _
            simp only [h'''', ite_true]
            rw [h'', Function.update_same]
          . rw [Function.update_noteq h'']
            simp only [h, dite_true]
            by_cases h''' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ i
            . simp only [h''', ite_true]
              have h'''' : (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ I i hi := by
                apply Nat.le_pred_of_lt
                rw [lt_iff_le_and_ne]
                erw [and_iff_right h''']
                by_contra habs
                rw [← (Fin.eq_of_val_eq habs)] at h'
                simp only [OrderIso.apply_symm_apply, not_true_eq_false] at h'
              simp only [h'''', ite_true]
            . simp only [h''', ite_false]
              have h'''' : ¬ (s.orderIsoOfFin hs).symm ⟨j, h⟩ ≤ I i hi :=
                fun habs => h''' (le_trans habs (Nat.pred_le _))
              simp only [h'''', ite_false]
      . have h' : ∀ (r : Fin n), j ≠ s.orderIsoOfFin hs r := by
          intro r
          by_contra habs
          rw [habs] at h
          simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_mem, not_true_eq_false] at h
        rw [Function.update_noteq (h' i), Function.update_noteq (h' (I i hi))]
        simp only [h, dite_false, id_eq, eq_mpr_eq_cast]
    rw [Finset.sum_bij I hI hIeq hIinj hIsurj
      (g := fun i => f (Function.update (fun j => if h : j ∈ s then
      if (OrderIso.symm (Finset.orderIsoOfFin s hs)) ⟨j, h⟩ ≤ i then a j else b j
      else v j)
      (((Finset.orderIsoOfFin s hs) i)) (a ((Finset.orderIsoOfFin s hs) i))))]
    simp only [Finset.mem_univ, not_true_eq_false, Finset.coe_orderIsoOfFin_apply,
      Finset.sum_erase_eq_sub, id_eq, eq_mpr_eq_cast, add_sub_add_left_eq_sub]
-/


/-! The goal of this part is, for `f` a multilinear map in finitely many variables indexed by `ι`,
to develop `f(x + y)` as a finite formal multilinear series in `y`. The nth term of this formal multilinear
series will be a sum over finsets `s` of `ι` of cardinality `n` of a multilinear map indexed by `s`,
evaluated at `fun (_ : s) => y`. So we start by introducing the individual terms indexed by finsets of
`ι`; actually, for the definition, we can consider any sets of `ι` and we don't need to take `ι` finite.-/

def toMultilinearMap_set (f : MultilinearMap R M N) (x : (i : ι) → M i) (s : Set ι)
[(i : ι) → Decidable (i ∈ s)] :
MultilinearMap R (fun (_ : s) => (i : ι) → M i) N where
toFun z := f (fun i => if h : i ∈ s then z ⟨i, h⟩ i else x i)
map_add' z i a b := by
  have heq : ∀ (c : (i : ι) → M i),
      (fun j ↦ if h : j ∈ s then Function.update z i c ⟨j, h⟩ j else x j) =
      Function.update (fun j => if h : j ∈ s then z ⟨j, h⟩ j else x j) i (c i.1) := by
    intro c; ext j
    by_cases h : j ∈ s
    . simp only [h, ne_eq, dite_true]
      by_cases h' : ⟨j, h⟩ = i
      . rw [h', Function.update_same]
        have h'' : j = i.1 := by apply_fun (fun k => k.1) at h'; simp only at h'; exact h'
        rw [h'', Function.update_same]
      . have h'' : j ≠ i.1 := by
          rw [← SetCoe.ext_iff] at h'
          exact h'
        rw [Function.update_noteq h', Function.update_noteq h'']
        simp only [h, dite_true]
    . have h' : j ≠ i.1 := by
        by_contra habs
        rw [habs] at h
        simp only [Subtype.coe_prop, not_true_eq_false] at h
      rw [Function.update_noteq h']
      simp only [h, ne_eq, dite_false]
  simp only
  rw [heq a, heq b, heq (a + b)]
  simp only [Pi.add_apply, MultilinearMap.map_add]
map_smul' z i c a := by
-- This is copy-pasted code from the proof of map_add'. If I try to make it an outside lemma, rw refuses to
-- take it for some reason.
  have heq : ∀ (c : (i : ι) → M i),
      (fun j ↦ if h : j ∈ s then Function.update z i c ⟨j, h⟩ j else x j) =
      Function.update (fun j => if h : j ∈ s then z ⟨j, h⟩ j else x j) i (c i.1) := by
    intro c; ext j
    by_cases h : j ∈ s
    . simp only [h, ne_eq, dite_true]
      by_cases h' : ⟨j, h⟩ = i
      . rw [h', Function.update_same]
        have h'' : j = i.1 := by apply_fun (fun k => k.1) at h'; simp only at h'; exact h'
        rw [h'', Function.update_same]
      . have h'' : j ≠ i.1 := by
          rw [← SetCoe.ext_iff] at h'
          exact h'
        rw [Function.update_noteq h', Function.update_noteq h'']
        simp only [h, dite_true]
    . have h' : j ≠ i.1 := by
        by_contra habs
        rw [habs] at h
        simp only [Subtype.coe_prop, not_true_eq_false] at h
      rw [Function.update_noteq h']
      simp only [h, ne_eq, dite_false]
  simp only
  rw [heq a, heq]
  simp only [Pi.smul_apply, MultilinearMap.map_smul]

@[simp]
lemma toMultilinearMap_set_apply (f : MultilinearMap R M N)
(x : (i : ι) → M i) (s : Set ι) [(i : ι) → Decidable (i ∈ s)]
(z : (_ : s) → ((i : ι) → M i)) :
f.toMultilinearMap_set x s z = f (fun i => if h : i ∈ s then z ⟨i, h⟩ i else x i) := by
  unfold toMultilinearMap_set
  rfl

lemma toMultilinearMap_set_apply_diag (f : MultilinearMap R M N)
(x : (i : ι) → M i) (s : Set ι) [(i : ι) → Decidable (i ∈ s)] (y : (i : ι) → M i) :
f.toMultilinearMap_set x s (fun (_ : s) => y) = f (s.piecewise y x) := by
  unfold toMultilinearMap_set
  simp only [coe_mk, dite_eq_ite]
  congr

variable [Fintype ι]

/-- This is the nth term of the formal multilinear series corresponding to the multilinear map `f`.
We need a linear order on ι to identify all finsets of `ι` of cardinality `n` to `Fin n`.-/
def toFormalMultilinearSeries_fixedDegree [LinearOrder ι]
    (f : MultilinearMap R M N) (x : (i : ι) → M i) (n : ℕ) :
    MultilinearMap R (fun (_ : Fin n) => (i : ι) → M i) N :=
  (∑ s : {s : Finset ι | s.card = n},
  (f.toMultilinearMap_set x s.1.toSet).domDomCongr (s.1.orderIsoOfFin s.2).symm.toEquiv)

@[simp]
lemma toFormalMultilinearSeries_fixedDegree_apply_diag [LinearOrder ι]
    (f : MultilinearMap R M N) (x y : (i : ι) → M i) (n : ℕ) :
    f.toFormalMultilinearSeries_fixedDegree x n (fun _ => y) = (∑ s : {s : Finset ι | s.card = n},
    f (s.1.piecewise y x)) := by
  unfold toFormalMultilinearSeries_fixedDegree
  simp only [Set.coe_setOf, Set.mem_setOf_eq, coe_sum, Finset.sum_apply, domDomCongr_apply]
  apply Finset.sum_congr rfl
  intro s _
  erw [f.toMultilinearMap_set_apply_diag x s.1 y]

/-- The nth term of the formal multilinear series of `f` vanishes if `n` is bigger than `Fintype.vard ι`
(because there are no finsets of `ι` of cardinality `n`).-/
lemma toFormalMultilinearSeriest_fixedDegree_zero [LinearOrder ι]
    (f : MultilinearMap R M N) (x : (i : ι) → M i) {n : ℕ} (hn : (Fintype.card ι).succ ≤ n) :
    f.toFormalMultilinearSeries_fixedDegree x n = 0 := by
    unfold toFormalMultilinearSeries_fixedDegree
    have he : IsEmpty {s : Finset ι | s.card = n} := by
      by_contra hne
      simp only [Set.coe_setOf, isEmpty_subtype, not_forall, not_not] at hne
      have h : (Fintype.card ι).succ < (Fintype.card ι).succ :=
        calc
          (Fintype.card ι).succ ≤ n := hn
          _ = (Classical.choose hne).card := Eq.symm (Classical.choose_spec hne)
          _ ≤ Fintype.card ι := Finset.card_le_univ _
          _ < (Fintype.card ι).succ := Nat.lt_succ_self _
      exact lt_irrefl _ h
    rw [Finset.univ_eq_empty_iff.mpr he, Finset.sum_empty]

/-- Expression of `f(x + y)` using the formal multilinear series of `f` at `x`, as a finite sum.-/
lemma hasFiniteFPowerSeries [LinearOrder ι]
    (f : MultilinearMap R M N) (x y : (i : ι) → M i) :
    f (x + y) = ∑ n : Finset.range (Fintype.card ι).succ,
    f.toFormalMultilinearSeries_fixedDegree x n (fun (_ : Fin n) => y) := by
  rw [add_comm, map_add_univ, ← (Finset.sum_fiberwise_of_maps_to (g := fun s => s.card)
    (t := Finset.range (Fintype.card ι).succ))]
  simp only [Finset.mem_univ, forall_true_left, Finset.univ_filter_card_eq, gt_iff_lt]
  rw [Finset.sum_coe_sort _ (fun n => f.toFormalMultilinearSeries_fixedDegree x n (fun _ => y))]
  apply Finset.sum_congr rfl
  . intro n hn
    simp only [Finset.mem_range] at hn
    rw [toFormalMultilinearSeries_fixedDegree_apply_diag]
    simp only [gt_iff_lt, Set.coe_setOf, Set.mem_setOf_eq]
    rw [Finset.sum_subtype (f := fun (s : Finset ι) => f (s.piecewise y x))]
    exact fun s => by simp only [Finset.mem_powersetCard_univ]
  . intro s _
    simp only [Finset.mem_range]
    rw [Nat.lt_succ]
    exact Finset.card_le_univ _


noncomputable def linearDeriv (f : MultilinearMap R M N)
(x : (i : ι) → M i) : ((i : ι) → M i) →ₗ[R] N :=
Finset.sum Finset.univ (fun (i : ι) => (f.toLinearMap x i).comp (LinearMap.proj i))

@[simp]
lemma linearDeriv_apply (f : MultilinearMap R M N)
(x y : (i : ι) → M i) :
  f.linearDeriv x y = Finset.sum Finset.univ (fun (i : ι) => f (Function.update x i (y i))) := by
  unfold linearDeriv
  simp only [LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

lemma linearDerive_eq_toFormalMultilinearSeries_degreeOne [LinearOrder ι]
    (f : MultilinearMap R M N) (x : (i : ι) → M i) :
    MultilinearMap.ofSubsingleton (ι := Fin 1) R ((i : ι) → M i) N (⟨0, Nat.zero_lt_one⟩ : Fin 1)
    (f.linearDeriv x) = f.toFormalMultilinearSeries_fixedDegree x 1 := by
  ext y
  have heq : y = fun _ => y 0 := by ext i; rw [Subsingleton.elim i]
  rw [heq]
  simp only [Fin.zero_eta, ofSubsingleton_apply_apply, linearDeriv_apply,
    toFormalMultilinearSeries_fixedDegree_apply_diag, Set.coe_setOf, Set.mem_setOf_eq]
  set I : (i : ι) → i ∈ Finset.univ → {s : Finset ι // s.card = 1} :=
    fun i _ => ⟨{i}, Finset.card_singleton _⟩
  have hI : ∀ (i : ι) (hi : i ∈ Finset.univ), I i hi ∈ Finset.univ := fun _ _ => Finset.mem_univ _
  have heq : ∀ (i : ι) (hi : i ∈ Finset.univ),
      f (Function.update x i (y 0 i)) = f ((I i hi).1.piecewise (y 0) x) :=
    fun _ _ => by rw [Finset.piecewise_singleton]
  have hinj : ∀ (i j : ι) (hi : i ∈ Finset.univ) (hj : j ∈ Finset.univ), I i hi = I j hj → i = j :=
    fun _ _ _ _ => by simp only [Subtype.mk.injEq, Finset.singleton_inj, imp_self]
  have hsurj : ∀ s ∈ Finset.univ (α := {s : Finset ι // s.card = 1}), ∃ (i : ι) (hi : i ∈ Finset.univ),
      I i hi = s := by
    intro ⟨s, hs⟩ _
    rw [Finset.card_eq_one] at hs
    existsi Classical.choose hs
    existsi Finset.mem_univ _
    simp only [Subtype.mk.injEq]
    exact Eq.symm (Classical.choose_spec hs)
  rw [Finset.sum_bij I hI (fun i hi j hj ↦ hinj i j hi hj) hsurj heq (g := fun s => f (s.1.piecewise (y 0) x))]

lemma sub_vs_linearDeriv (f : MultilinearMap R M N) (x h h' : (i : ι) → M i) :
    f (x + h) - f (x + h') - f.linearDeriv x (h - h') = Finset.sum
    (Set.Finite.toFinset ((Set.finite_coe_iff (s := {s : Finset ι | 2 ≤ s.card})).mp inferInstance))
    (fun (s : Finset ι) => f (s.piecewise h x) - f (s.piecewise h' x)) := by
  rw [add_comm x h, add_comm x h', MultilinearMap.map_add_univ, MultilinearMap.map_add_univ,
    linearDeriv_apply, ← Finset.sum_sub_distrib, ← (Finset.sum_compl_add_sum
    (Set.Finite.toFinset ((Set.finite_coe_iff (s := {s : Finset ι | 2 ≤ s.card})).mp inferInstance))),
    add_comm, ← add_sub, add_right_eq_self]
  set S := (Set.Finite.toFinset ((Set.finite_coe_iff (s := {s : Finset ι | 2 ≤ s.card})).mp inferInstance))ᶜ
  have hS : ∀ (s : Finset ι), s ∈ S ↔ s.card ≤ 1 := by
    intro s
    simp only [Set.Finite.toFinset_setOf, Finset.mem_univ, forall_true_left, not_le,
      Finset.compl_filter, not_lt, Finset.mem_filter, true_and]
    rw [Nat.lt_succ_iff]
  have heS : ∅ ∈ S := by rw [hS]; simp only [Finset.card_empty, zero_le]
  have hS' : ∀ (s : Finset ι), s ∈ S.erase ∅ ↔ s.card = 1 := by
    intro s
    rw [Finset.mem_erase, hS, Nat.le_one_iff_eq_zero_or_eq_one, Finset.card_eq_zero]
    aesop
  rw [← (Finset.sum_erase_add _ _ heS), Finset.piecewise_empty, Finset.piecewise_empty, sub_self, add_zero]
  set I : (s : Finset ι) → (s ∈ S.erase ∅) → ι :=
    fun s hs => by rw [hS' s, Finset.card_eq_one] at hs
                   exact Classical.choose hs
  have hI : ∀ (s : Finset ι) (hs : s ∈ S.erase ∅), I s hs ∈ Finset.univ :=
    fun _ _ => Finset.mem_univ _
  have heq : ∀ (s : Finset ι) (hs : s ∈ S.erase ∅), f (s.piecewise h x) - f (s.piecewise h' x) =
      f (Function.update x (I s hs) ((h - h') (I s hs))) := by
    intro s hs
    rw [hS', Finset.card_eq_one] at hs
    conv => lhs
            rw [Classical.choose_spec hs, Finset.piecewise_singleton,
              Finset.piecewise_singleton, ← MultilinearMap.map_sub]
  set J : (i : ι) → (i ∈ Finset.univ) → Finset ι := fun i _ => {i}
  have hJ : ∀ (i : ι) (hi : i ∈ Finset.univ), J i hi ∈ S.erase ∅ :=
    fun _ _ => by rw [hS']; exact Finset.card_singleton _
  have hJI : ∀ (s : Finset ι) (hs : s ∈ S.erase ∅), J (I s hs) (hI s hs) = s := by
    intro s hs
    simp only [Set.coe_setOf, Set.mem_setOf_eq]
    rw [hS', Finset.card_eq_one] at hs
    exact Eq.symm (Classical.choose_spec hs)
  have hIJ : ∀ (i : ι) (hi : i ∈ Finset.univ), I (J i hi) (hJ i hi) = i := by
    intro i hi; apply Eq.symm; rw [← Finset.mem_singleton]
    have hs := hJ i hi
    rw [hS', Finset.card_eq_one] at hs
    change i ∈ {Classical.choose hs}
    rw [← (Classical.choose_spec hs)]
    simp only [Finset.mem_singleton]
  rw [Finset.sum_bij' I J hI hJ hJI hIJ heq (g := fun i => f (Function.update x i ((h - h') i))),
    sub_self]


end MultilinearMap
