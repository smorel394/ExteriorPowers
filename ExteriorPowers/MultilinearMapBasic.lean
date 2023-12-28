import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Multilinear.Basic


section Derivative

open Function Fin Set BigOperators

universe uR uS uι v v' v₁ v₂ v₃

variable {R : Type uR} [Semiring R] {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}
  [∀ (i : ι), AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ (i : ι), Module R (M₁ i)]
  [Module R M₂]

namespace MultilinearMap


/-! The goal of this part is, for `f` a multilinear map in finitely many variables indexed by `ι`,
to develop `f(x + y)` as a finite formal multilinear series in `y`. The term of degree `n` of
this formal multilinear series will be a sum over finsets `s` of `ι` of cardinality `n` of a
multilinear map indexed by `s`, evaluated at `fun (_ : s) => y`; we use a linear order on
`ι` to identify all such `s` to `Fin n`. We also give a more direct definition of the term
of degree `1` in `f.linearDeriv`, which doesn't require a linear order on `ι`, and prove the
equivalence of the two definitions.-/

lemma domDomRestrict_aux [DecidableEq ι] (s : Set ι) [(i : ι) → Decidable (i ∈ s)]
    [DecidableEq s] (x : (i : s.compl)→ M₁ i) (z : (i : s) → M₁ i) (i : s)
    (c : M₁ i) : (fun j ↦ if h : j ∈ s then Function.update z i c ⟨j, h⟩ else x ⟨j, h⟩) =
    Function.update (fun j => if h : j ∈ s then z ⟨j, h⟩ else x ⟨j, h⟩) i c := by
  ext j
  by_cases h : j = i.1
  · rw [h, Function.update_same]
    simp only [Subtype.coe_prop, update_same, dite_true]
  · rw [Function.update_noteq h]
    by_cases h' : j ∈ s
    · simp only [h', ne_eq, dite_true]
      have h'' : ¬ ⟨j, h'⟩ = i :=
        fun he => by apply_fun (fun x => x.1) at he; exact h he
      rw [Function.update_noteq h'']
    · simp only [h', ne_eq, dite_false]

/-- Given a multilinear map `f` on `(i : ι) → M i`, an element `x` of `(i : ι) → M i` and s
set `s` of `ι`, construct a multilinear map on `s → ((i : ι) → Mi)` whose value at `z`
is `f` evaluated at the vector with `i`th coordinate `z i` if `i ∈ s` and `x i` otherwise.-/

def domDomRestrict [DecidableEq ι] (f : MultilinearMap R M₁ M₂)
    (s : Set ι) [(i : ι) → Decidable (i ∈ s)] (x : (i : s.compl) → M₁ i) :
    MultilinearMap R (fun (i : s) => M₁ i) M₂ where
  toFun z := f (fun i ↦ if h : i ∈ s then z ⟨i, h⟩ else x ⟨i, h⟩)
  map_add' z i a b := by
    simp only
    repeat (rw [domDomRestrict_aux])
    simp only [Pi.add_apply, MultilinearMap.map_add]
  map_smul' z i c a := by
    simp only
    repeat (rw [domDomRestrict_aux])
    simp only [Pi.smul_apply, MultilinearMap.map_smul]

--variable [Fintype ι][DecidableEq ι]

--example (s : Finset ι) (i : sᶜ) : 0 = 0 := sorry

@[simp]
lemma domDomRestrict_apply [DecidableEq ι] (f : MultilinearMap R M₁ M₂)
    (s : Set ι) [(i : ι) → Decidable (i ∈ s)]
    (x : (i : s.compl) → M₁ i) (z : (i : s) → M₁ i) :
    f.domDomRestrict s x z = f (fun i => if h : i ∈ s then z ⟨i, h⟩ else x ⟨i, h⟩) := rfl

open Finset in
/-- This is the nth term of a formal multilinear series corresponding to the multilinear map `f`.
We use a linear order on ι to identify all finsets of `ι` of cardinality `n` to `Fin n`.-/
def toFormalMultilinearSeries_fixedDegree [DecidableEq ι] [Fintype ι] [LinearOrder ι]
    (f : MultilinearMap R M₁ M₂) (x : (i : ι) → M₁ i) (n : ℕ) :
    MultilinearMap R (fun (_ : Fin n) => (i : ι) → M₁ i) M₂ :=
  ∑ s : univ.powersetCard n,
   ((f.domDomRestrict s.1.toSet (fun i => x i.1)).compLinearMap (fun (i : s.1) => LinearMap.proj
  i (φ := M₁))).domDomCongr (s.1.orderIsoOfFin (mem_powersetCard.mp s.2).2).symm.toEquiv

open Finset in
@[simp]
lemma toFormalMultilinearSeries_fixedDegree_apply_diag [DecidableEq ι] [Fintype ι] [LinearOrder ι]
    (f : MultilinearMap R M₁ M₂) (x y : (i : ι) → M₁ i) (n : ℕ) :
    f.toFormalMultilinearSeries_fixedDegree x n (fun _ => y) =
    (∑ s : univ.powersetCard n, f (s.1.piecewise y x)) := by
  unfold toFormalMultilinearSeries_fixedDegree
  simp only [coe_sort_coe, coe_sum, Finset.sum_apply, domDomCongr_apply,
    compLinearMap_apply, LinearMap.coe_proj, eval]
  apply Finset.sum_congr rfl (fun _ _ => by erw [domDomRestrict_apply])

/-- The nth term of the formal multilinear series of `f` vanishes if `n` is bigger than
`Fintype.card ι` (because there are no finsets of `ι` of cardinality `n`).-/
lemma toFormalMultilinearSeriest_fixedDegree_zero [DecidableEq ι] [Fintype ι] [LinearOrder ι]
    (f : MultilinearMap R M₁ M₂) (x : (i : ι) → M₁ i) {n : ℕ} (hn : (Fintype.card ι).succ ≤ n) :
    f.toFormalMultilinearSeries_fixedDegree x n = 0 := by
  unfold toFormalMultilinearSeries_fixedDegree
  convert Finset.sum_empty
  rw [Finset.univ_eq_empty_iff, Finset.isEmpty_coe_sort]
  apply Finset.powersetCard_empty
  rw [Finset.card_univ]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hn

/-- Expression of `f(x + y)` using the formal multilinear series of `f` at `x`, as a finite sum.-/
lemma toFormalMultilinearSeries_partialSum [DecidableEq ι] [Fintype ι] [LinearOrder ι]
    (f : MultilinearMap R M₁ M₂) (x y : (i : ι) → M₁ i) :
    f (x + y) = ∑ n in Finset.range (Fintype.card ι).succ,
    f.toFormalMultilinearSeries_fixedDegree x n (fun (_ : Fin n) => y) := by
  rw [add_comm, map_add_univ, ← (Finset.sum_fiberwise_of_maps_to (g := fun s => s.card)
    (t := Finset.range (Fintype.card ι).succ) fun s _ =>
    by rw [Finset.mem_range, Nat.lt_succ]; exact Finset.card_le_univ _)]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_range] at hn
  rw [toFormalMultilinearSeries_fixedDegree_apply_diag]
  rw [Finset.sum_subtype (f := fun (s : Finset ι) => f (s.piecewise y x))]
  exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.univ_filter_card_eq,
    gt_iff_lt, Finset.mem_powersetCard_univ, Finset.powerset_univ]


/-- The "derivative" of a multilinear map, as a linear map from `(i : ι) → M₁` to `M₂`.
For continuous multilinear maps, this will indeed be the derivative. This is equal to the degree
one part of the formal multilinear series defined by `f`, but we don't need a linear order on `ι`
to define it.-/
def linearDeriv [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x : (i : ι) → M₁ i) : ((i : ι) → M₁ i) →ₗ[R] M₂ :=
  ∑ i : ι, (f.toLinearMap x i).comp (LinearMap.proj i)

@[simp]
lemma linearDeriv_apply [DecidableEq ι] [Fintype ι] (f : MultilinearMap R M₁ M₂)
    (x y : (i : ι) → M₁ i) :
    f.linearDeriv x y = ∑ i, f (update x i (y i)) := by
  unfold linearDeriv
  simp only [LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, toLinearMap_apply]

/-- The equality between the derivarive of `f` and the degree one part of its formal
multilinear series.-/
lemma linearDeriv_eq_toFormalMultilinearSeries_degreeOne
    [DecidableEq ι] [Fintype ι] [LinearOrder ι]
    (f : MultilinearMap R M₁ M₂) (x : (i : ι) → M₁ i) :
    MultilinearMap.ofSubsingleton (ι := Fin 1) R ((i : ι) → M₁ i) M₂ (⟨0, Nat.zero_lt_one⟩ : Fin 1)
    (f.linearDeriv x) = f.toFormalMultilinearSeries_fixedDegree x 1 := by
  ext y
  rw [eq_const_of_subsingleton y 0, ← Function.const_def]
  simp only [zero_eta, ofSubsingleton_apply_apply, linearDeriv_apply,
    toFormalMultilinearSeries_fixedDegree_apply_diag]
  rw [Finset.sum_coe_sort _ (fun (s : Finset ι) => f (s.piecewise (y 0) x))]
  set I : (i : ι) → i ∈ Finset.univ → Finset ι := fun i _ => {i}
  rw [Finset.sum_bij I]
  · exact fun _ _ ↦ by simp only [Finset.powerset_univ, Finset.mem_univ, forall_true_left,
    Finset.univ_filter_card_eq, gt_iff_lt, Nat.lt_one_iff, Finset.card_eq_zero,
    Finset.mem_powersetCard_univ, Finset.card_singleton]
  · exact fun _ _ => by rw [Finset.piecewise_singleton]
  · exact fun _ _ _ _ => by simp only [Finset.singleton_inj, imp_self]
  · intro s hs
    simp only [Finset.powerset_univ, Finset.mem_univ, forall_true_left, Finset.univ_filter_card_eq,
      gt_iff_lt, Nat.lt_one_iff, Finset.card_eq_zero, Finset.mem_powersetCard_univ] at hs
    rw [Finset.card_eq_one] at hs
    existsi Classical.choose hs; existsi Finset.mem_univ _; exact Classical.choose_spec hs

end MultilinearMap

end Derivative
