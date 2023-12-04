import Mathlib.Tactic
import ExteriorPowers.ExteriorAlgebra

open Classical

set_option maxHeartbeats 300000

variable (R M N N' : Type*)
variable [CommRing R] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N'] (n : ℕ)

abbrev ExteriorPower := (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n)

namespace ExteriorPower

def Finite [Module.Finite R M]: Module.Finite R
(ExteriorPower R M n) := by
  apply Module.Finite.mk
  rw [Submodule.fg_top]
  apply Submodule.FG.pow
  rw [LinearMap.range_eq_map]
  apply Submodule.FG.map
  rw [←Module.finite_def]
  exact inferInstance


variable {R M N N'}

def liftAlternating_aux : (AlternatingMap R M N (Fin n)) →ₗ[R]
((i : ℕ) → AlternatingMap R M N (Fin i)) := by
  apply LinearMap.pi
  intro i
  by_cases h : i = n
  . rw [h]; exact LinearMap.id
  . exact 0


def liftAlternating : (AlternatingMap R M N (Fin n)) →ₗ[R] ExteriorPower R M n →ₗ[R] N := by
  set F := LinearMap.comp (ExteriorAlgebra.liftAlternating (R := R) (M := M) (N :=N))
    (liftAlternating_aux n)
  exact {toFun := fun f => LinearMap.domRestrict (F f) (ExteriorPower R M n)
         map_add' := by intro f g
                        simp only [map_add, LinearMap.coe_comp, Function.comp_apply]
                        ext u
                        simp only [LinearMap.domRestrict_apply, LinearMap.add_apply]
         map_smul' := by intro a f
                         simp only [map_smul, LinearMap.coe_comp, Function.comp_apply, RingHom.id_apply]
                         ext u
                         simp only [LinearMap.domRestrict_apply, LinearMap.smul_apply]
         }


variable (R M)


variable {M}

def ιMulti : AlternatingMap R M (ExteriorPower R M n) (Fin n) := by
  apply AlternatingMap.codRestrict (ExteriorAlgebra.ιMulti R n) (ExteriorPower R M n)
    (fun _ => ExteriorAlgebra.ιMulti_range R n (by simp only [Set.mem_range, exists_apply_eq_apply]))

@[simp] lemma ιMulti_apply (a : Fin n → M) :
ιMulti R n a = ExteriorAlgebra.ιMulti R n a := by
  unfold ιMulti
  simp only [AlternatingMap.codRestrict_apply_coe]


-- Here to use in rewrites.
lemma ιMulti_span_fixedDegree :
Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) =
ExteriorPower R M n :=
ExteriorAlgebra.ιMulti_span_fixedDegree R n

lemma ιMulti_span :
Submodule.span R (Set.range (ιMulti R n)) =
(⊤ : Submodule R (ExteriorPower R M n)) := by
  apply LinearMap.map_injective (Submodule.ker_subtype (ExteriorPower R M n))
  rw [LinearMap.map_span, ←Set.image_univ, Set.image_image]
  simp only [Submodule.coeSubtype, ιMulti_apply, Set.image_univ, Submodule.map_top, Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_fixedDegree R n

@[ext]
lemma lhom_ext ⦃f : ExteriorPower R M n →ₗ[R] N⦄ ⦃g : ExteriorPower R M n →ₗ[R] N⦄
(heq : (LinearMap.compAlternatingMap f) (ιMulti R n) =
(LinearMap.compAlternatingMap g) (ιMulti R n)) : f = g := by
  ext u
  have hu : u ∈ (⊤ : Submodule R (ExteriorPower R M n)) := Submodule.mem_top
  rw [←ιMulti_span] at hu
  apply Submodule.span_induction hu (p := fun u => f u = g u)
  . intro _ h
    rw [Set.mem_range] at h
    obtain ⟨a, ha⟩ := h
    apply_fun (fun F => F a) at heq; simp only [LinearMap.compAlternatingMap_apply] at heq
    rw [←ha, heq]
  . rw [LinearMap.map_zero, LinearMap.map_zero]
  . exact fun _ _ h h' => by rw [LinearMap.map_add, LinearMap.map_add, h, h']
  . exact fun _ _ h => by rw [LinearMap.map_smul, LinearMap.map_smul, h]


@[simp] lemma liftAlternating_apply_ιMulti (f : AlternatingMap R M N (Fin n))
(a : Fin n → M) : liftAlternating n f (ιMulti R n a) = f a := by
  unfold liftAlternating
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.domRestrict_apply]
  rw [ιMulti_apply, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  unfold liftAlternating_aux
  simp only [eq_mpr_eq_cast, LinearMap.pi_apply, cast_eq, dite_eq_ite, ite_true, LinearMap.id_coe, id_eq]

@[simp] lemma liftAlternating_comp_ιMulti (f : AlternatingMap R M N (Fin n)) :
(LinearMap.compAlternatingMap (liftAlternating n f)) (ιMulti R n) = f := by
  ext a
  simp only [LinearMap.compAlternatingMap_apply]
  rw [liftAlternating_apply_ιMulti]

@[simp] lemma liftAlternating_ιMulti :
liftAlternating n (R := R) (M := M) (ιMulti R n) = LinearMap.id := by
  ext u
  simp only [liftAlternating_comp_ιMulti, ιMulti_apply, LinearMap.compAlternatingMap_apply,
    LinearMap.id_coe, id_eq]

@[simp]
lemma liftAlternating_comp (g : N →ₗ[R] N') (f : AlternatingMap R M N (Fin n)) :
liftAlternating n (LinearMap.compAlternatingMap g f) =
LinearMap.comp g (liftAlternating n f) := by
  ext u
  simp only [liftAlternating_comp_ιMulti, LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    liftAlternating_apply_ιMulti]

@[simps apply symm_apply]
def liftAlternatingEquiv :
AlternatingMap R M N (Fin n) ≃ₗ[R] ExteriorPower R M n →ₗ[R] N where
toFun := liftAlternating n
map_add' := map_add _
map_smul' := map_smul _
invFun F := F.compAlternatingMap (ιMulti R n)
left_inv f := liftAlternating_comp_ιMulti R n f
right_inv F := by ext u; simp only [liftAlternating_comp, liftAlternating_ιMulti, LinearMap.comp_id]


noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) :
{s : Finset I // Finset.card s = n} → ExteriorPower R M n :=
fun ⟨s, hs⟩ => ιMulti R n (fun i => v (Finset.orderIsoOfFin s hs i))

lemma ιMulti_family_coe {I : Type*} [LinearOrder I] (v : I → M) :
ExteriorAlgebra.ιMulti_family R n v = (Submodule.subtype _) ∘ (ιMulti_family R n v) := by
  ext s
  unfold ιMulti_family
  simp only [Submodule.coeSubtype, Finset.coe_orderIsoOfFin_apply, Function.comp_apply, ιMulti_apply]
  rfl

lemma span_of_span {I : Type*} [LinearOrder I]
{v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) :
Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) = ExteriorPower R M n := by
  apply le_antisymm
  . rw [Submodule.span_le, Set.range_subset_iff]
    intro s
    unfold ExteriorAlgebra.ιMulti_family
    simp only [Finset.coe_orderIsoOfFin_apply, SetLike.mem_coe]
    apply (ExteriorAlgebra.ιMulti_range R n)
    simp only [Set.mem_range, exists_apply_eq_apply]
  . change (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) ≤ _
    rw [LinearMap.range_eq_map, ←hv, Submodule.map_span, Submodule.span_pow, Submodule.span_le]
    intro u hu
    rw [Set.mem_pow] at hu
    obtain ⟨f, hf⟩ := hu
    set g : Fin n → M := fun i => ExteriorAlgebra.ιInv (f i).1
    have hfg : ∀ (i : Fin n), (f i).1 = ExteriorAlgebra.ι R (g i) := by
      intro i
      have h : (f i).1 ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M)) := by
        have h' := (f i).2
        simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and] at h'
        obtain ⟨i, hi⟩ := h'
        simp only [LinearMap.mem_range]
        existsi v i
        exact hi
      rw [LinearMap.mem_range] at h
      obtain ⟨v, hv⟩ := h
      simp only
      rw [←hv, ExteriorAlgebra.ι_inj]
      erw [ExteriorAlgebra.ι_leftInverse]
    have hg : ∀ (i : Fin n), ∃ (j : I), g i = v j := by
      intro i
      have h := (f i).2
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and] at h
      obtain ⟨j, hj⟩ := h
      rw [hfg i, ExteriorAlgebra.ι_inj] at hj
      existsi j
      rw [hj]
    have heq : u = ExteriorAlgebra.ιMulti R n g := by
      rw [ExteriorAlgebra.ιMulti_apply, ←hf]
      apply congrArg; apply congrArg
      ext i
      exact hfg i
    rw [heq]
    set α : Fin n → I := fun i => Classical.choose (hg i)
    set αprop := fun i => Classical.choose_spec (hg i)
    by_cases hinj : Function.Injective α
    . set s := Finset.image α Finset.univ
      set h : Fin n → s := fun i => ⟨α i, by simp only [Finset.mem_image, Finset.mem_univ, true_and,
        exists_apply_eq_apply]⟩
      have hbij : Function.Bijective h := by
        constructor
        . intro i j hij
          rw [Subtype.mk.injEq] at hij
          exact hinj hij
        . intro ⟨i, hi⟩
          rw [Finset.mem_image] at hi
          obtain ⟨a, ha⟩ := hi
          existsi a
          simp only [Subtype.mk.injEq]
          exact ha.2
      have hs : Finset.card s = n := by
        suffices h : Fintype.card s = n
        . rw [←h]; simp only [Finset.mem_image, Finset.mem_univ, true_and, Fintype.card_coe]
        . rw [←(Fintype.card_of_bijective hbij)]
          simp only [Fintype.card_fin]
      set e := Finset.orderIsoOfFin s hs
      set g' : Fin n → M := fun i => v (e i)
      have hg' : ExteriorAlgebra.ιMulti R n g' ∈ Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) := by
        apply Submodule.subset_span
        rw [Set.mem_range]
        existsi ⟨s, hs⟩
        unfold ExteriorAlgebra.ιMulti_family
        simp only [Finset.coe_orderIsoOfFin_apply]
      set σ : Equiv.Perm (Fin n) := (Equiv.ofBijective h hbij).trans e.toEquiv.symm
      have hgg' : g = g' ∘ σ := by
        ext i
        rw [Function.comp_apply, Equiv.trans_apply]
        change g i = v (e (_))
        erw [Equiv.apply_symm_apply e.toEquiv (Equiv.ofBijective h hbij i)]
        simp only [Equiv.ofBijective_apply]
        exact αprop i
      rw [hgg', AlternatingMap.map_perm]
      exact Submodule.smul_mem _ _ hg'
    . change ¬(∀ (a b : Fin n), _) at hinj
      push_neg at hinj
      obtain ⟨i, j, hij1, hij2⟩ := hinj
      have heq : g = Function.update g i (g j) := by
        ext k
        by_cases hk : k = i
        . rw [Function.update_apply]
          simp only [hk, ite_true]
          change g i = g j
          rw [αprop i, αprop j]
          change v (α i) = v (α j)
          rw [hij1]
        . simp only [ne_eq, hk, not_false_eq_true, Function.update_noteq]
      rw [heq, AlternatingMap.map_update_self _ _ hij2]
      simp only [SetLike.mem_coe, Submodule.zero_mem]


lemma span_of_span' {I : Type*} [LinearOrder I]
{v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) :
Submodule.span R  (Set.range (ιMulti_family R n v)) = ⊤ := by
  rw [eq_top_iff]
  intro ⟨u, hu⟩ _
  set hu' := hu
  rw [←(span_of_span R n hv), ιMulti_family_coe,
    Set.range_comp, ←Submodule.map_span, Submodule.mem_map] at hu'
  obtain ⟨v, hv, huv⟩ := hu'
  have heq : ⟨u, hu⟩ = v := by
    rw [←SetCoe.ext_iff]
    simp only
    simp only [Submodule.coeSubtype] at huv
    exact (Eq.symm huv)
  rw [heq]
  exact hv

variable (M)

noncomputable def toTensorPower : ExteriorPower R M n →ₗ[R] TensorPower R n M :=
liftAlternatingEquiv R n
(MultilinearMap.alternatization (PiTensorProduct.tprod R (s := fun (_ : Fin n) => M)))

variable {M}

@[simp]
lemma toTensorPower_apply_ιMulti (v : Fin n → M) :
toTensorPower R M n (ιMulti R n v) =
Finset.sum Finset.univ (fun (σ : Equiv.Perm (Fin n)) => Equiv.Perm.sign σ •
(PiTensorProduct.tprod R (fun i => v (σ i)))) := by
  unfold toTensorPower
  simp only [liftAlternatingEquiv_apply, liftAlternating_apply_ιMulti]
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply]


noncomputable def TensorPower_linearFormOfFamily (f : (i : Fin n) → (M →ₗ[R] R)) :
TensorPower R n M →ₗ[R] R := PiTensorProduct.lift
(MultilinearMap.compLinearMap (MultilinearMap.mkPiRing R (Fin n) 1) f)

@[simp]
lemma TensorPower_linearFormOfFamily_apply_tprod (f : (i : Fin n) → (M →ₗ[R] R)) (v : Fin n → M) :
TensorPower_linearFormOfFamily R n f (PiTensorProduct.tprod R v) =
Finset.prod Finset.univ (fun i => (f i (v i))) := by
  unfold TensorPower_linearFormOfFamily
  simp only [Finset.coe_orderIsoOfFin_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, Basis.coord_apply, MultilinearMap.mkPiRing_apply,
    smul_eq_mul, _root_.mul_one]

noncomputable def linearFormOfFamily (f : (i : Fin n) → (M →ₗ[R] R)) :
ExteriorPower R M n →ₗ[R] R :=
LinearMap.comp (TensorPower_linearFormOfFamily R n f) (toTensorPower R M n)

@[simp]
lemma linearFormOfFamily_apply (f : (i : Fin n) → (M →ₗ[R] R)) (x : ExteriorPower R M n) :
linearFormOfFamily R n f x = TensorPower_linearFormOfFamily R n f (toTensorPower R M n x) := by
  unfold linearFormOfFamily
  simp only [LinearMap.coe_comp, Function.comp_apply]

@[simp]
lemma linearFormOfFamily_apply_ιMulti (f : (i : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
linearFormOfFamily R n f (ιMulti R n m) = Finset.sum Finset.univ (fun (σ : Equiv.Perm (Fin n)) => Equiv.Perm.sign σ •
Finset.prod Finset.univ (fun (i : Fin n) => f i (m (σ i)))) := by
  simp only [linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum,
    LinearMap.map_smul_of_tower, TensorPower_linearFormOfFamily_apply_tprod]


noncomputable def alternatingFormOfFamily (f : (i : Fin n) → (M →ₗ[R] R)) :
AlternatingMap R M R (Fin n) :=
(linearFormOfFamily R n f).compAlternatingMap (ιMulti R n)

@[simp]
lemma alternatingFormOfFamily_apply (f : (i : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
alternatingFormOfFamily R n f m = linearFormOfFamily R n f (ιMulti R n m) := by
  unfold alternatingFormOfFamily
  rw [LinearMap.compAlternatingMap_apply]

noncomputable def linearFormOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) : ExteriorPower R M n →ₗ[R] R :=
linearFormOfFamily R n (fun i => b.coord (Finset.orderIsoOfFin s hs i))

@[simp]
lemma linearFormOfBasis_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) (v : Fin n → M) :
linearFormOfBasis R n b hs (ιMulti R n v) =
Finset.sum Finset.univ (fun (σ : Equiv.Perm (Fin n)) => Equiv.Perm.sign σ •
Finset.prod Finset.univ (fun i => b.coord (Finset.orderIsoOfFin s hs i) (v (σ i)))) := by
  unfold linearFormOfBasis
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfFamily_apply, toTensorPower_apply_ιMulti,
    map_sum, LinearMap.map_smul_of_tower, TensorPower_linearFormOfFamily_apply_tprod,
    Basis.coord_apply]

lemma linearFormOfBasis_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) :
linearFormOfBasis R n b hs (ιMulti_family R n b ⟨s, hs⟩) = 1 := by
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfBasis_apply_ιMulti]
  have hzero : ∀ (σ : Equiv.Perm (Fin n)), σ ∈ Finset.univ → ¬σ ∈ ({Equiv.refl (Fin n)} :
    Finset (Equiv.Perm (Fin n))) → TensorPower_linearFormOfFamily R n (fun i => b.coord (Finset.orderIsoOfFin s hs i))
    (Equiv.Perm.sign σ • ⨂ₜ[R] (i : Fin n), b ((Finset.orderIsoOfFin s hs) (σ i))) = 0 := by
    intro σ _ hσ
    simp only [Finset.mem_singleton] at hσ
    erw [LinearMap.map_smul]
    apply smul_eq_zero_of_right
    simp only [Finset.coe_orderIsoOfFin_apply, TensorPower_linearFormOfFamily_apply_tprod]
    have h : ∃ (i : Fin n), ¬ σ i = i := by
      by_contra habs
      push_neg at habs
      apply hσ
      ext i
      simp only [Equiv.refl_apply]
      rw [habs i]
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _)
    rw [Basis.coord_apply, Basis.repr_self_apply]
    simp only [Finset.coe_orderIsoOfFin_apply, OrderEmbedding.eq_iff_eq, ite_eq_right_iff]
    simp only [hi, IsEmpty.forall_iff]
  have heq := Finset.sum_subset (s₁ := {Equiv.refl (Fin n)}) (Finset.subset_univ _) hzero
  simp only [Finset.coe_orderIsoOfFin_apply, LinearMap.map_smul_of_tower,
    TensorPower_linearFormOfFamily_apply_tprod, Basis.coord_apply, Basis.repr_self, ne_eq,
    RelEmbedding.inj, Finset.sum_singleton, Equiv.Perm.sign_refl, Equiv.refl_apply,
    Finsupp.single_eq_same, Finset.prod_const_one, one_smul] at heq ⊢
  rw [←heq]


lemma linearFormOfBasis_apply_nondiag_aux {I : Type*} [LinearOrder I]
{s t : Finset I} (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) (σ : Equiv.Perm (Fin n)) :
∃ (i : Fin n), (Finset.orderIsoOfFin s hs i).1 ≠ (Finset.orderIsoOfFin t ht (σ i)).1 := by
  by_contra habs
  push_neg at habs
  apply hst
  apply Finset.eq_of_subset_of_card_le
  . intro a has
    set b := Finset.orderIsoOfFin t ht (σ ((Finset.orderIsoOfFin s hs).symm ⟨a, has⟩))
    have heq : a = b.1 := by
      rw [←habs]
      simp only [OrderIso.apply_symm_apply]
    rw [heq]
    exact b.2
  . rw [hs, ht]

lemma linearFormOfBasis_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
{s t : Finset I} (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) :
linearFormOfBasis R n b hs (ιMulti_family R n b ⟨t, ht⟩) = 0 := by
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfBasis_apply_ιMulti]
  apply Finset.sum_eq_zero
  intro σ _
  erw [zsmul_eq_smul_cast R]
  apply smul_eq_zero_of_right
  obtain ⟨i, hi⟩ := linearFormOfBasis_apply_nondiag_aux n hs ht hst σ
  apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _)
  rw [Basis.coord_apply, Basis.repr_self_apply]
  simp only [Finset.coe_orderIsoOfFin_apply, ne_eq] at hi
  simp only [Finset.coe_orderIsoOfFin_apply, Ne.symm hi, ite_false]


noncomputable def BasisOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
Basis {s : Finset I // Finset.card s = n} R (ExteriorPower R M n) := by
  apply Basis.mk (v := ιMulti_family R n b)
  . apply linearIndependent_of_dualFamily R _
      (fun s => linearFormOfBasis R n b s.2)
    . intro ⟨s, hs⟩ ⟨t, ht⟩ hst
      simp only [ne_eq, Subtype.mk.injEq] at hst
      simp only [Function.comp_apply]
      apply linearFormOfBasis_apply_nondiag
      exact hst
    . intro ⟨s, hs⟩
      simp only [Function.comp_apply]
      apply linearFormOfBasis_apply_diag
  . rw [span_of_span']
    rw [Basis.span_eq]

lemma BasisOfBasis_coe {I : Type*} [LinearOrder I] (b : Basis I R M) :
FunLike.coe (BasisOfBasis R n b) = ιMulti_family R n b := Basis.coe_mk _ _

lemma BasisOfBasis_apply {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) :
BasisOfBasis R n b ⟨s, hs⟩ = ιMulti_family R n b ⟨s, hs⟩ := by
  rw [BasisOfBasis_coe]

lemma BasisOfBasis_coord {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) :
Basis.coord (BasisOfBasis R n b) ⟨s, hs⟩ = linearFormOfBasis R n b hs := by
  apply LinearMap.ext_on (ExteriorPower.span_of_span' R n (Basis.span_eq b))
  intro x hx
  rw [Set.mem_range] at hx
  obtain ⟨⟨t, ht⟩, htx⟩ := hx
  rw [←htx]
  conv_lhs => rw [←BasisOfBasis_apply]
  by_cases heq : s = t
  . have heq' : (⟨s, hs⟩ : {s : Finset I // Finset.card s = n}) = ⟨t, ht⟩ := by
      simp only [Subtype.mk.injEq]; exact heq
    rw [←heq']
    rw [linearFormOfBasis_apply_diag]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
  . rw [linearFormOfBasis_apply_nondiag R n b hs ht heq]
    rw [Basis.coord_apply, Basis.repr_self_apply]
    simp only [Subtype.mk.injEq, Ne.symm heq, ite_false]

lemma FreeOfFree (hfree : Module.Free R M) : Module.Free R
(ExteriorPower R M n) := by
  obtain ⟨I, b⟩ := (Classical.choice hfree.exists_basis)
  letI := WellFounded.wellOrderExtension (emptyWf (α := I)).wf
  exact Module.Free.of_basis (BasisOfBasis R n b)

variable [StrongRankCondition R]

lemma FinrankOfFiniteFree (hfree : Module.Free R M)
[Module.Finite R M] :
FiniteDimensional.finrank R (ExteriorPower R M n) =
Nat.choose (FiniteDimensional.finrank R M) n := by
  set I := hfree.ChooseBasisIndex
  set b := hfree.chooseBasis
  letI := WellFounded.wellOrderExtension (emptyWf (α := I)).wf
  set B :=  BasisOfBasis R n b
  rw [FiniteDimensional.finrank_eq_card_basis b, FiniteDimensional.finrank_eq_card_basis B,
    Fintype.card_finset_len]

-- TODO: Freeness, finite-dimensionality and dimension for the whole exterior algebra.

/- Not sure how useful that is. I certainly don't need it now.-/
/-lemma ExteriorAlgebra.GradedPiece.finrank (hfree : Module.Free R M) (hnf : ¬ Module.Finite R M) :
n > 0 → FiniteDimensional.finrank R (ExteriorAlgebra.GradedPiece R M n) = 0 := by
  set I := hfree.ChooseBasisIndex
  set b := hfree.chooseBasis
  letI := WellFounded.wellOrderExtension (emptyWf (α := I)).wf
  set B :=  ExteriorAlgebra.GradedPiece.basis R n b
  have h : FiniteDimensional.finrank R (ExteriorAlgebra.GradedPiece R M n) = 0 := by
    letI := ExteriorAlgebra.GradedPiece.free R n hfree
    apply finrank_eq_zero_of_basis_imp_false
    intro s Bs
    have heq := mk_eq_mk_of_basis B Bs
    simp only [Finset.coe_sort_coe, Cardinal.mk_fintype, Fintype.card_coe, Cardinal.lift_natCast,
      Cardinal.lift_eq_nat_iff] at heq
    have hinf : Infinite {s : Finset I // Finset.card s = n} := sorry
    rw [Cardinal.infinite_iff, heq] at hinf
    exact lt_irrefl _ (lt_of_lt_of_le (Cardinal.nat_lt_aleph0 (Finset.card s)) hinf)
  rw [h]; simp only [gt_iff_lt, implies_true]
-/

-- Functoriality

variable {R}

def map (f : M →ₗ[R] N) : ExteriorPower R M n →ₗ[R] ExteriorPower R N n := by
  refine LinearMap.restrict (AlgHom.toLinearMap (ExteriorAlgebra.map f)) ?_
  intro x hx
  rw [←ιMulti_span_fixedDegree] at hx ⊢
  have hx := Set.mem_image_of_mem (ExteriorAlgebra.map f) hx
  rw [←Submodule.map_coe, LinearMap.map_span, ←Set.range_comp] at hx
  erw [←(LinearMap.coe_compAlternatingMap (ExteriorAlgebra.map f).toLinearMap (ExteriorAlgebra.ιMulti R n))] at hx
  rw [ExteriorAlgebra.map_comp_ιMulti, AlternatingMap.coe_compLinearMap] at hx
  refine Set.mem_of_mem_of_subset hx ?_
  apply Submodule.span_mono
  apply Set.range_comp_subset_range

@[simp]
theorem map_apply_ιMulti (f : M →ₗ[R] N) (m : Fin n → M) :
(map n f) ((ιMulti R n) m) = (ιMulti R n) (f ∘ m) := by
  unfold map
  rw [LinearMap.restrict_apply]
  rw [←SetCoe.ext_iff]
  simp only
  rw [ιMulti_apply]
  erw [ExteriorAlgebra.map_apply_ιMulti, ιMulti_apply]

@[simp]
theorem map_comp_ιMulti (f : M →ₗ[R] N) :
(map n f).compAlternatingMap (ιMulti R n (M := M)) = (ιMulti R n (M := N)).compLinearMap f := by
  unfold map
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.restrict_coe_apply, ιMulti_apply,
    AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti, Function.comp_apply, AlternatingMap.compLinearMap_apply]
  apply congrArg
  ext i
  simp only [Function.comp_apply]

@[simp]
theorem map_id :
map n (LinearMap.id) = LinearMap.id (R := R) (M := ExteriorPower R M n) := by
  unfold map
  ext m
  simp only [map_id, AlgHom.toLinearMap_id, LinearMap.compAlternatingMap_apply, LinearMap.restrict_coe_apply,
    ιMulti_apply, LinearMap.id_coe, id_eq]
  rw [ExteriorAlgebra.map_id]
  simp only [AlgHom.toLinearMap_id, LinearMap.id_coe, id_eq]

@[simp]
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
LinearMap.comp (map n g) (map n f) = map n (LinearMap.comp g f) := by
  unfold map
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.restrict_coe_apply,
    ιMulti_apply, AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti]
  rw [Function.comp.assoc]


lemma linearFormOfFamily_compExteriorPowerMap (f : (i : Fin n) → (M →ₗ[R] R))
(p : N →ₗ[R] M) :
LinearMap.comp (linearFormOfFamily R n f) (ExteriorPower.map n p) =
linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) := by
  apply LinearMap.ext_on (ιMulti_span R n (M :=N))
  intro x hx
  rw [Set.mem_range] at hx
  obtain ⟨y, h⟩ := hx
  rw [←h]
  simp only [LinearMap.coe_comp, Function.comp_apply, map_apply_ιMulti, linearFormOfFamily_apply,
    toTensorPower_apply_ιMulti, map_sum, LinearMap.map_smul_of_tower,
    TensorPower_linearFormOfFamily_apply_tprod]


lemma linearFormOfFamily_compExteriorPowerMap_apply (f : (i : Fin n) → (M →ₗ[R] R))
(p : N →ₗ[R] M) (x : ExteriorPower R N n) :
(linearFormOfFamily R n f) (ExteriorPower.map n p x) =
linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) x := by
  rw [←LinearMap.comp_apply, linearFormOfFamily_compExteriorPowerMap]


lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
Function.Injective (map n f) := by
  obtain ⟨g, hgf⟩ := hf
  apply Function.RightInverse.injective (g := map n g)
  intro m
  rw [←LinearMap.comp_apply, map_comp_map, hgf, map_id]
  simp only [LinearMap.id_coe, id_eq]


lemma map_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f) :
Function.Surjective (map n f) := by
  rw [←LinearMap.range_eq_top, LinearMap.range_eq_map, ←ιMulti_span, ←ιMulti_span,
    Submodule.map_span, ←Set.range_comp, ←LinearMap.coe_compAlternatingMap, map_comp_ιMulti,
    AlternatingMap.coe_compLinearMap, Set.range_comp]
  apply congrArg
  conv_rhs => rw [←Set.image_univ]
  apply congrArg
  rw [Set.range_iff_surjective]
  intro y
  existsi fun i => Classical.choose (hf (y i))
  ext i
  simp only [Function.comp_apply]
  exact Classical.choose_spec (hf (y i))

variable {K E F: Type*} [Field K] [AddCommGroup E]
  [Module K E] [AddCommGroup F] [Module K F] (n : ℕ)

lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
Function.Injective (map n f) :=
map_injective n (LinearMap.exists_leftInverse_of_injective f hf)


/- Every element of ExteriorPower R M n is in the image of ExteriorPower R P n, for some finitely generated submodule
P of M.-/

lemma range_ExteriorPower_submodule_le {P Q : Submodule R M} (hPQ : P ≤ Q) :
LinearMap.range (map n (Submodule.subtype P)) ≤ LinearMap.range (map n (Submodule.subtype Q)) := by
  intro x hx
  rw [LinearMap.mem_range]
  obtain ⟨y, hyx⟩ := hx
  rw [←hyx]
  have hy : y ∈ (⊤ : Submodule R (ExteriorPower R P n)) := by simp only [Submodule.mem_top]
  rw [←ExteriorPower.ιMulti_span] at hy
  apply Submodule.span_induction hy (p := fun y => ∃ z, (map n (Submodule.subtype Q)) z = (map n (Submodule.subtype P)) y)
  . intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨m, hmx⟩ := hx
    existsi ExteriorPower.ιMulti R n (M := Q) (fun i => ⟨(m i).1, hPQ (m i).2⟩)
    rw [ExteriorPower.map_apply_ιMulti, ←hmx, ExteriorPower.map_apply_ιMulti]
    apply congrArg
    ext i
    simp only [Submodule.coeSubtype, Function.comp_apply]
  . existsi 0
    rw [LinearMap.map_zero, LinearMap.map_zero]
  . intro x y ⟨z, hz⟩ ⟨z', hz'⟩
    existsi z + z'
    rw [LinearMap.map_add, LinearMap.map_add, hz, hz']
  . intro a y ⟨z, hz⟩
    existsi a • z
    rw [LinearMap.map_smul, LinearMap.map_smul, hz]


lemma mem_ExteriorPowerSup {P Q : Submodule R M} (x : ExteriorPower R P n) (y : ExteriorPower R Q n) :
ExteriorPower.map n (Submodule.subtype P) x + ExteriorPower.map n (Submodule.subtype Q) y ∈
LinearMap.range (ExteriorPower.map n (Submodule.subtype (P ⊔ Q))) := by
  apply Submodule.add_mem
  . apply range_ExteriorPower_submodule_le n le_sup_left
    simp only [LinearMap.mem_range, exists_apply_eq_apply]
  . apply range_ExteriorPower_submodule_le n le_sup_right
    simp only [LinearMap.mem_range, exists_apply_eq_apply]


lemma mem_exteriorPowerFiniteSubmodule (x : ExteriorPower R M n) :
∃ (P : Submodule R M), Submodule.FG P ∧ x ∈ LinearMap.range (ExteriorPower.map n (Submodule.subtype P)) := by
  have hx : x ∈ (⊤ : Submodule R (ExteriorPower R M n)) := by simp only [Submodule.mem_top]
  rw [←ExteriorPower.ιMulti_span] at hx
  apply Submodule.span_induction hx (p := fun x => ∃ (P : Submodule R M), Submodule.FG P ∧ x ∈ LinearMap.range
    (ExteriorPower.map n (Submodule.subtype P)))
  . intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨m, hmx⟩ := hx
    existsi Submodule.span R (Set.range m)
    rw [and_iff_right (Submodule.fg_span (Set.finite_range m)), LinearMap.mem_range]
    have hm : ∀ (i : Fin n), m i ∈ Submodule.span R (Set.range m) := by
      intro i
      apply Submodule.subset_span
      simp only [Set.mem_range, exists_apply_eq_apply]
    existsi ιMulti R n (fun i => ⟨m i, hm i⟩)
    simp only [Subtype.mk.injEq, map_apply_ιMulti, Submodule.coeSubtype, Function.comp_apply]
    rw [←hmx]
    apply congrArg
    ext i
    simp only [Function.comp_apply]
  . existsi (⊥ : Submodule R M)
    exact ⟨Submodule.fg_bot, Submodule.zero_mem _⟩
  . intro x y ⟨Px, hx⟩ ⟨Py, hy⟩
    existsi Px ⊔ Py
    rw [and_iff_right (Submodule.FG.sup hx.1 hy.1)]
    rw [LinearMap.mem_range] at hx hy
    obtain ⟨x', hxx'⟩ := hx.2
    obtain ⟨y', hyy'⟩ := hy.2
    rw [←hxx', ←hyy']
    exact mem_ExteriorPowerSup n x' y'
  . intro a x ⟨P, h⟩
    existsi P
    exact ⟨h.1, Submodule.smul_mem _ a h.2⟩

end ExteriorPower
