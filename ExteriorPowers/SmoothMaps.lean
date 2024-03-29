import Mathlib.Tactic
import Mathlib.Geometry.Manifold.ContMDiff.Product
import ExteriorPowers.Manifold
import ExteriorPowers.contMDiff_openEmbedding
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Geometry.Manifold.Diffeomorph


open Classical

namespace Grassmannian

section SmoothMaps

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] [SeparatingDual 𝕜 E]
{I : Type*} [Fintype I] [Nonempty {v : I → E // LinearIndependent 𝕜 v}]



/- First we relate Grassmannian.mkI' and Grassmannian.mk', using an arbitrary bijection between I and Fin r.-/

variable {J : Type*} [Fintype J] [Nonempty {v : J → E // LinearIndependent 𝕜 v}]

noncomputable def ContinuousLinearEquivIJ (e : I ≃ J) : (I → E) ≃L[𝕜] (J → E) :=
{(LinearEquiv.piCongrLeft' 𝕜 (fun _ => E) e)
 with
 continuous_toFun := by continuity
 continuous_invFun := by continuity}

lemma ContinuousLinearEquivIJ_apply (e : I ≃ J) (v : I → E) :
ContinuousLinearEquivIJ 𝕜 E e v = v ∘ e.invFun := by
  unfold ContinuousLinearEquivIJ
  ext j
  simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.mk_coe, Equiv.invFun_as_coe, Function.comp_apply]
  change (LinearEquiv.piCongrLeft' 𝕜 (fun _ => E) e) v j = _
  rw [LinearEquiv.piCongrLeft'_apply]

noncomputable def FunctionLinearIndependentIJ (e : I ≃ J) : {v : I → E // LinearIndependent 𝕜 v} →
{v : J → E // LinearIndependent 𝕜 v} := by
  apply Set.MapsTo.restrict (ContinuousLinearEquivIJ 𝕜 E e)
  intro v hv
  change LinearIndependent 𝕜 _
  rw [ContinuousLinearEquivIJ_apply, Equiv.invFun_as_coe, linearIndependent_equiv]
  exact hv

lemma FunctionLinearIndependentIJ_apply (e : I ≃ J) (v : {v : I → E // LinearIndependent 𝕜 v}) :
(FunctionLinearIndependentIJ 𝕜 E e v).1 = v.1 ∘ e.invFun := by
  unfold FunctionLinearIndependentIJ
  simp only [Set.MapsTo.val_restrict_apply, Equiv.invFun_as_coe]
  rw [ContinuousLinearEquivIJ_apply, Equiv.invFun_as_coe]

noncomputable def EquivLinearIndependentIJ (e : I ≃ J) : {v : I → E // LinearIndependent 𝕜 v} ≃
{v : J → E // LinearIndependent 𝕜 v} :=
{toFun := FunctionLinearIndependentIJ 𝕜 E e
 invFun := FunctionLinearIndependentIJ 𝕜 E e.symm
 left_inv := by
   intro v
   rw [←SetCoe.ext_iff, FunctionLinearIndependentIJ_apply, FunctionLinearIndependentIJ_apply]
   ext i
   simp only [Equiv.invFun_as_coe, Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply]
 right_inv := by
   intro v
   rw [←SetCoe.ext_iff, FunctionLinearIndependentIJ_apply, FunctionLinearIndependentIJ_apply]
   ext i
   simp only [Equiv.invFun_as_coe, Equiv.symm_symm, Function.comp_apply, Equiv.apply_symm_apply]
}

lemma EquivLinearIndependentIJ_apply (e : I ≃ J) (v : {v :I → E // LinearIndependent 𝕜 v}) :
(EquivLinearIndependentIJ 𝕜 E e v).1 = v.1 ∘ e.invFun := by
  unfold EquivLinearIndependentIJ
  change (FunctionLinearIndependentIJ 𝕜 E e v).1 = _
  rw [FunctionLinearIndependentIJ_apply]

lemma SmoothFunctionLinearIndependentIJ (e : I ≃ J) :
ContMDiff (modelWithCornersSelf 𝕜 (I → E)) (modelWithCornersSelf 𝕜 (J → E)) ⊤
(FunctionLinearIndependentIJ 𝕜 E e) := by
  rw [ContMDiff_vs_openEmbedding]
  have heq : (fun v => v.1) ∘ (FunctionLinearIndependentIJ 𝕜 E e) = (ContinuousLinearEquivIJ 𝕜 E e) ∘ (fun v => v.1) := by
    apply funext
    intro v
    simp only [Function.comp_apply]
    rw [FunctionLinearIndependentIJ_apply, ContinuousLinearEquivIJ_apply]
  rw [heq]
  apply ContMDiff.comp (E' := I → E) (I' := modelWithCornersSelf 𝕜 (I → E))
  . rw [contMDiff_iff_contDiff]
    apply ContinuousLinearEquiv.contDiff
  . apply contMDiffOpenEmbedding

noncomputable def DiffeomorphLinearIndependentIJ (e : I ≃ J) : Diffeomorph (modelWithCornersSelf 𝕜 (I → E))
(modelWithCornersSelf 𝕜 (J → E)) {v : I → E // LinearIndependent 𝕜 v} {v : J → E // LinearIndependent 𝕜 v} ⊤ :=
{EquivLinearIndependentIJ 𝕜 E e with
 contMDiff_toFun := SmoothFunctionLinearIndependentIJ 𝕜 E e
 contMDiff_invFun := SmoothFunctionLinearIndependentIJ 𝕜 E e.symm}

lemma DiffeomorphLinearIndependentIJ_apply (e : I ≃ J) (v : {v :I → E // LinearIndependent 𝕜 v}) :
(DiffeomorphLinearIndependentIJ 𝕜 E e v).1 = v.1 ∘ e.invFun := by
  unfold DiffeomorphLinearIndependentIJ
  change (EquivLinearIndependentIJ 𝕜 E e v).1 = _
  rw [EquivLinearIndependentIJ_apply]


variable {r : ℕ} (hrI : Fintype.card I = r)
 [Nonempty (Grassmannian 𝕜 E r)]

instance instNonemptyGrassmannianLift : Nonempty {v : Fin r → E // LinearIndependent 𝕜 v} :=
(NonemptyGrassmannian_iff' 𝕜 E r).mpr inferInstance

lemma Grassmannian.mk'_vs_mkI' : Grassmannian.mkI' 𝕜 hrI = Grassmannian.mk' 𝕜 ∘
(DiffeomorphLinearIndependentIJ 𝕜 E (Fintype.equivFinOfCardEq hrI)) := by
  apply funext
  intro v
  rw [Function.comp_apply, ←SetCoe.ext_iff]
  rw [Grassmannian.mkI'_eq_mkI, Grassmannian.mkI_apply]
  rw [Grassmannian.mk'_eq_mk, Grassmannian.mk_apply]
  rw [DiffeomorphLinearIndependentIJ_apply]
  rw [Equiv.invFun_as_coe, EquivLike.range_comp]


lemma Smooth.quotientMap :
ContMDiff (modelWithCornersSelf 𝕜 (Fin r → E)) (E' := (Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r))
(M' := Grassmannian 𝕜 E r) (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) ⊤
(Grassmannian.mk' 𝕜) := by
  apply contMDiff_of_locally_contMDiffOn
  intro v
  set φ := PhiForChart (Epsilon 𝕜 E r) (Grassmannian.mk' 𝕜 v)
  set φ₁ := (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) _).comp φ.toContinuousLinearMap
  set hφ := PhiForChart_prop (Epsilon 𝕜 E r) (Grassmannian.mk' 𝕜 v)
  existsi {v | LinearIndependent 𝕜 (φ₁ ∘ v.1)}
  rw [and_iff_right (GoodsetIsOpen_aux2 φ₁), Set.mem_setOf_eq]
  erw [←(GoodsetPreimage φ₁ v.2), and_iff_right hφ]
  have heq : ∀ u, u ∈ {v | LinearIndependent 𝕜 (φ₁ ∘ v.1)} → (Grassmannian.mk' 𝕜) u =
    ((InverseChart φ) ∘ (ChartLift φ) ∘ (fun v => v.1)) u := by
    intro u hu
    exact QuotientInChart φ u hu
  rw [contMDiffOn_congr heq]
  apply ContMDiffOn.comp (g := InverseChart φ) (E' := ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)))
    (I' := modelWithCornersSelf 𝕜 ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r))) (t := ⊤)
  . have h1 : InverseChart φ = (instChartedSpaceGrassmannian.chartAt (Grassmannian.mk' 𝕜 v)).symm := by
      unfold ChartedSpace.chartAt instChartedSpaceGrassmannian ChartAt Chart_PartialHomeomorph Chart_PartialEquiv
      simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp, Set.top_eq_univ, PartialHomeomorph.mk_coe_symm,
        PartialEquiv.coe_symm_mk]
    rw [h1]
    have h2 : ⊤ = (instChartedSpaceGrassmannian.chartAt (Grassmannian.mk' 𝕜 v)).toPartialEquiv.target := by
      unfold ChartedSpace.chartAt instChartedSpaceGrassmannian ChartAt Chart_PartialHomeomorph Chart_PartialEquiv
      simp only [Set.top_eq_univ]
    rw [h2]
    apply contMDiffOn_chart_symm (I := ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r)
  . apply ContMDiffOn.comp (E' := Fin r → E) (I' := modelWithCornersSelf 𝕜 (Fin r → E))
      (t := {v : Fin r → E | LinearIndependent 𝕜 (φ₁ ∘ v)})
    . rw [contMDiffOn_iff_contDiffOn]
      apply ChartLiftSmoothOn
    . apply ContMDiff.contMDiffOn
      apply contMDiffOpenEmbedding
    . simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Set.preimage_setOf_eq,
      Set.setOf_subset_setOf, imp_self, Subtype.forall, implies_true, forall_const]
  . simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Set.top_eq_univ,
    Set.preimage_univ, Set.subset_univ]

/- A slight generalization where we take the quotient from {v : I → E // LinearIndependent 𝕜 v} instead, under
the assumption that Fintype.card I = r. This is sometimes useful when we don't have a natural order on I.-/


lemma Smooth.quotientMapI :
ContMDiff (modelWithCornersSelf 𝕜 (I → E)) (E' := (Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r))
(M' := Grassmannian 𝕜 E r) (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) ⊤
(Grassmannian.mkI' 𝕜 hrI) := by
  rw [Grassmannian.mk'_vs_mkI']
  rw [Diffeomorph.contMDiff_comp_diffeomorph_iff]
  apply Smooth.quotientMap
  exact le_refl _


/- If f is map from the Grassmannian to a manifold such that f ∘ Grassmannian.mk' is smooth, we prove that f is
smooth. This is useful to construct smooth maps from the Grassmannian.-/

variable {𝕜 E}


lemma ChoiceOfChartForLift (v : {v : Fin r → E // LinearIndependent 𝕜 v}) :
∃ (φ : E ≃L[𝕜] (Fin r → 𝕜) × (ModelSpace 𝕜 E r)), ((Grassmannian.mk' 𝕜 v) ∈ Goodset
((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) _).comp φ.toContinuousLinearMap) ∧
((InverseChartLift_codRestrict φ) ∘ (Chart φ) ∘ (Grassmannian.mk' 𝕜)) v = v) :=
ChoiceOfChart (PhiForChart (Epsilon 𝕜 E r) (Grassmannian.mk' 𝕜 v)) v
(PhiForChart_prop (Epsilon 𝕜 E r) (Grassmannian.mk' 𝕜 v))


lemma SmoothAt.mapFromGrassmannian {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*}
[TopologicalSpace H] {I : ModelWithCorners 𝕜 F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
[SmoothManifoldWithCorners I M] {n : ℕ∞} {f : Grassmannian 𝕜 E r → M} (v : {v : Fin r → E // LinearIndependent 𝕜 v})
(hf : ContMDiffAt (modelWithCornersSelf 𝕜 (Fin r → E)) I n (f ∘ (Grassmannian.mk' 𝕜) :
{v : Fin r → E // LinearIndependent 𝕜 v} → M) v) :
@ContMDiffAt 𝕜 _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _ _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _
(ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) (Grassmannian 𝕜 E r) _ _ F _ _ H _ I M _ _ n f
(Grassmannian.mk' 𝕜 v):= by
  set φ := Classical.choose (ChoiceOfChartForLift v)
  set φ₁ := (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) _).comp φ.toContinuousLinearMap
  set hφ := Classical.choose_spec (ChoiceOfChartForLift v)
  set g := (f ∘ (Grassmannian.mk' 𝕜)) ∘ (InverseChartLift_codRestrict φ) ∘ (Chart φ)
  have heq : f =ᶠ[nhds (Grassmannian.mk' 𝕜 v)] g := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    existsi (Goodset φ₁)
    constructor
    . refine IsOpen.mem_nhds ?_ hφ.1
      apply GoodsetIsOpen
    . intro W hW
      conv => lhs
              rw [IdInChart φ hW]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  apply ContMDiffAt.comp (E' := Fin r → E) (I' := modelWithCornersSelf 𝕜 (Fin r → E))
  . have heq : (InverseChartLift_codRestrict φ ∘ Chart φ) (Grassmannian.mk' 𝕜 v) = v := by
      conv => rhs
              rw [←hφ.2]
    rw [heq]
    exact hf
  . apply ContMDiffAt.comp (E' := (Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) (I' := modelWithCornersSelf 𝕜
      ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)))
    . rw [ContMDiffAt_vs_openEmbedding (modelWithCornersSelf 𝕜 ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)))
        (LinearIndependentToAll 𝕜 E (Fin r)) (InverseChartLift_codRestrict φ)]
      have heq : (fun v => v.1) ∘ InverseChartLift_codRestrict φ = InverseChartLift φ := by
        apply funext; intro f
        unfold InverseChartLift_codRestrict
        simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, Function.comp_apply,
          Set.val_codRestrict_apply]
      rw [heq]
      rw [contMDiffAt_iff_contDiffAt]
      apply ContDiff.contDiffAt
      apply ContDiff.of_le (InverseChartLiftSmooth φ) le_top
    . have heq : Chart φ = (Chart_PartialHomeomorph φ).toFun := rfl
      rw [heq]
      apply contMDiffAt_of_mem_maximalAtlas
      . apply SmoothManifoldWithCorners.subset_maximalAtlas
        unfold atlas ChartedSpace.atlas instChartedSpaceGrassmannian
        simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, Function.comp_apply,
          Set.mem_setOf_eq]
        existsi φ
        rfl
      . unfold Chart_PartialHomeomorph Chart_PartialEquiv
        simp only
        exact hφ.1


lemma SmoothAt.mapFromGrassmannianI {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*}
[TopologicalSpace H] {Im : ModelWithCorners 𝕜 F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
[SmoothManifoldWithCorners Im M] {n : ℕ∞} {f : Grassmannian 𝕜 E r → M} (v : {v : I → E // LinearIndependent 𝕜 v})
(hf : ContMDiffAt (modelWithCornersSelf 𝕜 (I → E)) Im n (f ∘ (Grassmannian.mkI' 𝕜 hrI) :
{v : I → E // LinearIndependent 𝕜 v} → M) v) :
@ContMDiffAt 𝕜 _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _ _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _
(ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) (Grassmannian 𝕜 E r) _ _ F _ _ H _ Im M _ _ n f
(Grassmannian.mkI' 𝕜 hrI v):= by
  rw [Grassmannian.mk'_vs_mkI', ←Function.comp.assoc, Diffeomorph.contMDiffAt_comp_diffeomorph_iff] at hf
  rw [Grassmannian.mk'_vs_mkI']
  exact SmoothAt.mapFromGrassmannian _ hf
  simp only [le_top]


lemma Smooth.mapFromGrassmannian {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*}
[TopologicalSpace H] {I : ModelWithCorners 𝕜 F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
[SmoothManifoldWithCorners I M] {n : ℕ∞} {f : Grassmannian 𝕜 E r → M}
(hf : ContMDiff (modelWithCornersSelf 𝕜 (Fin r → E)) I n (f ∘ (Grassmannian.mk' 𝕜))) :
@ContMDiff 𝕜 _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _ _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _
(ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) (Grassmannian 𝕜 E r) _ _ F _ _ H _ I M _ _ n f := by
  rw [contMDiff_iff_contMDiffAt] at hf ⊢
  intro x
  rw [←(Grassmannian.mk_rep x)]
  erw [←(Grassmannian.mk'_eq_mk 𝕜)]
  apply SmoothAt.mapFromGrassmannian (⟨Grassmannian.rep x, Grassmannian.rep_linearIndependent x⟩ :
    {v : Fin r → E // LinearIndependent 𝕜 v}) (hf _)


lemma Smooth.mapFromGrassmannianI {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*}
[TopologicalSpace H] {Im : ModelWithCorners 𝕜 F H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
[SmoothManifoldWithCorners Im M] {n : ℕ∞} {f : Grassmannian 𝕜 E r → M}
(hf : ContMDiff (modelWithCornersSelf 𝕜 (I → E)) Im n (f ∘ (Grassmannian.mkI' 𝕜 hrI))) :
@ContMDiff 𝕜 _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _ _ ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) _
(ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) (Grassmannian 𝕜 E r) _ _ F _ _ H _ Im M _ _ n f := by
  rw [Grassmannian.mk'_vs_mkI', ←Function.comp.assoc, Diffeomorph.contMDiff_comp_diffeomorph_iff] at hf
  exact Smooth.mapFromGrassmannian hf
  simp only [le_top]


lemma SmoothAt.mapFromProductGrassmannian {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
[NormedAddCommGroup G] [NormedSpace 𝕜 G] {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
{I : ModelWithCorners 𝕜 F H} {I' : ModelWithCorners 𝕜 G H'} {M N : Type*} [TopologicalSpace M]
[ChartedSpace H M] [SmoothManifoldWithCorners I M] [TopologicalSpace N] [ChartedSpace H' N]
[SmoothManifoldWithCorners I' N] {n : ℕ∞}
{f : N × Grassmannian 𝕜 E r → M}  (v : {v : Fin r → E // LinearIndependent 𝕜 v}) (y : N)
(hf : ContMDiffAt (ModelWithCorners.prod I' (modelWithCornersSelf 𝕜 (Fin r → E))) I n
(f ∘ (Prod.map (fun x => x) (Grassmannian.mk' 𝕜))) (⟨y, v⟩ : N × {v : Fin r → E // LinearIndependent 𝕜 v}))  :
ContMDiffAt (ModelWithCorners.prod I' (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r)) I n f
⟨y, Grassmannian.mk' 𝕜 v⟩ := by
  set φ := Classical.choose (ChoiceOfChartForLift v)
  set φ₁ := (ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) _).comp φ.toContinuousLinearMap
  set hφ := Classical.choose_spec (ChoiceOfChartForLift v)
  set g := (f ∘ Prod.map (fun x => x) (Grassmannian.mk' 𝕜)) ∘ Prod.map (fun x => x) ((InverseChartLift_codRestrict φ)
    ∘ (Chart φ))
  have heq : f =ᶠ[nhds ⟨y, Grassmannian.mk' 𝕜 v⟩] g := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    existsi ⊤ ×ˢ (Goodset φ₁)
    constructor
    . refine IsOpen.mem_nhds ?_ ?_
      . apply IsOpen.prod
        . simp only [Set.top_eq_univ, isOpen_univ]
        . apply GoodsetIsOpen
      . rw [Set.mem_prod, Set.top_eq_univ, and_iff_right (Set.mem_univ _)]
        exact hφ.1
    . intro ⟨y, W⟩ hyW
      rw [Set.mem_prod, Set.top_eq_univ, and_iff_right (Set.mem_univ _)] at hyW
      change W ∈ _ at hyW
      conv => lhs
              rw [IdInChart φ hyW]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ heq
  apply ContMDiffAt.comp (E' := G × (Fin r → E)) (I' := (ModelWithCorners.prod I' (modelWithCornersSelf 𝕜 (Fin r → E))))
  . have heq : (Prod.map (fun x => x) ((InverseChartLift_codRestrict φ) ∘ (Chart φ)))
      ⟨y, Grassmannian.mk' 𝕜 v⟩ = ⟨y, v⟩ := by
      conv => rhs
              rw [←hφ.2]
    rw [heq]
    exact hf
  . apply ContMDiffAt.prod_map
    . apply contMDiffAt_id
    . apply ContMDiffAt.comp (E' := (Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)) (I' := modelWithCornersSelf 𝕜
      ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)))
      . rw [ContMDiffAt_vs_openEmbedding (modelWithCornersSelf 𝕜 ((Fin r → 𝕜) →L[𝕜] (ModelSpace 𝕜 E r)))
          (LinearIndependentToAll 𝕜 E (Fin r)) (InverseChartLift_codRestrict φ)]
        have heq : (fun v => v.1) ∘ InverseChartLift_codRestrict φ = InverseChartLift φ := by
          apply funext; intro f
          unfold InverseChartLift_codRestrict
          simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, Function.comp_apply,
            Set.val_codRestrict_apply]
        rw [heq]
        rw [contMDiffAt_iff_contDiffAt]
        apply ContDiff.contDiffAt
        apply ContDiff.of_le (InverseChartLiftSmooth φ) le_top
      . have heq : Chart φ = (Chart_PartialHomeomorph φ).toFun := rfl
        rw [heq]
        apply contMDiffAt_of_mem_maximalAtlas
        . apply SmoothManifoldWithCorners.subset_maximalAtlas
          unfold atlas ChartedSpace.atlas instChartedSpaceGrassmannian
          simp only [mk'_eq_mk, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst, Function.comp_apply,
            Set.mem_setOf_eq]
          existsi φ
          rfl
        . unfold Chart_PartialHomeomorph Chart_PartialEquiv
          simp only
          exact hφ.1

/- Not too hard to prove, but is it needed ?
lemma SmoothAt.mapFromProductGrassmannianI {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
[NormedAddCommGroup G] [NormedSpace 𝕜 G] {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
{Im : ModelWithCorners 𝕜 F H} {I' : ModelWithCorners 𝕜 G H'} {M N : Type*} [TopologicalSpace M]
[ChartedSpace H M] [SmoothManifoldWithCorners Im M] [TopologicalSpace N] [ChartedSpace H' N]
[SmoothManifoldWithCorners I' N] {n : ℕ∞}
{f : N × Grassmannian 𝕜 E r → M}  (v : {v : I → E // LinearIndependent 𝕜 v}) (y : N)
(hf : ContMDiffAt (ModelWithCorners.prod I' (modelWithCornersSelf 𝕜 (I → E))) Im n
(f ∘ (Prod.map (fun x => x) (Grassmannian.mkI' 𝕜 hrI))) (⟨y, v⟩ : N × {v : I → E // LinearIndependent 𝕜 v}))  :
ContMDiffAt (ModelWithCorners.prod I' (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r)) Im n f
⟨y, Grassmannian.mkI' 𝕜 hrI v⟩ := by
  sorry
-/

lemma Smooth.mapFromProductGrassmannian {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
[NormedAddCommGroup G] [NormedSpace 𝕜 G] {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
{I : ModelWithCorners 𝕜 F H} {I' : ModelWithCorners 𝕜 G H'} {M N : Type*} [TopologicalSpace M]
[ChartedSpace H M] [SmoothManifoldWithCorners I M] [TopologicalSpace N] [ChartedSpace H' N]
[SmoothManifoldWithCorners I' N] {n : ℕ∞}
{f : N × Grassmannian 𝕜 E r → M}
(hf : ContMDiff (ModelWithCorners.prod I' (modelWithCornersSelf 𝕜 (Fin r → E))) I n
(f ∘ (Prod.map (fun x => x) (Grassmannian.mk' 𝕜))))  :
ContMDiff (ModelWithCorners.prod I' (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r)) I n f := by
  rw [contMDiff_iff_contMDiffAt] at hf ⊢
  intro ⟨y, x⟩
  rw [←(Grassmannian.mk_rep x)]
  erw [←(Grassmannian.mk'_eq_mk 𝕜)]
  apply SmoothAt.mapFromProductGrassmannian
  exact hf _




/- We define the action of GL(E) on the grassmannian and prove that it is a smooth action.-/

lemma ActionGL_aux (f : (E →L[𝕜] E)ˣ) {v : Fin r → E} (hv : LinearIndependent 𝕜 v) :
LinearIndependent 𝕜 (f.1 ∘ v) := by
  set g := ContinuousLinearEquiv.ofUnit f
  change LinearIndependent 𝕜 (g ∘ v)
  apply LinearIndependent.map' hv
  rw [LinearMap.ker_eq_bot]
  apply ContinuousLinearEquiv.injective

variable (𝕜 E r)

noncomputable def ActionGL : (E →L[𝕜] E)ˣ × (Grassmannian 𝕜 E r) → (Grassmannian 𝕜 E r) :=
fun ⟨g, W⟩ => Grassmannian.mk 𝕜 (g.1 ∘ (Grassmannian.rep W)) (ActionGL_aux g (Grassmannian.rep_linearIndependent W))


/- We lift this action to {v : Fin r → E // LinearIndependent 𝕜 v}.-/

def ActionGLLift : (E →L[𝕜] E)ˣ × {v : Fin r → E // LinearIndependent 𝕜 v} →
{v : Fin r → E // LinearIndependent 𝕜 v} := by
  intro ⟨g, ⟨v, hv⟩⟩
  refine ⟨g.1 ∘ v, ActionGL_aux g hv⟩

/- We prove that the left is a lift.-/

lemma ActionGLLift_IsLift :
(ActionGL 𝕜 E r ∘ Prod.map (fun x => x) (Grassmannian.mk' 𝕜)) = Grassmannian.mk' 𝕜 ∘ ActionGLLift 𝕜 E r := by
  apply funext
  intro ⟨g, ⟨v, hv⟩⟩
  unfold ActionGL ActionGLLift
  simp only [Function.comp_apply, Prod_map, mk'_eq_mk]
  rw [Grassmannian.mk_eq_mk_iff_span]
  have heq := Grassmannian.mk_rep (Grassmannian.mk 𝕜 v hv)
  rw [Grassmannian.mk_eq_mk_iff_span] at heq
  rw [Set.range_comp, Set.range_comp, ←Submodule.map_span, ←Submodule.map_span]
  rw [heq]


def ActionGLLift_extended : ((E →L[𝕜] E) × (Fin r → E)) → (Fin r → E) := fun p => p.1 ∘ p.2

lemma ActionGLLift_extended_IsSmooth : ContDiff 𝕜 ⊤ (ActionGLLift_extended 𝕜 E r) := by
  have heq : ActionGLLift_extended 𝕜 E r = fun p => (fun i => p.1 (p.2 i)) := by
    apply funext
    intro ⟨g, v⟩
    unfold ActionGLLift_extended
    ext i
    simp only [Function.comp_apply]
  rw [heq, contDiff_pi]
  intro i
  have heq : (fun (p : (E →L[𝕜] E) × (Fin r → E)) => p.1 (p.2 i)) = (fun (p : (E →L[𝕜] E) × E) => p.1 p.2)
    ∘ Prod.map (fun g => g) (fun (v : Fin r → E) => v i) := by
    ext ⟨g, v⟩
    simp only [Function.comp_apply, Prod_map]
  rw [heq]
  apply ContDiff.comp
  . apply IsBoundedBilinearMap.contDiff
    apply isBoundedBilinearMap_apply
  . apply ContDiff.prod_map
    . apply contDiff_id
    . apply contDiff_apply

/- To get the smooth manifold structure on (E →L[𝕜] E)ˣ, we need E to be complete.-/

variable [CompleteSpace E]

/- Smoothness of the lifted action.-/


lemma ActionGLLift_isSmooth : ContMDiff (ModelWithCorners.prod (modelWithCornersSelf 𝕜 (E →L[𝕜] E))
  (modelWithCornersSelf 𝕜 (Fin r → E))) (modelWithCornersSelf 𝕜 (Fin r → E)) ⊤ (ActionGLLift 𝕜 E r) := by
  rw [ContMDiff_vs_openEmbedding]
  have heq : (fun v => v.1) ∘ (ActionGLLift 𝕜 E r) = (ActionGLLift_extended 𝕜 E r) ∘
    (Prod.map (fun g => g.1) (fun v => v.1)) := by
    apply funext
    intro ⟨g, v⟩
    unfold ActionGLLift ActionGLLift_extended
    simp only [Function.comp_apply, Prod_map]
  rw [heq]
  apply ContMDiff.comp (I' := ModelWithCorners.prod (modelWithCornersSelf 𝕜 (E →L[𝕜] E))
    (modelWithCornersSelf 𝕜 (Fin r → E)))
  . rw [←modelWithCornersSelf_prod]
    erw [contMDiff_iff_contDiff]
    apply ActionGLLift_extended_IsSmooth
  . apply ContMDiff.prod_map
    . apply contMDiffOpenEmbedding
    . apply contMDiffOpenEmbedding


/- Smoothness of the action.-/

lemma ActionGLIsSmooth : ContMDiff (ModelWithCorners.prod (modelWithCornersSelf 𝕜 (E →L[𝕜] E))
(ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r)) (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r) ⊤ (ActionGL 𝕜 E r) := by
  apply Smooth.mapFromProductGrassmannian
  rw [ActionGLLift_IsLift]
  apply ContMDiff.comp (I' := modelWithCornersSelf 𝕜 (Fin r → E))
  . apply Smooth.quotientMap
  . apply ActionGLLift_isSmooth



end SmoothMaps

end Grassmannian
