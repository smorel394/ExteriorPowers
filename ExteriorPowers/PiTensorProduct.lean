import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.LinearAlgebra.PiTensorProduct

variable {ι : Type*} [Fintype ι]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped TensorProduct

open BigOperators

namespace PiTensorProduct

lemma toDualMultilinearMap_bound (x : ⨂[𝕜] i, E i) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (G : Type*) [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G),
    ‖lift f.toMultilinearMap x‖ ≤ C * ‖f‖ := by
  induction' x using PiTensorProduct.induction_on with r m x y hx hy
  · existsi ‖r‖ * ∏ i : ι, ‖m i‖
    constructor
    · exact mul_nonneg (norm_nonneg r) (Finset.prod_nonneg (fun i _ ↦ norm_nonneg (m i)))
    · intro G _ _ f
      simp only [map_smul, lift.tprod, ContinuousMultilinearMap.coe_coe]
      rw [mul_assoc, mul_comm _ ‖f‖, norm_smul]
      exact le_trans (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm f m)
        (norm_nonneg r)) (le_refl _)
  · obtain ⟨Cx, hCx⟩ := hx; obtain ⟨Cy, hCy⟩ := hy
    existsi Cx + Cy
    constructor
    · exact add_nonneg hCx.1 hCy.1
    · intro G _ _ f
      rw [map_add, add_mul]
      refine le_trans (norm_add_le _ _) (add_le_add (hCx.2 _ f) (hCy.2 _ f))

@[simps!]
noncomputable def toDualContinuousMultilinearMap : (⨂[𝕜] i, E i) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun x := LinearMap.mkContinuousOfExistsBound
    ((LinearMap.flip (lift (R := 𝕜) (s := E) (E := F)).toLinearMap x) ∘ₗ
    ContinuousMultilinearMap.toMultilinearMapLinear) (by
      obtain ⟨C, hC⟩ := toDualMultilinearMap_bound x
      existsi C
      intro f
      simp only [LinearMap.coe_comp, Function.comp_apply,
        ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.flip_apply,
        LinearEquiv.coe_coe]
      exact hC.2 F f)
  map_add' x y := by
    ext _
    simp only [map_add, LinearMap.mkContinuousOfExistsBound_apply, LinearMap.coe_comp,
      Function.comp_apply, ContinuousMultilinearMap.toMultilinearMapLinear_apply,
      LinearMap.add_apply, LinearMap.flip_apply, LinearEquiv.coe_coe, ContinuousLinearMap.add_apply]
  map_smul' a x := by
    ext _
    simp only [map_smul, LinearMap.mkContinuousOfExistsBound_apply, LinearMap.coe_comp,
      Function.comp_apply, ContinuousMultilinearMap.toMultilinearMapLinear_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, LinearEquiv.coe_coe, RingHom.id_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply]

@[simp]
lemma toDualContinuousMultilinearMap_tprod_apply (m : (i : ι) → E i)
    (f : ContinuousMultilinearMap 𝕜 E F) :
    toDualContinuousMultilinearMap (⨂ₜ[𝕜] i, m i) f = f m := by
  simp only [toDualContinuousMultilinearMap_apply_toFun, lift.tprod,
    ContinuousMultilinearMap.coe_coe]

noncomputable def injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i) :=
  sSup {p | ∃ (G : Type (max (max u_1 u_2) u_3)) (_ : SeminormedAddCommGroup G)
  (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
  (toDualContinuousMultilinearMap (F := G) (𝕜 := 𝕜) (E := E))}

lemma dualSeminorms_bounded : BddAbove {p | ∃ (G : Type (max (max u_1 u_2) u_3))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G),
    p = Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap (F := G) (𝕜 := 𝕜) (E := E))} := by
  rw [Seminorm.bddAbove_iff]
  set bound : (⨂[𝕜] i, E i) → ℝ :=
    fun x ↦ Classical.choose (toDualMultilinearMap_bound x)
  existsi bound
  rw [mem_upperBounds]
  intro p hp
  simp only [Set.mem_image] at hp
  let ⟨q, hq⟩ := hp
  simp only [Set.mem_setOf_eq] at hq
  intro x
  rw [← hq.2]
  obtain ⟨⟨G, G₁, ⟨G₂, h⟩⟩⟩ := hq
  letI := G₁
  letI := G₂
  rw [h]
  simp only [Seminorm.comp_apply, ge_iff_le]
  let hbound := Classical.choose_spec (toDualMultilinearMap_bound x)
  exact ContinuousLinearMap.opNorm_le_bound _ hbound.1 (fun f ↦ by
    simp only [toDualContinuousMultilinearMap_apply_toFun]
    exact hbound.2 G f)

@[simp]
theorem injectiveSeminorm_apply (x : ⨂[𝕜] i, E i) :
    injectiveSeminorm x = ⨆ p : {p | ∃ (G : Type (max (max u_1 u_2) u_3))
    (_ : SeminormedAddCommGroup G) (_ : NormedSpace 𝕜 G), p = Seminorm.comp (normSeminorm 𝕜
    (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
    (toDualContinuousMultilinearMap (F := G) (𝕜 := 𝕜) (E := E))}, p.1 x := by
  refine Seminorm.sSup_apply dualSeminorms_bounded

theorem injectiveSeminorm_bound (f : ContinuousMultilinearMap 𝕜 E F) (x : ⨂[𝕜] i, E i) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * injectiveSeminorm x := by
  set G := (⨂[𝕜] i, E i) ⧸ LinearMap.ker (lift f.toMultilinearMap)
  set G' := LinearMap.range (lift f.toMultilinearMap)
  set e := LinearMap.quotKerEquivRange (lift f.toMultilinearMap)
  letI := SeminormedAddCommGroup.induced G G' e
  letI := NormedSpace.induced 𝕜 G G' e
  set f'₀ := lift.symm (e.symm.toLinearMap ∘ₗ LinearMap.rangeRestrict (lift f.toMultilinearMap))
  have hf'₀ : ∀ (x : Π (i : ι), E i), ‖f'₀ x‖ ≤ ‖f‖ * ∏ i, ‖x i‖ := fun x ↦ by
    change ‖e (f'₀ x)‖ ≤ _
    simp only [lift_symm, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, Submodule.coe_norm,
        LinearMap.codRestrict_apply, lift.tprod, ContinuousMultilinearMap.coe_coe, e, f'₀]
    exact f.le_opNorm x
  set f' := MultilinearMap.mkContinuous f'₀ ‖f‖ hf'₀
  have hnorm : ‖f'‖ ≤ ‖f‖ := (f'.opNorm_le_iff (norm_nonneg f)).mpr hf'₀
  have heq : e (lift f'.toMultilinearMap x) = lift f.toMultilinearMap x := by
    induction' x using PiTensorProduct.induction_on with a m _ _ hx hy
    · simp only [lift_symm, map_smul, lift.tprod, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, SetLike.val_smul,
      LinearMap.codRestrict_apply, f', f'₀]
    · simp only [map_add, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, hx, hy]
  suffices h : ‖lift f'.toMultilinearMap x‖ ≤ ‖f'‖ * injectiveSeminorm x by
    change ‖(e (lift f'.toMultilinearMap x)).1‖ ≤ _ at h
    rw [heq] at h
    refine le_trans h (mul_le_mul_of_nonneg_right hnorm (apply_nonneg _ _))
  have hle : Seminorm.comp (normSeminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G →L[𝕜] G))
      (toDualContinuousMultilinearMap (F := G) (𝕜 := 𝕜) (E := E)) ≤ injectiveSeminorm := by
    simp only [injectiveSeminorm]
    refine le_csSup dualSeminorms_bounded ?_
    rw [Set.mem_setOf]
    existsi G, inferInstance, inferInstance
    rfl
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hle x) (norm_nonneg f'))
  simp only [Seminorm.comp_apply, coe_normSeminorm, ← toDualContinuousMultilinearMap_apply_apply]
  rw [mul_comm]
  exact ContinuousLinearMap.le_opNorm _ _

theorem injectiveSeminorm_tprod_le (m : Π (i : ι), E i) :
    injectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖ := by
  rw [injectiveSeminorm_apply]
  apply csSup_le
  · rw [Set.range_nonempty_iff_nonempty]
    simp only [Set.coe_setOf, nonempty_subtype]
    existsi 0, PUnit, inferInstance, inferInstance
    ext x
    simp only [Seminorm.zero_apply, Seminorm.comp_apply, coe_normSeminorm]
    have heq : toDualContinuousMultilinearMap (F := PUnit) x = 0 := by ext _
    rw [heq, norm_zero]
  · intro a ha
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop] at ha
    let ⟨p, ⟨⟨G, _, _, hp⟩, hpa⟩⟩ := ha
    rw [← hpa, hp]
    simp only [Seminorm.comp_apply, coe_normSeminorm, ge_iff_le]
    rw [ContinuousLinearMap.opNorm_le_iff (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))]
    intro f
    simp only [toDualContinuousMultilinearMap_apply_toFun, lift.tprod,
        ContinuousMultilinearMap.coe_coe]
    rw [mul_comm]
    exact ContinuousMultilinearMap.le_opNorm f m

noncomputable instance : SeminormedAddCommGroup (⨂[𝕜] i, E i) :=
  AddGroupSeminorm.toSeminormedAddCommGroup injectiveSeminorm.toAddGroupSeminorm

noncomputable instance : NormedSpace 𝕜 (⨂[𝕜] i, E i) where
  norm_smul_le a x := by
    change injectiveSeminorm.toFun (a • x) ≤ _
    rw [injectiveSeminorm.smul']
    rfl

@[simps]
noncomputable def liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F where
  toFun f := LinearMap.mkContinuous (lift f.toMultilinearMap) ‖f‖
    (fun x ↦ injectiveSeminorm_bound f x)
  map_add' f g := by ext _; simp only [ContinuousMultilinearMap.toMultilinearMap_add, map_add,
    LinearMap.mkContinuous_apply, LinearMap.add_apply, ContinuousLinearMap.add_apply]
  map_smul' a f := by ext _; simp only [ContinuousMultilinearMap.toMultilinearMap_smul, map_smul,
    LinearMap.mkContinuous_apply, LinearMap.smul_apply, RingHom.id_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  invFun l := MultilinearMap.mkContinuous (lift.symm l.toLinearMap) ‖l‖ (fun x ↦ by
    simp only [lift_symm, LinearMap.compMultilinearMap_apply, ContinuousLinearMap.coe_coe]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_left ?_
      (norm_nonneg l))
    exact injectiveSeminorm_tprod_le x)
  left_inv f := by ext x; simp only [LinearMap.mkContinuous_coe, LinearEquiv.symm_apply_apply,
      MultilinearMap.coe_mkContinuous, ContinuousMultilinearMap.coe_coe]
  right_inv l := by
    rw [← ContinuousLinearMap.coe_inj]
    apply PiTensorProduct.ext; ext m
    simp only [lift_symm, LinearMap.mkContinuous_coe, LinearMap.compMultilinearMap_apply,
      lift.tprod, ContinuousMultilinearMap.coe_coe, MultilinearMap.coe_mkContinuous,
      ContinuousLinearMap.coe_coe]

@[simps!]
noncomputable def liftIsometry  : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F :=
  {liftEquiv with
   norm_map' := by
     intro f
     refine le_antisymm ?_ ?_
     · simp only [liftEquiv_apply]
       exact LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
     · conv_lhs => rw [← liftEquiv.left_inv f]
       simp only [LinearEquiv.invFun_eq_symm, liftEquiv_symm_apply]
       exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _}

noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i) :=
  liftIsometry.invFun (ContinuousLinearMap.id 𝕜 _)


end PiTensorProduct
