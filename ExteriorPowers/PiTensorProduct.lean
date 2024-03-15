import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.LinearAlgebra.PiTensorProduct

variable {ι : Type*} [Fintype ι]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {R₁ R₂ : Type*}

variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped TensorProduct

open BigOperators

namespace PiTensorProduct

@[simps!]
noncomputable def toDualMultilinearMap : (⨂[𝕜] i, E i) →ₗ[𝕜] MultilinearMap 𝕜 E F →ₗ[𝕜] F :=
  LinearMap.flip (lift (R := 𝕜) (s := E) (E := F))

@[simp]
lemma toDualMultilinearMap_apply_tprod (m : (i : ι) → E i) (f : MultilinearMap 𝕜 E F) :
    toDualMultilinearMap (⨂ₜ[𝕜] i, m i) f = f m := by
  simp only [toDualMultilinearMap_apply_apply, lift.tprod]

lemma toDualMultilinearMap_bound (x : ⨂[𝕜] i, E i) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (f : ContinuousMultilinearMap 𝕜 E F),
    ‖toDualMultilinearMap x f.toMultilinearMap‖ ≤ C * ‖f‖ := by
  induction' x using PiTensorProduct.induction_on with r m x y hx hy
  · existsi ‖r‖ * ∏ i : ι, ‖m i‖
    constructor
    · exact mul_nonneg (norm_nonneg r) (Finset.prod_nonneg (fun i _ ↦ norm_nonneg (m i)))
    · intro f
      simp only [map_smul, LinearMap.smul_apply, toDualMultilinearMap_apply_apply, lift.tprod,
        ContinuousMultilinearMap.coe_coe, norm_smul]
      rw [mul_assoc, mul_comm _ ‖f‖]
      exact le_trans (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm f m)
        (norm_nonneg r)) (le_refl _)
  · obtain ⟨Cx, hCx⟩ := hx; obtain ⟨Cy, hCy⟩ := hy
    existsi Cx + Cy
    constructor
    · exact add_nonneg hCx.1 hCy.1
    · intro f
      rw [map_add, add_mul]
      refine le_trans (norm_add_le _ _) (add_le_add (hCx.2 f) (hCy.2 f))

@[simps!]
noncomputable def toDualContinuousMultilinearMap : (⨂[𝕜] i, E i) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun x := {(toDualMultilinearMap x) ∘ₗ ContinuousMultilinearMap.toMultilinearMapLinear with
    cont := by
      obtain ⟨C, hC⟩ := toDualMultilinearMap_bound x (F := F)
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      apply AddMonoidHomClass.continuous_of_bound _ C
      intro f
      simp only [LinearMap.coe_comp, Function.comp_apply,
        ContinuousMultilinearMap.toMultilinearMapLinear_apply]
      exact hC.2 f}
  map_add' x y := by
    ext f
    simp only [map_add, ContinuousLinearMap.coe_mk', LinearMap.coe_comp, Function.comp_apply,
      ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.add_apply,
      toDualMultilinearMap_apply_apply, ContinuousLinearMap.add_apply]
  map_smul' a x := by
    ext f
    simp only [map_smul, ContinuousLinearMap.coe_mk', LinearMap.coe_comp, Function.comp_apply,
      ContinuousMultilinearMap.toMultilinearMapLinear_apply, LinearMap.smul_apply,
      toDualMultilinearMap_apply_apply, RingHom.id_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply]

@[simp]
lemma toDualContinuousMultilinearMap_apply_tprod (m : (i : ι) → E i)
    (f : ContinuousMultilinearMap 𝕜 E F) :
    toDualContinuousMultilinearMap (⨂ₜ[𝕜] i, m i) f = f m := by
  simp only [toDualContinuousMultilinearMap_apply_toFun, lift.tprod,
    ContinuousMultilinearMap.coe_coe]

lemma toDualMultilinearMap_bound' (x : ⨂[𝕜] i, E i) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (G : Type*) [SeminormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : ContinuousMultilinearMap 𝕜 E G),
    ‖toDualMultilinearMap x f.toMultilinearMap‖ ≤ C * ‖f‖ := by
  induction' x using PiTensorProduct.induction_on with r m x y hx hy
  · existsi ‖r‖ * ∏ i : ι, ‖m i‖
    constructor
    · exact mul_nonneg (norm_nonneg r) (Finset.prod_nonneg (fun i _ ↦ norm_nonneg (m i)))
    · intro _ _ _ f
      simp only [map_smul, LinearMap.smul_apply, toDualMultilinearMap_apply_apply, lift.tprod,
        ContinuousMultilinearMap.coe_coe, norm_smul]
      rw [mul_assoc, mul_comm _ ‖f‖]
      exact le_trans (mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm f m)
        (norm_nonneg r)) (le_refl _)
  · obtain ⟨Cx, hCx⟩ := hx; obtain ⟨Cy, hCy⟩ := hy
    existsi Cx + Cy
    constructor
    · exact add_nonneg hCx.1 hCy.1
    · intro _ _ _ f
      rw [map_add, add_mul]
      refine le_trans (norm_add_le _ _) (add_le_add (hCx.2 _ f) (hCy.2 _ f))

noncomputable example : Seminorm 𝕜 (⨂[𝕜] i, E i) :=
  Seminorm.comp
  {toFun := fun x ↦ ‖x‖
   map_zero' := by aesop
   add_le' := fun x y ↦ by simp?
   neg' := sorry
   smul' := sorry}
  (toDualContinuousMultilinearMap (F := F) (𝕜 := 𝕜) (E := E))

end PiTensorProduct
