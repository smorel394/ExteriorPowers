import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.LinearAlgebra.PiTensorProduct

variable {ι : Type*} [Fintype ι]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {R₁ R₂ : Type*}

variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 F]

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

lemma toDualContinuousAlternatingMap_bound (x : ⨂[𝕜] i, E i) :
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

#exit


variable (𝕜 E r)

def toDualContinuousAlternatingMapLinear :
    ⋀[𝕜]^r E →ₗ[𝕜] NormedSpace.Dual 𝕜 (E [⋀^(Fin r)]→L[𝕜] 𝕜) :=
{
  toFun := fun x => LinearMap.mkContinuousOfExistsBound (toDualContinuousAlternatingMap x)
    (by obtain ⟨C, h⟩ := toDualContinuousAlternatingMap_bound x (F :=𝕜); existsi C; exact h.2)
  map_add' := fun x y => by ext f; simp only [toDualContinuousAlternatingMap_add,
    LinearMap.mkContinuousOfExistsBound_apply, LinearMap.add_apply, ContinuousLinearMap.add_apply]
  map_smul' := fun a x => by ext f; simp only [toDualContinuousAlternatingMap_smul,
    LinearMap.mkContinuousOfExistsBound_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
}


end PiTensorProduct
