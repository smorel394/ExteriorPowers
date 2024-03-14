import Mathlib.Analysis.NormedSpace.Dual
import ExteriorPowers.ExteriorPower
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic

open ExteriorAlgebra


variable {𝕜 E F ι: Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Fintype ι] {r : ℕ}

namespace ContinuousAlternatingMap

noncomputable instance instSeminormedAddCommGroupContinuousAlternatingMap :
    SeminormedAddCommGroup (E [⋀^(Fin r)]→L[𝕜] F) :=
  SeminormedAddCommGroup.induced (E [⋀^(Fin r)]→L[𝕜] F) (ContinuousMultilinearMap 𝕜
  (fun _ ↦ E) F) (toContinuousMultilinearMapLinear (R := 𝕜))

noncomputable instance instNormedSpaceexteriorPower : NormedSpace 𝕜 (E [⋀^(Fin r)]→L[𝕜] F) :=
  NormedSpace.induced 𝕜 (E [⋀^(Fin r)]→L[𝕜] F) (ContinuousMultilinearMap 𝕜 (fun _ ↦ E) F)
  (toContinuousMultilinearMapLinear (R := 𝕜))

end ContinuousAlternatingMap

namespace exteriorPower

def toDualContinuousAlternatingMap (x : ⋀[𝕜]^r E) : E [⋀^(Fin r)]→L[𝕜] F →ₗ[𝕜] F :=
{
 toFun := fun f => liftAlternating r f.toAlternatingMap x
 map_add' := fun f g => by simp only [ContinuousAlternatingMap.toAlternatingMap_add, map_add,
   LinearMap.add_apply]
 map_smul' := fun a f => by simp only [ContinuousAlternatingMap.toAlternatingMap_smul, map_smul,
   LinearMap.smul_apply, RingHom.id_apply]
 }

@[simp]
lemma toDualContinuousAlternatingMap_apply (x : ⋀[𝕜]^r E) (f : E [⋀^(Fin r)]→L[𝕜] F):
toDualContinuousAlternatingMap x f = liftAlternating r f.toAlternatingMap x := rfl


@[simp]
lemma toDualContinuousAlternatingMap_zero :
    toDualContinuousAlternatingMap (F := F) (0 : ⋀[𝕜]^r E) = 0 := by
  ext f
  unfold toDualContinuousAlternatingMap
  simp only [map_zero, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]

@[simp]
lemma toDualContinuousAlternatingMap_add (x y : ⋀[𝕜]^r E) :
toDualContinuousAlternatingMap (F := F) (x + y) = toDualContinuousAlternatingMap x + toDualContinuousAlternatingMap y := by
  ext f
  unfold toDualContinuousAlternatingMap
  simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]

@[simp]
lemma toDualContinuousAlternatingMap_smul (a : 𝕜) (x : ⋀[𝕜]^r E) :
toDualContinuousAlternatingMap (F := F) (a • x) = a • toDualContinuousAlternatingMap x := by
  ext f
  unfold toDualContinuousAlternatingMap
  simp only [map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]

@[simp]
lemma toDualContinuousAlternatingMap_apply_ιMulti (m : Fin r → E)
    (f : E [⋀^(Fin r)]→L[𝕜] F) :
toDualContinuousAlternatingMap (ιMulti 𝕜 r m) f = f m := by
  unfold toDualContinuousAlternatingMap
  simp only [liftAlternating_apply_ιMulti, AlternatingMap.coe_mk, ContinuousMultilinearMap.coe_coe,
    ContinuousAlternatingMap.coe_toContinuousMultilinearMap, LinearMap.coe_mk, AddHom.coe_mk]

lemma toDualContinuousAlternatingMap_bound (x : ⋀[𝕜]^r E) :
∃ (C : ℝ), 0 ≤ C ∧ ∀ (f : E [⋀^(Fin r)]→L[𝕜] F), ‖toDualContinuousAlternatingMap x f‖ ≤ C * ‖f‖ := by
  have hx : x ∈ (⊤ : Submodule 𝕜 (⋀[𝕜]^r E)) := by simp only [Submodule.mem_top]
  rw [← exteriorPower.ιMulti_span] at hx
  apply Submodule.span_induction hx (p := fun x => ∃ (C : ℝ), 0 ≤ C ∧ ∀ (f : E [⋀^(Fin r)]→L[𝕜] F),
    ‖toDualContinuousAlternatingMap x f‖ ≤ C * ‖f‖)
  . intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨m, hmx⟩ := hx
    existsi Finset.prod Finset.univ (fun (i : Fin r) => ‖m i‖)
    rw [and_iff_right (Finset.prod_nonneg (fun i _ => norm_nonneg _))]
    intro f
    rw [←hmx, toDualContinuousAlternatingMap_apply_ιMulti, mul_comm]
    exact ContinuousMultilinearMap.le_opNorm f.toContinuousMultilinearMap m
  . existsi 0
    rw [and_iff_right (le_refl _)]
    intro f
    simp only [toDualContinuousAlternatingMap_zero, LinearMap.zero_apply, norm_zero, zero_mul,
      le_refl]
  . intro x y ⟨Cx, hx⟩ ⟨Cy, hy⟩
    existsi Cx + Cy
    rw [and_iff_right (add_nonneg hx.1 hy.1)]
    intro f
    rw [toDualContinuousAlternatingMap_add, LinearMap.add_apply, add_mul]
    exact le_trans (norm_add_le _ _) (add_le_add (hx.2 f) (hy.2 f))
  . intro a x ⟨C, h⟩
    existsi ‖a‖ * C
    rw [and_iff_right (mul_nonneg (norm_nonneg a) h.1)]
    intro f
    rw [toDualContinuousAlternatingMap_smul, LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.2 f) (norm_nonneg a)

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

variable {𝕜 E r}

@[simp]
lemma toDualContinuousAlternatingMapLinear_apply (x : ⋀[𝕜]^r E) (f : E [⋀^(Fin r)]→L[𝕜] 𝕜):
toDualContinuousAlternatingMapLinear 𝕜 E r x f = liftAlternating r f.toAlternatingMap x := by
  unfold toDualContinuousAlternatingMapLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mkContinuousOfExistsBound_apply,
    toDualContinuousAlternatingMap_apply]

@[simp]
lemma toDualContinuousAlternatingMapLinear_apply_ιMulti (m : Fin r → E) (f : E [⋀^(Fin r)]→L[𝕜] 𝕜) :
toDualContinuousAlternatingMapLinear 𝕜 E r (ιMulti 𝕜 r m) f = f m := by
  unfold toDualContinuousAlternatingMapLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mkContinuousOfExistsBound_apply,
    toDualContinuousAlternatingMap_apply_ιMulti]


noncomputable instance instSeminormedAddCommGroupexteriorPower :
    SeminormedAddCommGroup (⋀[𝕜]^r E) :=
  SeminormedAddCommGroup.induced (⋀[𝕜]^r E) (NormedSpace.Dual 𝕜 (E [⋀^(Fin r)]→L[𝕜] 𝕜))
  (toDualContinuousAlternatingMapLinear 𝕜 E r)

noncomputable instance instNormedSpaceExteriorPower : NormedSpace 𝕜 (⋀[𝕜]^r E) :=
NormedSpace.induced 𝕜 (⋀[𝕜]^r E) (NormedSpace.Dual 𝕜 (E [⋀^(Fin r)]→L[𝕜] 𝕜))
(toDualContinuousAlternatingMapLinear 𝕜 E r)


lemma SeminormexteriorPower_apply_ιMulti_le (m : Fin r → E) :
‖ιMulti 𝕜 r m‖ ≤ Finset.prod Finset.univ (fun (i : Fin r) => ‖m i‖) := by
  change ‖toDualContinuousAlternatingMapLinear 𝕜 E r (ιMulti 𝕜 r m)‖ ≤ _
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg (fun i _ => norm_nonneg _))
  intro f
  rw [toDualContinuousAlternatingMapLinear_apply_ιMulti, mul_comm]
  exact ContinuousMultilinearMap.le_opNorm f.toContinuousMultilinearMap m

noncomputable def ιMulti_continuous : E [⋀^(Fin r)]→L[𝕜] (⋀[𝕜]^r E) :=
  {MultilinearMap.mkContinuous (ιMulti 𝕜 r (M := E)) 1
  (fun m ↦ by rw [one_mul]; exact SeminormexteriorPower_apply_ιMulti_le (𝕜 := 𝕜) m) with
  map_eq_zero_of_eq' := fun v _ _ h h' ↦ by simp only [MultilinearMap.toFun_eq_coe,
    ContinuousMultilinearMap.coe_coe, MultilinearMap.coe_mkContinuous,
    AlternatingMap.coe_multilinearMap]
                                            exact (ιMulti 𝕜 r).map_eq_zero_of_eq v h h'}

@[simp]
lemma ιMulti_continuous_apply (v : Fin r → E) :
ιMulti_continuous v = ιMulti 𝕜 r v := by
  simp only [ιMulti_continuous, ContinuousAlternatingMap.coe_mk, MultilinearMap.coe_mkContinuous,
    AlternatingMap.coe_multilinearMap]

lemma ιMulti_continuous_norm : ‖ιMulti_continuous (𝕜 := 𝕜) (E := E) (r := r)‖ ≤ 1 :=
  ContinuousMultilinearMap.opNorm_le_bound _ zero_le_one
    (fun m ↦ by rw [one_mul]; exact SeminormexteriorPower_apply_ιMulti_le (𝕜 := 𝕜) m)

lemma liftContinuousAlternating_normAt (f : E [⋀^(Fin r)]→L[𝕜] 𝕜) (x : ⋀[𝕜]^r E) :
‖exteriorPower.liftAlternating r f.toAlternatingMap x‖ ≤  ‖f‖ * ‖x‖ := by
  rw [←toDualContinuousAlternatingMapLinear_apply, mul_comm]
  exact ContinuousLinearMap.le_opNorm _ f

variable (r 𝕜 E)

def liftContinuousAlternating : (E [⋀^(Fin r)]→L[𝕜] 𝕜) →ₗ[𝕜] ⋀[𝕜]^r E →L[𝕜] 𝕜 :=
{toFun := fun f =>
⟨liftAlternating r f.toAlternatingMap,
AddMonoidHomClass.continuous_of_bound (exteriorPower.liftAlternating r f.toAlternatingMap) ‖f‖
    (fun x => liftContinuousAlternating_normAt f x)⟩
 map_add' := by intro f g; ext _; simp only [ContinuousAlternatingMap.toAlternatingMap_add, map_add,
   ContinuousLinearMap.coe_mk', LinearMap.add_apply, ContinuousLinearMap.add_apply]
 map_smul' := by intro a d; ext _; simp only [ContinuousAlternatingMap.toAlternatingMap_smul,
   map_smul, ContinuousLinearMap.coe_mk', LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
   ContinuousLinearMap.coe_smul', Pi.smul_apply]
}

variable {r 𝕜 E}

lemma liftContinuousAlternating_norm_le (f : E [⋀^(Fin r)]→L[𝕜] 𝕜) :
‖liftContinuousAlternating 𝕜 E r f‖ ≤  ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  . exact norm_nonneg f
  . exact fun x => liftContinuousAlternating_normAt f x

lemma liftCOntinuousAlternating_continuous : Continuous (liftContinuousAlternating 𝕜 E r) :=
AddMonoidHomClass.continuous_of_bound
(liftContinuousAlternating 𝕜 E r) 1 (fun f => by rw [one_mul]; exact liftContinuousAlternating_norm_le f)

variable (r 𝕜 E)


noncomputable def liftContinuousAlternating_invFun :
    (⋀[𝕜]^r E →L[𝕜] 𝕜) →ₗ[𝕜] (E [⋀^(Fin r)]→L[𝕜] 𝕜) :=
{toFun := fun L => L.compContinuousAlternatingMap ιMulti_continuous
 map_add' := fun f g => by ext _; simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe,
   Function.comp_apply, ContinuousLinearMap.add_apply, ContinuousAlternatingMap.add_apply]
 map_smul' := fun a f => by ext _; simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe,
   ContinuousLinearMap.coe_smul', Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
   ContinuousAlternatingMap.smul_apply]
}


#exit

variable {r 𝕜 E}

-- TODO : the continuous linear equivalence between ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r) and the
-- continuous dual of exteriorPower 𝕜 E r. See ExteriorNormedSeparatingDual.lean for now.

noncomputable def continuousAlternatingFormOfFamily (f : (i : Fin r) → (E →L[𝕜] 𝕜)) :
E [⋀^(Fin r)]→L[𝕜] 𝕜 :=
AlternatingMap.mkContinuousAlternating (alternatingFormOfFamily 𝕜 r (fun i => (f i).toLinearMap))
((Nat.factorial r) * (Finset.prod Finset.univ (fun (i : Fin r) => ‖f i‖)))
(by intro m
    simp only [alternatingFormOfFamily_apply, linearFormOfFamily_apply, toTensorPower_apply_ιMulti,
      map_sum, LinearMap.map_smul_of_tower, TensorPower.linearFormOfFamily_apply_tprod,
      ContinuousLinearMap.coe_coe]
    refine le_trans (norm_sum_le _ _) ?_
    conv_rhs => congr
                congr
                rw [←(Fintype.card_fin r), ←Fintype.card_perm]
    conv_rhs => rw [mul_assoc]
                rw [←smul_eq_mul, ←nsmul_eq_smul_cast]
    apply Finset.sum_le_card_nsmul
    intro σ _
    erw [norm_zsmul 𝕜]
    have heq : ‖(Equiv.Perm.sign σ : 𝕜)‖ = 1 := by
      cases Int.units_eq_one_or (Equiv.Perm.sign σ) with
      | inl h => rw [h]; simp only [Units.val_one, Int.cast_one, norm_one]
      | inr h => rw [h]; simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
        norm_neg, norm_one]
    rw [norm_prod, heq, one_mul, ← Equiv.prod_comp σ (fun i => ‖m i‖), ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
      (fun i _ => ContinuousLinearMap.le_op_norm (f i) (m (σ i)))
)

@[simp]
lemma continuousAlternatingFormOfFamily_apply (f : (i : Fin r) → (E →L[𝕜] 𝕜)) :
(continuousAlternatingFormOfFamily f).toAlternatingMap = alternatingFormOfFamily 𝕜 r
(fun i => (f i).toLinearMap) := by
  unfold continuousAlternatingFormOfFamily
  rw [AlternatingMap.coe_mkContinuousAlternating]
