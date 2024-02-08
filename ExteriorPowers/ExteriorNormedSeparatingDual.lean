import Mathlib.Tactic
import ExteriorPowers.SeparatingMaps
import ExteriorPowers.ExteriorNormed

set_option maxHeartbeats 1000000

open Classical

namespace ExteriorPower

variable {𝕜 E F ι: Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
[NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Fintype ι] {r : ℕ}

section SeparatingDual

variable [SeparatingDual 𝕜 E] [CompleteSpace 𝕜]

lemma toDualContinuousAlternatingMapLinear_injective : Function.Injective
(toDualContinuousAlternatingMapLinear 𝕜 E r) := by
  rw [←LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨W, hW, hWx⟩ := mem_exteriorPower_is_mem_finite r x
  rw [LinearMap.mem_range] at hWx
  obtain ⟨y, hyx⟩ := hWx
  have hW1 : FiniteDimensional 𝕜 W := by
    rw [←Submodule.fg_top, ←Module.finite_def] at hW
    exact hW
  letI := hW1
  set n := FiniteDimensional.finrank 𝕜 W
  have hW2 : FiniteDimensional.finrank 𝕜 W = n := rfl
  set hsep := SeparatingMaps.ofSeparatingDual inferInstance n ⟨W, hW1, hW2⟩
  rw [SeparatingMaps_iff_projection] at hsep
  obtain ⟨p, hp⟩ := hsep
  have hxy : y = ExteriorPower.map r p.toLinearMap x := by
    rw [←hyx, ←(LinearMap.comp_apply (ExteriorPower.map r p.toLinearMap)
      (ExteriorPower.map r (Submodule.subtype W)) y), ExteriorPower.map_comp_map]
    suffices h : LinearMap.comp p.toLinearMap (Submodule.subtype W) = LinearMap.id by
      rw [h]; simp only [ExteriorPower.map_id, LinearMap.id_coe, id_eq]
    ext z
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype,
      Function.comp_apply, hp z, LinearMap.id_coe, id_eq]
  set b := FiniteDimensional.finBasisOfFinrankEq 𝕜 W hW2
  set B := BasisOfBasis 𝕜 r b
  suffices h : y = 0 by rw [←hyx, h, map_zero]
  rw [←(Basis.forall_coord_eq_zero_iff B)]
  intro ⟨s, hs⟩
  set F : Fin r → (E →L[𝕜] 𝕜) := fun i =>
    ContinuousLinearMap.comp (LinearMap.toContinuousLinearMap (b.coord (Finset.orderIsoOfFin s hs i))) p
  have heq1 : toDualContinuousAlternatingMapLinear 𝕜 E r x (continuousAlternatingFormOfFamily F) =
    linearFormOfBasis 𝕜 r b hs y := by
    rw [hxy]
    unfold linearFormOfBasis toDualContinuousAlternatingMapLinear continuousAlternatingFormOfFamily
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.coe_orderIsoOfFin_apply,
      ContinuousLinearMap.coe_comp, LinearMap.coe_toContinuousLinearMap,
      LinearMap.mkContinuousOfExistsBound_apply, toDualContinuousAlternatingMap_apply,
      AlternatingMap.coe_mkContinuousAlternating]
    unfold alternatingFormOfFamily
    simp only [liftAlternating_comp, liftAlternating_ιMulti, LinearMap.comp_id]
    rw [linearFormOfFamily_comp_map_apply]
  have heq2 : toDualContinuousAlternatingMapLinear 𝕜 E r x (continuousAlternatingFormOfFamily F) =
    Basis.coord B ⟨s, hs⟩ y := by
    rw [heq1, BasisOfBasis_coord]
  rw [LinearMap.mem_ker] at hx
  rw [←heq2, hx, ContinuousLinearMap.zero_apply]

lemma opSeminorm_is_norm {x : ExteriorPower 𝕜 E r} (hx : ‖x‖ = 0) : x = 0 := by
  change ‖toDualContinuousAlternatingMapLinear 𝕜 E r x‖ = 0 at hx
  rw [norm_eq_zero] at hx
  change x ∈ LinearMap.ker _ at hx
  rw [LinearMap.ker_eq_bot.mpr toDualContinuousAlternatingMapLinear_injective, Submodule.mem_bot] at hx
  exact hx

noncomputable instance instNormedAddCommGroupExteriorPower : NormedAddCommGroup (ExteriorPower 𝕜 E r) :=
NormedAddCommGroup.ofSeparation (fun _ hx => opSeminorm_is_norm hx)

lemma ιMulti_continuous_norm : ‖ιMulti_continuous (𝕜 := 𝕜) (E := E) (r := r)‖ ≤ 1 := by
  apply ContinuousMultilinearMap.op_norm_le_bound
  . simp only [zero_le_one]
  . intro m
    rw [one_mul]
    exact SeminormExteriorPower_apply_ιMulti_le m

lemma liftContinuousAlternating_invFun_norm_le (L : ExteriorPower 𝕜 E r →L[𝕜] 𝕜) :
‖liftContinuousAlternating_invFun 𝕜 E r L‖ ≤ ‖L‖ := by
  apply ContinuousMultilinearMap.op_norm_le_bound
  . exact norm_nonneg _
  . intro m
    unfold liftContinuousAlternating_invFun
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    refine le_trans (ContinuousLinearMap.le_op_norm _ _) ( mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    change ‖ιMulti_continuous m‖ ≤ _
    refine le_trans (ContinuousMultilinearMap.le_op_norm (ιMulti_continuous (𝕜 := 𝕜)
      (E := E) (r :=r)).toContinuousMultilinearMap m) ?_
    exact mul_le_of_le_one_left (Finset.prod_nonneg (fun i _ => norm_nonneg _)) ιMulti_continuous_norm

lemma liftContinuousAlternating_invFun_continuous : Continuous (liftContinuousAlternating_invFun 𝕜 E r) :=
AddMonoidHomClass.continuous_of_bound
(liftContinuousAlternating_invFun 𝕜 E r) 1 (fun L => by rw [one_mul]; exact liftContinuousAlternating_invFun_norm_le L)

variable (𝕜 E r)


noncomputable def liftContinuousAlternating_equiv : (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) ≃ₗ[𝕜]
(ExteriorPower 𝕜 E r →L[𝕜] 𝕜) := LinearEquiv.ofLinear
(liftContinuousAlternating 𝕜 E r) (liftContinuousAlternating_invFun 𝕜 E r)
(by ext L x
    unfold liftContinuousAlternating liftContinuousAlternating_invFun ιMulti_continuous
      AlternatingMap.mkContinuousAlternating ContinuousLinearMap.compContinuousAlternatingMap
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      ContinuousLinearMap.coe_mk', LinearMap.id_coe, id_eq]
    change liftAlternating r (LinearMap.compAlternatingMap _ (ιMulti 𝕜 r)) x = _
    rw [liftAlternating_comp]
    simp only [liftAlternating_ιMulti, LinearMap.comp_id, ContinuousLinearMap.coe_coe]
)
(by ext f x
    unfold liftContinuousAlternating liftContinuousAlternating_invFun ιMulti_continuous
      AlternatingMap.mkContinuousAlternating
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      ContinuousLinearMap.compContinuousAlternatingMap_coe, ContinuousLinearMap.coe_mk',
      ContinuousAlternatingMap.coe_mk, LinearMap.id_coe, id_eq]
    sorry
)

noncomputable def liftContinuousAlternating_linearIsometry :
(ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) ≃ₛₗᵢ[RingHom.id 𝕜]
(ExteriorPower 𝕜 E r →L[𝕜] 𝕜) := LinearIsometryEquiv.ofBounds (liftContinuousAlternating_equiv 𝕜 E r)
(by intro f; unfold liftContinuousAlternating_equiv; simp only [LinearEquiv.ofLinear_apply]
    exact liftContinuousAlternating_norm_le f
)
(by intro L; unfold liftContinuousAlternating_equiv; simp only [LinearEquiv.ofLinear_symm_apply]
    exact liftContinuousAlternating_invFun_norm_le L
)

end SeparatingDual

end ExteriorPower
