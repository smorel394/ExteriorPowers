import Mathlib.Tactic
import ExteriorPowers.ExteriorPower
--import Grassmannian.SeparatingMaps
import ExteriorPowers.ContinuousAlternatingMap


open Classical

namespace ExteriorPower

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℕ}

def seminormAlternatingForm (f : AlternatingMap 𝕜 E 𝕜 (Fin r)) : Seminorm 𝕜 (ExteriorPower 𝕜 E r).carrier := by
  set p : Seminorm 𝕜 𝕜 :=
    {toFun := fun x => ‖x‖
     map_zero' := norm_zero
     add_le' := fun _ _ => norm_add_le _ _
     neg' := fun _ => norm_neg _
     smul' := fun _ _ => norm_smul _ _}
  exact Seminorm.comp p (liftAlternating r f) (𝕜 := 𝕜) (𝕜₂ := 𝕜) (σ₁₂ := RingHom.id 𝕜) (E₂ := 𝕜) (E := (ExteriorPower 𝕜 E r).carrier)

lemma seminormAlternatingForm_apply_ιMulti (f : AlternatingMap 𝕜 E 𝕜 (Fin r)) (y : Fin r → E) :
seminormAlternatingForm f (ExteriorPower.ιMulti 𝕜 r y) = ‖f y‖ := by
  unfold seminormAlternatingForm
  simp only [Seminorm.comp_apply]
  erw [liftAlternating_apply_ιMulti]
  rfl

lemma seminormAlternatingFormBounded (x : ExteriorPower 𝕜 E r) : ∃ (M : ℝ),
∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)), ‖f‖ = 1 → (seminormAlternatingForm f.toAlternatingMap x) ≤ M := by
  have hx : x ∈ (⊤ : Submodule 𝕜 (ExteriorPower 𝕜 E r)) := by simp only [Submodule.mem_top]
  rw [←ExteriorPower.ιMulti_span] at hx
  apply Submodule.span_induction hx (p := fun x => ∃ (M : ℝ), ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    ‖f‖ = 1 → (seminormAlternatingForm f.toAlternatingMap x) ≤ M)
  . intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨y, hyx⟩ := hx
    existsi Finset.prod Finset.univ (fun (i : Fin r) => ‖y i‖)
    intro f hf
    rw [←hyx, seminormAlternatingForm_apply_ιMulti]
    refine le_trans (ContinuousMultilinearMap.le_op_norm f.toContinuousMultilinearMap y) ?_
    change ‖f‖ * _ ≤ _
    rw [hf, one_mul]
  . existsi 0
    intro f _
    simp only [map_zero, le_refl]
  . intro x y hx hy
    obtain ⟨Mx, hx⟩ := hx
    obtain ⟨My, hy⟩ := hy
    existsi Mx + My
    intro f hf
    exact le_trans ((seminormAlternatingForm f.toAlternatingMap).add_le' x y) (add_le_add (hx f hf) (hy f hf))
  . intro a x hx
    obtain ⟨M, hx⟩ := hx
    existsi ‖a‖ * |M|
    intro f hf
    change AddGroupSeminorm.toFun (seminormAlternatingForm f.toAlternatingMap).toAddGroupSeminorm (a • x) ≤ _
    rw [Seminorm.smul']
    refine mul_le_mul (le_refl _) (le_trans (hx f hf) (le_abs_self M)) ?_ (norm_nonneg _)
    simp only [AddGroupSeminorm.toFun_eq_coe, map_nonneg]
