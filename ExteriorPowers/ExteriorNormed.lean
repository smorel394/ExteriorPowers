import Mathlib.Tactic
import ExteriorPowers.ExteriorPower
import ExteriorPowers.SeparatingMaps
import ExteriorPowers.ContinuousAlternatingMap


open Classical

namespace ExteriorPower

variable {𝕜 E F ι: Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
[NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Fintype ι] {r : ℕ}

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

lemma seminormAlternatingForm_zero : seminormAlternatingForm (0 : AlternatingMap 𝕜 E 𝕜 (Fin r)) = 0 := by
  unfold seminormAlternatingForm
  ext x
  simp only [map_zero, Seminorm.comp_zero, Seminorm.zero_apply]

lemma seminormAlternatingFormBoundedAt (x : ExteriorPower 𝕜 E r) : ∃ (M : ℝ),
∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)), ‖f‖ ≤ 1 → (seminormAlternatingForm f.toAlternatingMap x) ≤ M := by
  have hx : x ∈ (⊤ : Submodule 𝕜 (ExteriorPower 𝕜 E r)) := by simp only [Submodule.mem_top]
  rw [←ExteriorPower.ιMulti_span] at hx
  apply Submodule.span_induction hx (p := fun x => ∃ (M : ℝ), ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    ‖f‖ ≤ 1 → (seminormAlternatingForm f.toAlternatingMap x) ≤ M)
  . intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨y, hyx⟩ := hx
    existsi Finset.prod Finset.univ (fun (i : Fin r) => ‖y i‖)
    intro f hf
    rw [←hyx, seminormAlternatingForm_apply_ιMulti]
    refine le_trans (ContinuousMultilinearMap.le_op_norm f.toContinuousMultilinearMap y) ?_
    exact mul_le_of_le_one_left (Finset.prod_nonneg (fun i _ => norm_nonneg (y i))) hf
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

lemma seminormAlternatingFormBounded : BddAbove {p : Seminorm 𝕜 (ExteriorPower 𝕜 E r) |
∃ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)), ‖f‖ ≤ 1 ∧ p = seminormAlternatingForm f.toAlternatingMap} := by
  rw [Seminorm.bddAbove_iff]
  set M : (ExteriorPower 𝕜 E r) → ℝ := fun x => Classical.choose (seminormAlternatingFormBoundedAt x)
  existsi M
  rw [mem_upperBounds]
  intro g hg
  simp only [Set.mem_image, Set.mem_setOf_eq] at hg
  obtain ⟨p, ⟨⟨f, hf, hfp⟩, hp⟩⟩ := hg
  rw [←hp, hfp]
  exact fun x => Classical.choose_spec (seminormAlternatingFormBoundedAt x) f hf

variable (𝕜 E r)

noncomputable def seminormExteriorPower : Seminorm 𝕜 (ExteriorPower 𝕜 E r) :=
  sSup {p : Seminorm 𝕜 (ExteriorPower 𝕜 E r) |
  ∃ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)), ‖f‖ ≤ 1 ∧ p = seminormAlternatingForm f.toAlternatingMap}

noncomputable def opSeminorm (x : ExteriorPower 𝕜 E r) : ℝ :=
sInf {c : ℝ | 0 ≤ c ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
‖liftAlternating r f.toAlternatingMap x‖ ≤ c * ‖f‖}

variable {𝕜 E r}

noncomputable instance hasOpSemnorm : Norm (ExteriorPower 𝕜 E r) :=
  ⟨opSeminorm 𝕜 E r⟩

theorem opSeminorm_def (x : ExteriorPower 𝕜 E r) : ‖x‖ = sInf { c | 0 ≤ c ∧ ∀
(f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)), ‖liftAlternating r f.toAlternatingMap x‖ ≤ c * ‖f‖}
 :=
  rfl

lemma bound (x : ExteriorPower 𝕜 E r) : ∃ (C : ℝ), 0 < C ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
‖liftAlternating r f.toAlternatingMap x‖ ≤ C * ‖f‖ := by
  have hx : x ∈ (⊤ : Submodule 𝕜 (ExteriorPower 𝕜 E r)) := by simp only [Submodule.mem_top]
  rw [←ExteriorPower.ιMulti_span] at hx
  apply Submodule.span_induction hx (p := fun x => ∃ (C : ℝ), 0 < C ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    (liftAlternating f.toAlternatingMap x) ≤ M)


#exit


variable {𝕜 E r}

lemma SeminormExteriorPower_apply_ιMulti_le (m : Fin r → E) :
seminormExteriorPower 𝕜 E r (ExteriorPower.ιMulti 𝕜 r m) ≤ Finset.prod Finset.univ (fun (i : Fin r) => ‖m i‖) := by
  unfold seminormExteriorPower
  rw [Seminorm.sSup_apply seminormAlternatingFormBounded]
  letI : Nonempty {p | ∃ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    ‖f‖ ≤ 1 ∧ p = seminormAlternatingForm f.toAlternatingMap} := by
    existsi (0 : Seminorm 𝕜 (ExteriorPower 𝕜 E r))
    simp only [Set.mem_setOf_eq]
    existsi 0
    simp only [norm_zero, zero_le_one, ContinuousAlternatingMap.toAlternatingMap_zero, true_and]
    rw [seminormAlternatingForm_zero]
  rw [ciSup_le_iff]
  . intro ⟨p, hp⟩
    simp only [Set.mem_setOf_eq] at hp
    obtain ⟨f, hf, hfp⟩ := hp
    change p _ ≤ _
    rw [hfp]
    erw [seminormAlternatingForm_apply_ιMulti]
    change ‖f.toContinuousMultilinearMap _‖ ≤ _
    refine le_trans (ContinuousMultilinearMap.le_op_norm f.toContinuousMultilinearMap m) ?_
    exact mul_le_of_le_one_left (Finset.prod_nonneg (fun i _ => norm_nonneg (m i))) hf
  . obtain ⟨M, hM⟩ := seminormAlternatingFormBoundedAt (ExteriorPower.ιMulti 𝕜 r m)
    existsi M
    rw [mem_upperBounds]
    intro a ha
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop] at ha
    obtain ⟨p, ⟨⟨f, hf, hfp⟩, hpa⟩⟩ := ha
    rw [←hpa, hfp]
    exact hM f hf


noncomputable instance instSeminormedAddCommGroupExteriorPower : SeminormedAddCommGroup (ExteriorPower 𝕜 E r) :=
(seminormExteriorPower 𝕜 E r).toAddGroupSeminorm.toSeminormedAddCommGroup

instance instNormedSpaceExteriorPower : NormedSpace 𝕜 (ExteriorPower 𝕜 E r)
where norm_smul_le a x := by change (seminormExteriorPower 𝕜 E r).toFun (a • x) ≤ _
                             rw [(seminormExteriorPower 𝕜 E r).smul']
                             apply le_refl

def ιMulti_continuous : ContinuousAlternatingMap 𝕜 E (ExteriorPower 𝕜 E r) (Fin r) :=
AlternatingMap.mkContinuousAlternating (𝕜 := 𝕜) (E := E) (F := ExteriorPower 𝕜 E r) (ι := Fin r) (ιMulti 𝕜 r (M := E)) 1
(by intro (m : Fin r → E); rw [one_mul]; exact SeminormExteriorPower_apply_ιMulti_le (𝕜 := 𝕜) m)

lemma liftContinuousAlternating_norm (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) (x : ExteriorPower 𝕜 E r) :
‖ExteriorPower.liftAlternating r f.toAlternatingMap x‖ ≤  ‖f‖ * ‖x‖ := by
  obtain ⟨g, a, hg, ha⟩ := vector_normalize 𝕜 (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) f
  rw [ha]
  simp only [ContinuousAlternatingMap.toAlternatingMap_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, norm_mul]
  rw [norm_smul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg a)
  sorry

lemma liftContinuousAlternating_continuous (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) :
Continuous (ExteriorPower.liftAlternating r f.toAlternatingMap) :=
AddMonoidHomClass.continuous_of_bound (ExteriorPower.liftAlternating r f.toAlternatingMap) ‖f‖
    (fun x => liftContinuousAlternating_norm f x)

section SeparatingDual

variable [SeparatingDual 𝕜 E]




end SeparatingDual
