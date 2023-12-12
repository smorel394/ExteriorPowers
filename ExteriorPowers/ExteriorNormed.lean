import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Dual
import ExteriorPowers.ExteriorPower
import ExteriorPowers.ContinuousAlternatingMap


open Classical

namespace ExteriorPower

variable {𝕜 E F ι: Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
[NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Fintype ι] {r : ℕ}


def toDualContinuousAlternatingMap (x : ExteriorPower 𝕜 E r) : ContinuousAlternatingMap 𝕜 E F (Fin r) →ₗ[𝕜] F :=
{
 toFun := fun f => liftAlternating r f.toAlternatingMap x
 map_add' := fun f g => by simp only [ContinuousAlternatingMap.toAlternatingMap_add, map_add,
   LinearMap.add_apply]
 map_smul' := fun a f => by simp only [ContinuousAlternatingMap.toAlternatingMap_smul, map_smul,
   LinearMap.smul_apply, RingHom.id_apply]
 }

@[simp]
lemma toDualContinuousAlternatingMap_apply (x : ExteriorPower 𝕜 E r) (f : ContinuousAlternatingMap 𝕜 E F (Fin r)):
toDualContinuousAlternatingMap x f = liftAlternating r f.toAlternatingMap x := rfl


@[simp]
lemma toDualContinuousAlternatingMap_zero : toDualContinuousAlternatingMap (F := F) (0 : ExteriorPower 𝕜 E r) = 0 := by
  ext f
  unfold toDualContinuousAlternatingMap
  simp only [map_zero, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]

@[simp]
lemma toDualContinuousAlternatingMap_add (x y : ExteriorPower 𝕜 E r) :
toDualContinuousAlternatingMap (F := F) (x + y) = toDualContinuousAlternatingMap x + toDualContinuousAlternatingMap y := by
  ext f
  unfold toDualContinuousAlternatingMap
  simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]

@[simp]
lemma toDualContinuousAlternatingMap_smul (a : 𝕜) (x : ExteriorPower 𝕜 E r) :
toDualContinuousAlternatingMap (F := F) (a • x) = a • toDualContinuousAlternatingMap x := by
  ext f
  unfold toDualContinuousAlternatingMap
  simp only [map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]

@[simp]
lemma toDualContinuousAlternatingMap_apply_ιMulti (m : Fin r → E) (f : ContinuousAlternatingMap 𝕜 E F (Fin r)) :
toDualContinuousAlternatingMap (ιMulti 𝕜 r m) f = f m := by
  unfold toDualContinuousAlternatingMap
  simp only [liftAlternating_apply_ιMulti, ContinuousAlternatingMap.coe_coe, LinearMap.coe_mk,
    AddHom.coe_mk]

lemma toDualContinuousAlternatingMap_bound (x : ExteriorPower 𝕜 E r) :
∃ (C : ℝ), 0 ≤ C ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E F (Fin r)), ‖toDualContinuousAlternatingMap x f‖ ≤ C * ‖f‖ := by
  have hx : x ∈ (⊤ : Submodule 𝕜 (ExteriorPower 𝕜 E r)) := by simp only [Submodule.mem_top]
  rw [←ExteriorPower.ιMulti_span] at hx
  apply Submodule.span_induction hx (p := fun x => ∃ (C : ℝ), 0 ≤ C ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E F (Fin r)),
    ‖toDualContinuousAlternatingMap x f‖ ≤ C * ‖f‖)
  . intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨m, hmx⟩ := hx
    existsi Finset.prod Finset.univ (fun (i : Fin r) => ‖m i‖)
    rw [and_iff_right (Finset.prod_nonneg (fun i _ => norm_nonneg _))]
    intro f
    rw [←hmx, toDualContinuousAlternatingMap_apply_ιMulti, mul_comm]
    exact ContinuousMultilinearMap.le_op_norm f.toContinuousMultilinearMap m
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
ExteriorPower 𝕜 E r →ₗ[𝕜] NormedSpace.Dual 𝕜 (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) :=
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
lemma toDualContinuousAlternatingMapLinear_apply (x : ExteriorPower 𝕜 E r) (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)):
toDualContinuousAlternatingMapLinear 𝕜 E r x f = liftAlternating r f.toAlternatingMap x := by
  unfold toDualContinuousAlternatingMapLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mkContinuousOfExistsBound_apply,
    toDualContinuousAlternatingMap_apply]

@[simp]
lemma toDualContinuousAlternatingMapLinear_apply_ιMulti (m : Fin r → E) (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) :
toDualContinuousAlternatingMapLinear 𝕜 E r (ιMulti 𝕜 r m) f = f m := by
  unfold toDualContinuousAlternatingMapLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mkContinuousOfExistsBound_apply,
    toDualContinuousAlternatingMap_apply_ιMulti]


noncomputable instance instSeminormedAddCommGroupExteriorPower : SeminormedAddCommGroup (ExteriorPower 𝕜 E r) :=
SeminormedAddCommGroup.induced (ExteriorPower 𝕜 E r) (NormedSpace.Dual 𝕜 (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)))
(toDualContinuousAlternatingMapLinear 𝕜 E r)

noncomputable instance instNormedSpaceExteriorPower : NormedSpace 𝕜 (ExteriorPower 𝕜 E r) :=
NormedSpace.induced 𝕜 (ExteriorPower 𝕜 E r) (NormedSpace.Dual 𝕜 (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)))
(toDualContinuousAlternatingMapLinear 𝕜 E r)


lemma SeminormExteriorPower_apply_ιMulti_le (m : Fin r → E) :
‖ιMulti 𝕜 r m‖ ≤ Finset.prod Finset.univ (fun (i : Fin r) => ‖m i‖) := by
  change ‖toDualContinuousAlternatingMapLinear 𝕜 E r (ιMulti 𝕜 r m)‖ ≤ _
  apply ContinuousLinearMap.op_norm_le_bound _ (Finset.prod_nonneg (fun i _ => norm_nonneg _))
  intro f
  rw [toDualContinuousAlternatingMapLinear_apply_ιMulti, mul_comm]
  exact ContinuousMultilinearMap.le_op_norm f.toContinuousMultilinearMap m

def ιMulti_continuous : ContinuousAlternatingMap 𝕜 E (ExteriorPower 𝕜 E r) (Fin r) :=
AlternatingMap.mkContinuousAlternating (𝕜 := 𝕜) (E := E) (F := ExteriorPower 𝕜 E r) (ι := Fin r) (ιMulti 𝕜 r (M := E)) 1
(by intro (m : Fin r → E); rw [one_mul]; exact SeminormExteriorPower_apply_ιMulti_le (𝕜 := 𝕜) m)

@[simp]
lemma ιMulti_continuous_apply (v : Fin r → E) :
ιMulti_continuous v = ιMulti 𝕜 r v := by
  unfold ιMulti_continuous
  rw [AlternatingMap.mkContinuousAlternating_apply]

/- This is trivial from what we already did, but I can't state it yet because ContinuousAlternatingMap doesn't
have a morm unless the origin space is normed and not just semi-normed. So we put this lemma and
the following in ExteriorNormedSeparatingDual.lean for now.-/
--lemma ιMulti_continuous_norm : ‖ιMulti_continuous (𝕜 := 𝕜) (E := E) (r := r)‖ ≤ 1 := sorry

lemma liftContinuousAlternating_normAt (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) (x : ExteriorPower 𝕜 E r) :
‖ExteriorPower.liftAlternating r f.toAlternatingMap x‖ ≤  ‖f‖ * ‖x‖ := by
  rw [←toDualContinuousAlternatingMapLinear_apply, mul_comm]
  exact ContinuousLinearMap.le_op_norm _ f

variable (r 𝕜 E)

def liftContinuousAlternating : (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) →ₗ[𝕜]
(ExteriorPower 𝕜 E r →L[𝕜] 𝕜) :=
{toFun := fun f =>
⟨liftAlternating r f.toAlternatingMap,
AddMonoidHomClass.continuous_of_bound (ExteriorPower.liftAlternating r f.toAlternatingMap) ‖f‖
    (fun x => liftContinuousAlternating_normAt f x)⟩
 map_add' := by intro f g; ext _; simp only [ContinuousAlternatingMap.toAlternatingMap_add, map_add,
   ContinuousLinearMap.coe_mk', LinearMap.add_apply, ContinuousLinearMap.add_apply]
 map_smul' := by intro a d; ext _; simp only [ContinuousAlternatingMap.toAlternatingMap_smul,
   map_smul, ContinuousLinearMap.coe_mk', LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
   ContinuousLinearMap.coe_smul', Pi.smul_apply]
}

variable {r 𝕜 E}

lemma liftContinuousAlternating_norm_le (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) :
‖liftContinuousAlternating 𝕜 E r f‖ ≤  ‖f‖ := by
  apply ContinuousLinearMap.op_norm_le_bound
  . exact norm_nonneg f
  . exact fun x => liftContinuousAlternating_normAt f x

lemma liftCOntinuousAlternating_continuous : Continuous (liftContinuousAlternating 𝕜 E r) :=
AddMonoidHomClass.continuous_of_bound
(liftContinuousAlternating 𝕜 E r) 1 (fun f => by rw [one_mul]; exact liftContinuousAlternating_norm_le f)

variable (r 𝕜 E)


def liftContinuousAlternating_invFun : (ExteriorPower 𝕜 E r →L[𝕜] 𝕜) →ₗ[𝕜]
(ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)) :=
{toFun := fun L => L.compContinuousAlternatingMap ιMulti_continuous
 map_add' := fun f g => by ext _; simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe,
   Function.comp_apply, ContinuousLinearMap.add_apply, ContinuousAlternatingMap.add_apply]
 map_smul' := fun a f => by ext _; simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe,
   ContinuousLinearMap.coe_smul', Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
   ContinuousAlternatingMap.smul_apply]
}


variable {r 𝕜 E}


-- TODO : the continuous linear equivalence between ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r) and the
-- continuous dual of ExteriorPower 𝕜 E r. See ExteriorNormedSeparatingDual.lean for now.


noncomputable def continuousAlternatingFormOfFamily (f : (i : Fin r) → (E →L[𝕜] 𝕜)) :
ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r) :=
AlternatingMap.mkContinuousAlternating (alternatingFormOfFamily 𝕜 r (fun i => (f i).toLinearMap))
((Nat.factorial r) * (Finset.prod Finset.univ (fun (i : Fin r) => ‖f i‖)))
(by intro m
    simp only [alternatingFormOfFamily_apply, linearFormOfFamily_apply, toTensorPower_apply_ιMulti,
      map_sum, LinearMap.map_smul_of_tower, TensorPower_linearFormOfFamily_apply_tprod,
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
    rw [norm_prod, heq, one_mul, Finset.Equiv.prod_comp_finset σ (fun i => ‖m i‖)
      (Eq.symm (Finset.image_univ_equiv σ.symm)), ←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
      (fun i _ => ContinuousLinearMap.le_op_norm (f i) (m (σ i)))
)

@[simp]
lemma continuousAlternatingFormOfFamily_apply (f : (i : Fin r) → (E →L[𝕜] 𝕜)) :
(continuousAlternatingFormOfFamily f).toAlternatingMap = alternatingFormOfFamily 𝕜 r
(fun i => (f i).toLinearMap) := by
  unfold continuousAlternatingFormOfFamily
  rw [AlternatingMap.coe_mkContinuousAlternating]





/-
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
-/

/-variable (𝕜 E r)-/

/-
noncomputable def seminormExteriorPower : Seminorm 𝕜 (ExteriorPower 𝕜 E r) :=
  sSup {p : Seminorm 𝕜 (ExteriorPower 𝕜 E r) |
  ∃ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)), ‖f‖ ≤ 1 ∧ p = seminormAlternatingForm f.toAlternatingMap}
-/

/-
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

/-- If `‖f‖ = 0` and `x` is in `ExteriorPower 𝕜 E r` then `‖f x‖ = 0`. -/
theorem norm_image_of_norm_zero (x : ExteriorPower 𝕜 E r) {f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)}
    (hf : ‖f‖ = 0) : ‖liftAlternating r f.toAlternatingMap x‖ = 0 := by
  rw [norm_eq_zero] at hf
  rw [hf]
  simp only [ContinuousAlternatingMap.toAlternatingMap_zero, map_zero, LinearMap.zero_apply,
    norm_zero]

lemma bound (x : ExteriorPower 𝕜 E r) : ∃ (C : ℝ), 0 < C ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
‖liftAlternating r f.toAlternatingMap x‖ ≤ C * ‖f‖ := by
  have hx : x ∈ (⊤ : Submodule 𝕜 (ExteriorPower 𝕜 E r)) := by simp only [Submodule.mem_top]
  rw [←ExteriorPower.ιMulti_span] at hx
  apply Submodule.span_induction hx (p := fun x => ∃ (C : ℝ), 0 < C ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    ‖(liftAlternating r f.toAlternatingMap x)‖ ≤ C * ‖f‖)
  . intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨m, hm⟩ := hx
    existsi Finset.prod Finset.univ (fun (i : Fin r) => ‖m i‖) + 1
    constructor
    . exact add_pos_of_nonneg_of_pos (Finset.prod_nonneg (fun i _ => norm_nonneg _)) zero_lt_one
    . intro f
      rw [add_mul, ←hm, liftAlternating_apply_ιMulti, mul_comm]
      refine le_trans ?_ (le_add_of_nonneg_right (mul_nonneg (le_of_lt zero_lt_one) (norm_nonneg _)))
      exact ContinuousMultilinearMap.le_op_norm f.toContinuousMultilinearMap m
  . existsi 1
    rw [and_iff_right (zero_lt_one)]
    intro f
    simp only [map_zero, norm_zero, one_mul, norm_nonneg]
  . intro x y ⟨Cx, hx⟩ ⟨Cy, hy⟩
    existsi Cx + Cy
    rw [and_iff_right (add_pos hx.1 hy.1)]
    intro f
    rw [map_add, add_mul]
    exact le_trans (norm_add_le _ _) (add_le_add (hx.2 f) (hy.2 f))
  . intro a x ⟨C, h⟩
    existsi ‖a‖ * C + 1
    constructor
    . exact add_pos_of_nonneg_of_pos (mul_nonneg (norm_nonneg a) (le_of_lt h.1)) zero_lt_one
    . intro f
      rw [map_smul, add_mul, norm_smul, mul_assoc]
      refine le_trans ?_ (le_add_of_nonneg_right (mul_nonneg (le_of_lt zero_lt_one) (norm_nonneg _)))
      exact mul_le_mul_of_nonneg_left (h.2 f) (norm_nonneg a)

theorem bounds_nonempty {x : ExteriorPower 𝕜 E r} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    ‖liftAlternating r f.toAlternatingMap x‖ ≤ c * ‖f‖} :=
  let ⟨M, hMp, hMb⟩ := ExteriorPower.bound x
  ⟨M, le_of_lt hMp, hMb⟩

theorem bounds_bddBelow {x : ExteriorPower 𝕜 E r} : BddBelow { c | 0 ≤ c ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    ‖liftAlternating r f.toAlternatingMap x‖ ≤ c * ‖f‖} :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

theorem isLeast_opSeminorm (x : ExteriorPower 𝕜 E r) :
    IsLeast { c | 0 ≤ c ∧ ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    ‖liftAlternating r f.toAlternatingMap x‖ ≤ c * ‖f‖} ‖x‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [Set.setOf_and, Set.setOf_forall]
  refine isClosed_Ici.inter <| isClosed_iInter fun _ ↦ isClosed_le ?_ ?_ <;> continuity

/-- If one controls the norm of every `f x`, then one controls the norm of `x`. -/
theorem opSeminorm_le_bound (x : ExteriorPower 𝕜 E r) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
‖liftAlternating r f.toAlternatingMap x‖ ≤ M * ‖f‖) :
    ‖x‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩

/-- If one controls the norm of every `f x`, `‖f‖ ≠ 0`, then one controls the norm of `x`. -/
theorem op_norm_le_bound' (x : ExteriorPower 𝕜 E r) {M : ℝ} (hMp : 0 ≤ M)
(hM : ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)), ‖f‖ ≠ 0 →
‖liftAlternating r f.toAlternatingMap x‖ ≤ M * ‖f‖) : ‖x‖ ≤ M :=
  opSeminorm_le_bound x hMp fun f =>
    (ne_or_eq ‖f‖ 0).elim (hM f) fun h => by
      simp only [h, mul_zero, norm_image_of_norm_zero x h, le_refl]

theorem opSeminorm_eq_of_bounds {x : ExteriorPower 𝕜 E r} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)), ‖liftAlternating r f.toAlternatingMap x‖ ≤ M * ‖f‖)
    (h_below : ∀ N ≥ 0, (∀ (f : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin r)),
    ‖liftAlternating r f.toAlternatingMap x‖ ≤ N * ‖f‖) → M ≤ N) :
    ‖x‖ = M :=
  le_antisymm (ExteriorPower.opSeminorm_le_bound x M_nonneg h_above)
    ((le_csInf_iff ExteriorPower.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

theorem opSeminorm_neg (x : ExteriorPower 𝕜 E r) : ‖-x‖ = ‖x‖ := by simp only [opSeminorm_def, neg_apply, norm_neg]

theorem opSeminorm_nonneg (x : ExteriorPower 𝕜 E r) : 0 ≤ ‖x‖ :=
  Real.sInf_nonneg _ fun _ ↦ And.left

/-- The norm of the `0` vector is `0`. -/
theorem opSeminorm_zero : ‖(0 : ExteriorPower 𝕜 E r)‖ = 0 :=
  le_antisymm (opSeminorm_le_bound _ le_rfl fun _ ↦ by simp) (opSeminorm_nonneg _)-/


--variable {𝕜 E r}

/-lemma SeminormExteriorPower_apply_ιMulti_le (m : Fin r → E) :
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
                             apply le_refl-/

/-def ιMulti_continuous : ContinuousAlternatingMap 𝕜 E (ExteriorPower 𝕜 E r) (Fin r) :=
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




end SeparatingDual-/
