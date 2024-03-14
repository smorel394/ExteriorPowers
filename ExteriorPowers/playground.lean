import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Algebra.Module.Projective



variable (f : ℕ → ℕ)

open BigOperators in
example : ∑ x in {1,2,3}, f x = 0 := by
  rw [Finset.sum_insert]
  sorry
  simp only [Finset.mem_insert, OfNat.one_ne_ofNat, Finset.mem_singleton, or_self,
    not_false_eq_true]

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable {a : V} {k : ℕ}

open Submodule in
noncomputable def truc : V ≃ₗ[K] (V ⧸ span K {a}) ×  span K {a} :=
  (Classical.choice (quotient_prod_linearEquiv (span K {a}))).symm

open Finset

variable (n : ℕ)

open BigOperators

#eval ∑ i : Fin 5, i
#eval ∑ i : Fin 4, i
#eval ∑ i : Fin 6, i


variable {α V : Type*} [DivisionRing α] [AddCommGroup V] [Module α V]

open Submodule in
noncomputable def construct_map (v p : Fin 2 → V) (hp : LinearIndependent α p)
    (hv : LinearIndependent α v) :
    ∃ l : V ≃ₗ[α] V, ∀ i, l (p i) = v i := by
  set W := span α (Set.range p ∪ Set.range v)
  have p_mem_W : ∀ i, p i ∈ W := fun i ↦ subset_span (by simp only [Set.mem_union,
    Set.mem_range, exists_apply_eq_apply, true_or])
  have v_mem_W : ∀ i, v i ∈ W := fun i ↦ subset_span (by simp only [Set.mem_union,
    Set.mem_range, exists_apply_eq_apply, or_true])
  letI : FiniteDimensional α W := by
    apply FiniteDimensional.span_of_finite
    rw [Set.finite_union]
    constructor
    all_goals (apply Set.finite_range)
  set W' := Classical.choose (Submodule.exists_isCompl W)
  set hW' := Classical.choose_spec (Submodule.exists_isCompl W)
  set eprod := Submodule.prodEquivOfIsCompl W W' hW'
  set pW : Fin 2 → W := fun i ↦ ⟨p i, p_mem_W i⟩
  have hpW := LinearIndependent.of_comp (Submodule.subtype W) (by
        have : p = Submodule.subtype W ∘ pW := by ext _; simp only [coeSubtype,
          Function.comp_apply]
        rw [← this]; exact hp)
  set vW : Fin 2 → W := fun i ↦ ⟨v i, v_mem_W i⟩
  have hvW := LinearIndependent.of_comp (Submodule.subtype W) (by
        have : v = Submodule.subtype W ∘ vW := by ext _; simp only [coeSubtype,
          Function.comp_apply]
        rw [← this]; exact hv)
  set W₁ : Submodule α W := span α (Set.range pW)
  set W₂ : Submodule α W := span α (Set.range vW)
  set b₁ := Basis.span hpW
  set b₂ := Basis.span hvW
  set W'₁ := Classical.choose (Submodule.exists_isCompl W₁)
  set W'₂ := Classical.choose (Submodule.exists_isCompl W₂)
  set hW'₁ := Classical.choose_spec (Submodule.exists_isCompl W₁)
  set hW'₂ := Classical.choose_spec (Submodule.exists_isCompl W₂)
  have r₁ : FiniteDimensional.finrank α W₁ = 2 := finrank_span_eq_card hpW
  have r₂ : FiniteDimensional.finrank α W₂ = 2 := finrank_span_eq_card hvW
  have r' : FiniteDimensional.finrank α W'₁ = FiniteDimensional.finrank α W'₂ := by
    apply add_right_injective 2
    simp only
    conv_lhs => congr
                rw [← r₁]
    conv_rhs => congr
                rw [← r₂]
    rw [finrank_add_eq_of_isCompl hW'₁, finrank_add_eq_of_isCompl hW'₂]
  set eW' := LinearEquiv.ofFinrankEq W'₁ W'₂ r'
  set eW := b₁.repr.trans b₂.repr.symm
  set f := Submodule.prodEquivOfIsCompl W₁ W'₁ hW'₁
  set f2 := Submodule.prodEquivOfIsCompl W₂ W'₂ hW'₂
  set e' := f.symm ≪≫ₗ (LinearEquiv.prod eW eW') ≪≫ₗ f2
  set e := eprod.symm ≪≫ₗ (LinearEquiv.prod e' (LinearEquiv.refl α _)) ≪≫ₗ eprod
  have he : ∀ i, e (p i) = v i := by
    intro i
    have : e (p i) = eprod ((LinearEquiv.prod e' (LinearEquiv.refl α _)) (eprod.symm (p i))) :=
      by simp only [LinearEquiv.trans_apply, LinearEquiv.prod_apply, Basis.repr_symm_apply,
        coe_prodEquivOfIsCompl', LinearEquiv.refl_apply, AddSubmonoid.coe_add, coe_toAddSubmonoid]
    rw [this]
    have : eprod.symm (p i) = ⟨pW i, 0⟩ := by
      apply LinearEquiv.injective eprod
      simp only [LinearEquiv.apply_symm_apply, coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero,
        add_zero]
    rw [this]
    have : e' (pW i) = vW i := by
      have : e' (pW i) = f2 ((LinearEquiv.prod eW eW') (f.symm (pW i))) := by
        simp only [LinearEquiv.trans_apply, LinearEquiv.prod_apply, Basis.repr_symm_apply,
          coe_prodEquivOfIsCompl']
      rw [this]
      have : f.symm (pW i) = ⟨b₁ i, 0⟩ := by
        apply LinearEquiv.injective f
        simp only [LinearEquiv.apply_symm_apply, coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero,
          add_zero, Basis.span_apply]
      rw [this]
      apply LinearEquiv.injective f2.symm
      have : f2.symm (vW i) = ⟨b₂ i, 0⟩ := by
        apply LinearEquiv.injective f2
        simp only [LinearEquiv.apply_symm_apply, coe_prodEquivOfIsCompl', Basis.span_apply,
          ZeroMemClass.coe_zero, add_zero]
      rw [this]
      simp only [LinearEquiv.prod_apply, LinearEquiv.trans_apply, Basis.repr_self,
        Basis.repr_symm_apply, Finsupp.total_single, one_smul, _root_.map_zero,
        coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero,
        prodEquivOfIsCompl_symm_apply_left]
    rw [LinearEquiv.prod_apply, this]
    simp only [_root_.map_zero, coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
  exact ⟨e, he⟩

example (a b : V) : Fin 2 → V := fun i ↦ if i = 0 then a else b

  #exit

  set f : W₁ →ₗ[α] W := Basis.constr b₁ ℕ (fun i ↦ vW i)


open scoped LinearAlgebra.Projectivization

def is_even_b : ℕ → Bool
  | 0 => true
  | 1 => false
  | n + 2  => is_even_b n

inductive is_even : ℕ → Prop where
  | is_even_zero : is_even 0
  | is_even_succsucc : ∀ n, is_even n → is_even n.succ.succ

lemma is_even_b_correct : ∀ n, is_even_b n = true ↔ is_even n := by
  simp_rw [iff_def]; rw [forall_and]
  constructor
  all_goals (apply Nat.twoStepInduction)
  · exact fun _ ↦ is_even.is_even_zero
  · exact fun h ↦ by exfalso; simp only [is_even_b] at h
  · exact fun _ hn _ h ↦ by rw [is_even_b] at h; apply is_even.is_even_succsucc; exact hn h
  · exact fun _ ↦ by rw [is_even_b]
  · exact fun h ↦ by cases h
  · exact fun _ hn _ h ↦ by rw [is_even_b]; apply hn; cases h; assumption


#check (2 : ℝ)

#check Real.pi

#check (fun x  ↦ x + 2 : ℝ → ℝ)

#check sq_pos_iff

example :  ∀ (x : ℝ), x ≠ 0 → x^2 > 0 :=
  fun x hx ↦ (sq_pos_iff x).mpr hx

#check ∀ (n : ℕ), ∃ (x : ℚ), x≥ 0 ∧
  x^2 = n → ∃ (y : ℕ), y^2 =n ∧ (y : ℚ) = x

variable (K V : Type*) [Field K]
  [AddCommGroup V] [Module K V] (r : ℕ)

def Grassmannienne :=
  {W : Submodule K V |
  FiniteDimensional.finrank K W = r ∧
  FiniteDimensional K W}

#check Grassmannienne




































#check 2
#check -1
#check Real.pi

#check fun x : ℤ ↦ x + 2

#check ∀ (x : ℝ), x ≠ 0 → x^2 > 0

lemma carre_pos : ∀ (x : ℝ), x ≠ 0 → x^2 > 0 := by
  sorry

example : ∀ (n : ℕ), ∃ (y : ℚ), 0 ≤ y ∧ y^2 = x → Rat.isInt y := sorry

variable (K E : Type*) [Field K] [AddCommGroup E] [Module K E] (r : ℕ)

def Grassmannian := {W : Submodule K E | FiniteDimensional K W ∧ FiniteDimensional.finrank K W = r}

#check Grassmannian K E r

#print projectivizationSetoid

#print Projectivization

#print Projectivization.mk

#print Projectivization.rep

#print Projectivization.mk_rep

#print Projectivization.mk_eq_mk_iff


#exit

def f : ℕ → ℕ := by
  intro n
  by_cases h : n = 0
  · exact 0
  · exact n + 1

#exit

example : ∀ (x : ℝ), x^2 ≥ 0 := by
  intro x
  by_cases h : x = 0
  · rw [h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow', ge_iff_le,
    le_refl]
  · exact le_of_lt (carre_pos x h)

#exit

def f : K → K := by
  intro x
  by_cases h : x = 0
  · exact 0
  · exact x⁻¹
