import Mathlib.Data.Set.Finite
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic

open scoped LinearAlgebra.Projectivization


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
