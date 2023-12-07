import Mathlib.Tactic
import ExteriorPowers.SmoothMaps
import ExteriorPowers.ExteriorNormedSeparatingDual
import ExteriorPowers.ContinuousMultilinearMapContDiff

open Classical

namespace Grassmannian

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (r n : ℕ)

def PluckerMap (x : Grassmannian K V r) : Grassmannian K (ExteriorPower K V n) (Nat.choose r n) := by
  refine ⟨LinearMap.range (ExteriorPower.map n (Submodule.subtype x.1)), ?_⟩
  letI := x.2.1
  letI := ExteriorPower.Finite K x.1 n
  constructor
  . apply Module.Finite.range
  . rw [LinearMap.finrank_range_of_inj]
    . rw [ExteriorPower.FinrankOfFiniteFree]
      . rw [x.2.2]
      . apply Module.Free.of_divisionRing
    . apply ExteriorPower.map_injective_field
      apply Submodule.ker_subtype


noncomputable abbrev PluckerMapLift_extended := ExteriorPower.ιMulti_family

noncomputable def PluckerMapLift : {v : Fin r → V // LinearIndependent K v} →
{v : {s : Finset (Fin r) // Finset.card s = n} → ExteriorPower K V n // LinearIndependent K v} := by
  intro ⟨v, hv⟩
  refine ⟨PluckerMapLift_extended K n v, ?_⟩
  apply ExteriorPower.ιMulti_family_linearIndependent_field n hv

lemma PluckerMapLift_isLift :
(PluckerMap K V r n) ∘ (Grassmannian.mk' K) = (Grassmannian.mkI' K
(I := {s : Finset (Fin r) // Finset.card s = n})
(by rw [Fintype.card_finset_len, Fintype.card_fin])) ∘
(PluckerMapLift K V r n) := by
  apply funext
  intro ⟨v, hv⟩
  unfold PluckerMap PluckerMapLift
  simp only [Function.comp_apply, mkI'_eq_mkI]
  rw [←SetCoe.ext_iff]; simp only
  conv_rhs => rw [Grassmannian.mkI_apply]
  have heq : Submodule.subtype (Grassmannian.mk K v hv).1 = Submodule.subtype (Submodule.span K (Set.range v)) := by
    congr
  rw [heq, ←ExteriorPower.span_of_span]

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] [SeparatingDual 𝕜 E]
[Nonempty (Grassmannian 𝕜 E r)]

variable (𝕜 E)

variable [Nonempty {v : {s : Finset (Fin r) // Finset.card s = n} → ExteriorPower 𝕜 E n // LinearIndependent 𝕜 v}]
variable [SeparatingDual 𝕜 (ExteriorPower 𝕜 E n)]

local instance instNonEmptyGrass2 : Nonempty (Grassmannian 𝕜 (ExteriorPower 𝕜 E n) (Nat.choose r n)) :=
(NonemptyGrassmannian_iff 𝕜 (ExteriorPower 𝕜 E n) (I := {s : Finset (Fin r) // Finset.card s = n})
  (r := Nat.choose r n) (by rw [Fintype.card_finset_len, Fintype.card_fin])).mp inferInstance

lemma Smooth.pluckerMapLift : ContMDiff (modelWithCornersSelf 𝕜 (Fin r → E))
(modelWithCornersSelf 𝕜 ({s : Finset (Fin r) // Finset.card s = n} → (ExteriorPower 𝕜 E n)))
⊤ (PluckerMapLift 𝕜 E r n) := sorry

lemma Smooth.pluckerMap : ContMDiff (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r)
(ModelGrassmannian 𝕜 (ModelSpace 𝕜 (ExteriorPower 𝕜 E n) (Nat.choose r n)) (Nat.choose r n)) ⊤
(PluckerMap 𝕜 E r n) := by
  apply Smooth.mapFromGrassmannian
  rw [PluckerMapLift_isLift]
  apply ContMDiff.comp (E' := {s : Finset (Fin r) // Finset.card s = n} → (ExteriorPower 𝕜 E n))
    (I' := modelWithCornersSelf 𝕜 ({s : Finset (Fin r) // Finset.card s = n} → (ExteriorPower 𝕜 E n)))
  . apply Smooth.quotientMapI
  . apply Smooth.pluckerMapLift



end Grassmannian
