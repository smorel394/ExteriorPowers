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


noncomputable abbrev PluckerMapLift := ExteriorPower.ιMulti_family

lemma PluckerMapLift_isLift {v : Fin r → V} (hv : LinearIndependent K v) :
PluckerMap K V r n (Grassmannian.mk K v hv) = Grassmannian.mkI K
(by rw [Fintype.card_finset_len, Fintype.card_fin])
(PluckerMapLift K n v) (ExteriorPower.ιMulti_family_linearIndependent_field n hv) := by
  unfold PluckerMap PluckerMapLift
  rw [←SetCoe.ext_iff]; simp only
  conv_rhs => rw [Grassmannian.mkI_apply]
  have heq : Submodule.subtype (Grassmannian.mk K v hv).1 = Submodule.subtype (Submodule.span K (Set.range v)) := by
    congr
  rw [heq]
sorry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] [SeparatingDual 𝕜 E]
[Nonempty (Grassmannian 𝕜 E r)]

variable (𝕜 E)

variable [Nonempty (Grassmannian 𝕜 (ExteriorPower 𝕜 E n) (Nat.choose r n))] [SeparatingDual 𝕜 (ExteriorPower 𝕜 E n)]

lemma Smooth.pluckerMap : ContMDiff (ModelGrassmannian 𝕜 (ModelSpace 𝕜 E r) r)
(ModelGrassmannian 𝕜 (ModelSpace 𝕜 (ExteriorPower 𝕜 E n) (Nat.choose r n)) (Nat.choose r n)) ⊤
(PluckerMap 𝕜 E r n) := by
  apply Smooth.mapFromGrassmannian
  sorry




end Grassmannian
