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
