import Mathlib.Tactic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.TensorPower
import ExteriorPowers.Lemmas
import Mathlib.Order.Extension.Well
import Mathlib.Data.Finite.Defs


namespace ExteriorAlgebra

variable {R M N N' : Type*}
variable [CommRing R] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N'] (n : ℕ)

-- Functoriality

def map (f : M →ₗ[R] N) : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R N :=
CliffordAlgebra.map {f with map_app' := by intro _; simp only [AddHom.toFun_eq_coe,
LinearMap.coe_toAddHom, QuadraticForm.zero_apply]}

@[simp]
theorem map_comp_ι (f : M →ₗ[R] N) :
LinearMap.comp (AlgHom.toLinearMap (map f)) (ι R) =
LinearMap.comp (ι R) f := CliffordAlgebra.map_comp_ι _

@[simp]
theorem map_apply_ι (f : M →ₗ[R] N) (m : M) :
(map f) ((ι R) m) = (ι R) (f m) :=
CliffordAlgebra.map_apply_ι _ m

@[simp]
theorem map_apply_ιMulti (f : M →ₗ[R] N) (m : Fin n → M) :
(map f) ((ιMulti R n) m) = (ιMulti R n) (f ∘ m) := by
  rw [ιMulti_apply, ιMulti_apply, map_list_prod]
  simp only [List.map_ofFn, Function.comp_apply]
  apply congrArg; apply congrArg
  ext i
  simp only [Function.comp_apply, map_apply_ι]


@[simp]
theorem map_comp_ιMulti (f : M →ₗ[R] N) :
(map f).toLinearMap.compAlternatingMap (ιMulti R n (M := M)) =
(ιMulti R n (M := N)).compLinearMap f := by
  ext m
  simp only [LinearMap.compAlternatingMap_apply, AlgHom.toLinearMap_apply, map_apply_ιMulti, Function.comp_apply,
    AlternatingMap.compLinearMap_apply]
  apply congrArg
  ext i
  simp only [Function.comp_apply]


@[simp]
theorem map_id :
map (LinearMap.id) = AlgHom.id R (ExteriorAlgebra R M) :=
CliffordAlgebra.map_id 0

@[simp]
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
AlgHom.comp (map g) (map f) = map (LinearMap.comp g f) := by
  unfold map
  rw [CliffordAlgebra.map_comp_map]
  apply congrArg
  ext m
  simp only [QuadraticForm.Isometry.comp_apply]
  change g (f m) = (LinearMap.comp g f) m
  simp only [LinearMap.coe_comp, Function.comp_apply]


@[simp]
theorem ι_range_map_map (f : M →ₗ[R] N) :
Submodule.map (AlgHom.toLinearMap (map f)) (LinearMap.range (ι R (M := M))) =
Submodule.map (ι R) (LinearMap.range f) :=
CliffordAlgebra.ι_range_map_map _




variable (R)

lemma ιMulti_range : Set.range (ιMulti R n) ⊆
(LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n).carrier := by
  rw [Set.range_subset_iff]
  intro v
  rw [ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  existsi fun i => ⟨(ι R) (v i), by simp only [SetLike.mem_coe, LinearMap.mem_range,
    ι_inj, exists_eq]⟩
  simp only

lemma ιMulti_span_fixedDegree :
Submodule.span R (Set.range (ιMulti R n)) =
(LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) := by
  apply le_antisymm
  . rw [Submodule.span_le]
    apply le_trans (ιMulti_range R n) (le_refl _)
  . change (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) ≤ _
    rw [Submodule.pow_eq_span_pow_set, Submodule.span_le]
    intro u hu
    apply Submodule.subset_span
    simp only [Set.mem_range]
    rw [Set.mem_pow] at hu
    obtain ⟨f, hfu⟩ := hu
    rw [←hfu]
    existsi fun i => ιInv (f i).1
    rw [ιMulti_apply]
    apply congrArg; apply congrArg
    ext i
    have h : (f i).1 ∈ LinearMap.range (ι R (M := M)) := by simp only [SetLike.coe_mem]
    rw [LinearMap.mem_range] at h
    obtain ⟨v, hv⟩ := h
    rw [←hv, ι_inj]
    erw [ι_leftInverse]

lemma ιMulti_span :
Submodule.span R (Set.range (fun (x : Σ (n : ℕ), (Fin n → M)) => ιMulti R x.1 x.2)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  apply DirectSum.Decomposition.inductionOn (fun i => LinearMap.range (ι R (M := M)) ^ i)
    (p := (fun m => m ∈ Submodule.span R (Set.range (fun (x : Σ (n : ℕ),
    (Fin n → M)) => ιMulti R x.1 x.2))))
  . simp only [Submodule.zero_mem]
  . intro i ⟨_, hm⟩
    apply Set.mem_of_mem_of_subset hm
    rw [←ιMulti_span_fixedDegree]
    apply Submodule.span_mono
    intro x hx
    simp only [Set.mem_range, Sigma.exists] at hx ⊢
    obtain ⟨y, hyx⟩ := hx
    rw [←hyx]
    existsi i; existsi y
    rfl
  . exact fun _ _ hm hm' => Submodule.add_mem _ hm hm'


noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) :
{s : Finset I // Finset.card s = n} → ExteriorAlgebra R M := by
  intro ⟨s, hs⟩
  have e := Finset.orderIsoOfFin s hs
  exact ιMulti R n (fun i => v (e i))



variable {R}

lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
Function.Injective (map f) := by
  obtain ⟨g, hgf⟩ := hf
  apply Function.RightInverse.injective (g := map g)
  intro m
  rw [←AlgHom.comp_apply, map_comp_map, hgf, map_id]
  simp only [AlgHom.coe_id, id_eq]

lemma map_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f) :
Function.Surjective (map f) := by
  rw [←LinearMap.range_eq_top, LinearMap.range_eq_map, ←ιMulti_span, ←ιMulti_span,
    Submodule.map_span, ←Set.range_comp]
  apply congrArg
  ext y
  simp only [Set.mem_range, Function.comp_apply, map_apply_ιMulti, Sigma.exists]
  constructor
  . intro hy
    obtain ⟨n, x, hx⟩ := hy
    existsi n
    existsi f ∘ x
    rw [←hx]
  . intro hy
    obtain ⟨n, x, hx⟩ := hy
    existsi n
    existsi (fun i => Classical.choose (hf (x i)))
    rw [←hx]
    apply congrArg
    ext i
    simp only [Function.comp_apply]
    exact Classical.choose_spec (hf (x i))


variable {K E F: Type*} [Field K] [AddCommGroup E]
  [Module K E] [AddCommGroup F] [Module K F]

lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
Function.Injective (map f) :=
map_injective (LinearMap.exists_leftInverse_of_injective f hf)

end ExteriorAlgebra
