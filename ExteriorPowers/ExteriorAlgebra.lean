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

/-! Functoriality of the exterior algebra.-/

/-- The morphism of exterior algebras induced by a morphism of modules.-/
def map (f : M →ₗ[R] N) : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R N :=
  CliffordAlgebra.map {f with map_app' := by intro _; simp only [AddHom.toFun_eq_coe,
  LinearMap.coe_toAddHom, QuadraticForm.zero_apply]}

@[simp]
theorem map_comp_ι (f : M →ₗ[R] N) :
    LinearMap.comp (AlgHom.toLinearMap (map f)) (ι R) = LinearMap.comp (ι R) f :=
  CliffordAlgebra.map_comp_ι _

@[simp]
theorem map_apply_ι (f : M →ₗ[R] N) (m : M) : (map f) ((ι R) m) = (ι R) (f m) :=
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
  exact congrArg _ (by ext i; simp only [Function.comp_apply])

@[simp]
theorem map_id :
    map (LinearMap.id) = AlgHom.id R (ExteriorAlgebra R M) :=
CliffordAlgebra.map_id 0

@[simp]
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    AlgHom.comp (map g) (map f) = map (LinearMap.comp g f) := by
  ext m
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_apply_ι, map_comp_ι]

@[simp]
theorem ι_range_map_map (f : M →ₗ[R] N) :
    Submodule.map (AlgHom.toLinearMap (map f)) (LinearMap.range (ι R (M := M))) =
    Submodule.map (ι R) (LinearMap.range f) :=
  CliffordAlgebra.ι_range_map_map _

variable (R)

/-- The image of `ExteriorAlgebra.ιMulti R n` is contained in the `n`th exterior power.-/
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

/-- The image of `ExteriorAlgebra.ιMulti R n` spans the `n`th exterior power, as a submodule
of the exterior algebra.-/
lemma ιMulti_span_fixedDegree :
    Submodule.span R (Set.range (ιMulti R n)) =
    (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) := by
  refine le_antisymm (by rw [Submodule.span_le]; apply le_trans (ιMulti_range R n) (le_refl _)) ?_
  rw [Submodule.pow_eq_span_pow_set, Submodule.span_le]
  refine fun u hu ↦ Submodule.subset_span ?_
  obtain ⟨f, hfu⟩ := Set.mem_pow.mp hu
  rw [Set.mem_range, ← hfu]
  existsi fun i => ιInv (f i).1
  rw [ιMulti_apply]
  congr
  ext i
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (by simp only [SetLike.coe_mem] :
    (f i).1 ∈ LinearMap.range (ι R (M := M)))
  rw [← hv, ι_inj]; erw [ι_leftInverse]

/-- If we see `ExteriorAlgebra.ιMulti R n` as a map into the `n`th exterior power, then its image
spans the whole space (variant of `ExteriorAlegbra.ιMulti_span_fixedDegree`).-/
lemma ιMulti_span :
    Submodule.span R (Set.range (fun (x : Σ (n : ℕ), (Fin n → M)) => ιMulti R x.1 x.2)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  refine DirectSum.Decomposition.inductionOn (fun i => LinearMap.range (ι R (M := M)) ^ i)
    (p := (fun m => m ∈ Submodule.span R (Set.range (fun (x : Σ (n : ℕ),
    (Fin n → M)) => ιMulti R x.1 x.2)))) (by simp only [Submodule.zero_mem]) ?_
    (fun _ _ hm hm' => Submodule.add_mem _ hm hm')
  intro i ⟨_, hm⟩
  apply Set.mem_of_mem_of_subset hm
  simp only
  rw [← ιMulti_span_fixedDegree]
  refine Submodule.span_mono (fun _ hx ↦ ?_)
  simp only [Set.mem_range, Sigma.exists] at hx ⊢
  obtain ⟨y, hyx⟩ := hx
  rw [← hyx]
  existsi i, y
  rfl

/-- Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, produce the
family of `n`fold exterior products of elements of `v`, seen as members of the exterior algebra.-/
noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) :
    {s : Finset I // Finset.card s = n} → ExteriorAlgebra R M :=
  fun ⟨s, hs⟩ ↦ ιMulti R n (fun i => v (Finset.orderIsoOfFin s hs i))

variable {R}

lemma _root_.CliffordAlgebra.map_injective
    {Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N} (f : Q₁ →qᵢ Q₂) (hf : ∃ (g : Q₂ →qᵢ Q₁),
    g.comp f = QuadraticForm.Isometry.id _) : Function.Injective (CliffordAlgebra.map f) :=
  let ⟨g, hg⟩ := hf
  Function.RightInverse.injective (g := CliffordAlgebra.map g)
  (fun x ↦ by rw [← AlgHom.comp_apply, CliffordAlgebra.map_comp_map, hg, CliffordAlgebra.map_id,
        AlgHom.coe_id, id_eq])

lemma _root_.CliffordAlgebra.map_surjective
{Q₁ : QuadraticForm R M} {Q₂ : QuadraticForm R N} (f : Q₁ →qᵢ Q₂) (hf : Function.Surjective f):
Function.Surjective (CliffordAlgebra.map f) := by
  rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, Submodule.eq_top_iff']
  intro y
  apply CliffordAlgebra.induction (C:= fun y ↦ y ∈ Submodule.map (CliffordAlgebra.map f) ⊤)
  all_goals (simp only [Submodule.map_top, LinearMap.mem_range, forall_exists_index])
  · exact fun r ↦ ⟨(algebraMap R (CliffordAlgebra Q₁)) r, by simp only [AlgHom.commutes]⟩
  · exact fun y ↦ let ⟨x, hx⟩ := hf y; ⟨CliffordAlgebra.ι Q₁ x,
      by simp only [CliffordAlgebra.map_apply_ι, hx]⟩
  · exact fun _ _ x  hx x' hx' ↦ ⟨x * x', by simp only [map_mul, hx, hx']⟩
  · exact fun _ _ x hx x' hx' ↦ ⟨x + x', by simp only [map_add, hx, hx']⟩

/-- A morphism of modules that is injective and admits a linear section induces an injective
morphism of exterior algebras.-/
lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
    Function.Injective (map f) :=
  let ⟨g, hgf⟩ := hf
  Function.RightInverse.injective (g := map g) (fun _ ↦
  by rw [← AlgHom.comp_apply, map_comp_map, hgf, map_id]; simp only [AlgHom.coe_id, id_eq])

/-- A surjective morphism of modules induces a surjective morphism of exterior algebras.-/
lemma map_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (map f) := CliffordAlgebra.map_surjective _ hf

variable {K E F: Type*} [Field K] [AddCommGroup E]
  [Module K E] [AddCommGroup F] [Module K F]

/-- An injective morphism of vector spaces induces an injective morphism of exterior algebras.-/
lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
    Function.Injective (map f) :=
  map_injective (LinearMap.exists_leftInverse_of_injective f hf)

end ExteriorAlgebra
