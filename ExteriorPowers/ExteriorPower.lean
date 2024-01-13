import ExteriorPowers.ExteriorAlgebra

set_option maxHeartbeats 300000

open BigOperators

variable (R M N N' : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N'] (n : ℕ)

variable {K E F: Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/--Definition of the `n`th exterior power-/
abbrev ExteriorPower := (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n)

namespace ExteriorPower

/-- The `n`th exterior power of a finite module is a finite module.-/
def Finite [Module.Finite R M]: Module.Finite R (ExteriorPower R M n) :=
  Module.Finite.mk ((Submodule.fg_top _).mpr (Submodule.FG.pow (by
  rw [LinearMap.range_eq_map]; exact Submodule.FG.map _  (Module.finite_def.mp inferInstance)) _ ))

variable {R M N N'}

/-! We prove the universal property of the `n`th exterior power of `M`: linear maps from
`ExteriorPower R M n` to a module `N` are in linear equivalence with `n`-fold alternating maps from
`M` to `N`-/

def liftAlternating_aux : (AlternatingMap R M N (Fin n)) →ₗ[R]
((i : ℕ) → AlternatingMap R M N (Fin i)) :=
  LinearMap.pi (fun i ↦ if h : i = n then by rw [h]; exact LinearMap.id else 0)

/-- The linear map from `n`-fold alternating maps from `M` to `N` to linear maps from
`ExteriorPower R n M` to `N`-/
def liftAlternating : (AlternatingMap R M N (Fin n)) →ₗ[R] ExteriorPower R M n →ₗ[R] N where
  toFun f := LinearMap.domRestrict (LinearMap.comp (ExteriorAlgebra.liftAlternating (R := R)
    (M := M) (N :=N)) (liftAlternating_aux n) f) (ExteriorPower R M n)
  map_add' f g := by ext u; simp only [map_add, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.domRestrict_apply, LinearMap.add_apply]
  map_smul' a f := by ext u; simp only [map_smul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.domRestrict_apply, LinearMap.smul_apply, RingHom.id_apply]

variable (R)

/-- The canonical alternating map from `(Fin n) → M` to `ExteriorPower R M n`.-/
def ιMulti : AlternatingMap R M (ExteriorPower R M n) (Fin n) :=
  AlternatingMap.codRestrict (ExteriorAlgebra.ιMulti R n) (ExteriorPower R M n)
  (fun _ => ExteriorAlgebra.ιMulti_range R n (by simp only [Set.mem_range, exists_apply_eq_apply]))

@[simp] lemma ιMulti_apply (a : Fin n → M) :
ιMulti R n a = ExteriorAlgebra.ιMulti R n a := by
  unfold ιMulti
  simp only [AlternatingMap.codRestrict_apply_coe]

/-- Variant of `ExteriorAlgebra.ιMulti_span_fixedDegree`, useful in rewrites.-/
lemma ιMulti_span_fixedDegree :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) = ExteriorPower R M n :=
  ExteriorAlgebra.ιMulti_span_fixedDegree R n

/-- The image of `ExteriorPower.ιMulti` spans `ExteriorPower R M n`.-/
lemma ιMulti_span :
    Submodule.span R (Set.range (ιMulti R n)) = (⊤ : Submodule R (ExteriorPower R M n)) := by
  apply LinearMap.map_injective (Submodule.ker_subtype (ExteriorPower R M n))
  rw [LinearMap.map_span, ← Set.image_univ, Set.image_image]
  simp only [Submodule.coeSubtype, ιMulti_apply, Set.image_univ, Submodule.map_top,
    Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_fixedDegree R n

/-- Two linear maps on `ExteriorPower R M n` that agree on the image of `ExteriorPower.ιMulti`
are equal.-/
@[ext]
lemma lhom_ext ⦃f : ExteriorPower R M n →ₗ[R] N⦄ ⦃g : ExteriorPower R M n →ₗ[R] N⦄
    (heq : (LinearMap.compAlternatingMap f) (ιMulti R n) =
    (LinearMap.compAlternatingMap g) (ιMulti R n)) : f = g := by
  ext u
  have hu : u ∈ (⊤ : Submodule R (ExteriorPower R M n)) := Submodule.mem_top
  rw [← ιMulti_span] at hu
  apply Submodule.span_induction hu (p := fun u => f u = g u)
  · exact fun _ h ↦ by
      let ⟨a, ha⟩ := Set.mem_range.mpr h
      apply_fun (fun F => F a) at heq; simp only [LinearMap.compAlternatingMap_apply] at heq
      rw [← ha, heq]
  · rw [LinearMap.map_zero, LinearMap.map_zero]
  · exact fun _ _ h h' => by rw [LinearMap.map_add, LinearMap.map_add, h, h']
  · exact fun _ _ h => by rw [LinearMap.map_smul, LinearMap.map_smul, h]

@[simp] lemma liftAlternating_apply_ιMulti (f : AlternatingMap R M N (Fin n)) (a : Fin n → M) :
    liftAlternating n f (ιMulti R n a) = f a := by
  unfold liftAlternating
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.domRestrict_apply]
  rw [ιMulti_apply, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  unfold liftAlternating_aux
  simp only [eq_mpr_eq_cast, LinearMap.pi_apply, cast_eq, dite_eq_ite, ite_true,
    LinearMap.id_coe, id_eq]

@[simp] lemma liftAlternating_comp_ιMulti (f : AlternatingMap R M N (Fin n)) :
    (LinearMap.compAlternatingMap (liftAlternating n f)) (ιMulti R n) = f := by
  ext a
  simp only [LinearMap.compAlternatingMap_apply]
  rw [liftAlternating_apply_ιMulti]

@[simp] lemma liftAlternating_ιMulti :
    liftAlternating n (R := R) (M := M) (ιMulti R n) = LinearMap.id := by
  ext u
  simp only [liftAlternating_comp_ιMulti, ιMulti_apply, LinearMap.compAlternatingMap_apply,
    LinearMap.id_coe, id_eq]

/-- If `f` is an alternating map from `M` to `N`, `liftAlternating n f` is the corresponding
linear map from `ExteriorPower R M n` to `N` and `g` is a linear map from `N` to `N'`, then
the alternating map `g.compAlternatingMap f` from `M` to `N'` corresponds to the linear
map `g.comp (liftAlternating n f)` on `ExteriorPower R M n`.-/
@[simp]
lemma liftAlternating_comp (g : N →ₗ[R] N') (f : AlternatingMap R M N (Fin n)) :
    liftAlternating n (g.compAlternatingMap f) = g.comp (liftAlternating n f) := by
  ext u
  simp only [liftAlternating_comp_ιMulti, LinearMap.compAlternatingMap_apply, LinearMap.coe_comp,
    Function.comp_apply, liftAlternating_apply_ιMulti]

/-- The linear equivalence between `n`-fold alternating maps from `M` to `N` and linear maps from
`ExteriorPower R M n` to `N`.-/
@[simps!]
def liftAlternatingEquiv : AlternatingMap R M N (Fin n) ≃ₗ[R] ExteriorPower R M n →ₗ[R] N :=
  LinearEquiv.ofLinear (liftAlternating n)
  {toFun := fun F ↦ F.compAlternatingMap (ιMulti R n)
   map_add' := by intro F G; ext x
                  simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
                    AlternatingMap.add_apply]
   map_smul' := by intro a F; ext x
                   simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
                     RingHom.id_apply, AlternatingMap.smul_apply]}
  (by ext _; simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        liftAlternating_comp, liftAlternating_ιMulti, LinearMap.comp_id,
        LinearMap.compAlternatingMap_apply, LinearMap.id_coe, id_eq])
  (by ext _; simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        liftAlternating_comp_ιMulti, LinearMap.id_coe, id_eq])

@[simp]
lemma liftAlternatingEquiv_apply (f :AlternatingMap R M N (Fin n)) (x : ExteriorPower R M n) :
  ExteriorPower.liftAlternatingEquiv R n f x = ExteriorPower.liftAlternating n f x := rfl

@[simp]
lemma liftAlternatingEquiv_symm_apply (F : ExteriorPower R M n →ₗ[R] N) (m : Fin n → M) :
  (ExteriorPower.liftAlternatingEquiv R n).symm F m = F.compAlternatingMap (ιMulti R n) m := rfl

/-! Functoriality of the exterior powers.-/

variable {R}

/-- The linear map between `n`th exterior powers induced by a linear map between the modules.-/
def map (f : M →ₗ[R] N) : ExteriorPower R M n →ₗ[R] ExteriorPower R N n := by
  refine LinearMap.restrict (AlgHom.toLinearMap (ExteriorAlgebra.map f)) ?_
  intro x hx
  rw [← ιMulti_span_fixedDegree] at hx ⊢
  have hx := Set.mem_image_of_mem (ExteriorAlgebra.map f) hx
  rw [← Submodule.map_coe, LinearMap.map_span, ←Set.range_comp] at hx
  erw [← (LinearMap.coe_compAlternatingMap (ExteriorAlgebra.map f).toLinearMap
    (ExteriorAlgebra.ιMulti R n))] at hx
  rw [ExteriorAlgebra.map_comp_ιMulti, AlternatingMap.coe_compLinearMap] at hx
  exact Set.mem_of_mem_of_subset hx (Submodule.span_mono (Set.range_comp_subset_range _ _))

@[simp]
theorem map_apply_ιMulti (f : M →ₗ[R] N) (m : Fin n → M) :
    (map n f) ((ιMulti R n) m) = (ιMulti R n) (f ∘ m) := by
  unfold map
  rw [LinearMap.restrict_apply, ← SetCoe.ext_iff]
  simp only [ιMulti_apply, AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti]

@[simp]
theorem map_comp_ιMulti (f : M →ₗ[R] N) :
    (map n f).compAlternatingMap (ιMulti R n (M := M)) = (ιMulti R n (M := N)).compLinearMap f := by
  unfold map
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.restrict_coe_apply, ιMulti_apply,
    AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  congr

@[simp]
theorem map_id :
    map n (LinearMap.id) = LinearMap.id (R := R) (M := ExteriorPower R M n) := by
  unfold map
  ext m
  simp only [ExteriorAlgebra.map_id, AlgHom.toLinearMap_id, LinearMap.compAlternatingMap_apply,
    LinearMap.restrict_coe_apply, ιMulti_apply, LinearMap.id_coe, id_eq]

@[simp]
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    LinearMap.comp (map n g) (map n f) = map n (LinearMap.comp g f) := by
  unfold map
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.restrict_coe_apply, ιMulti_apply, AlgHom.toLinearMap_apply,
    ExteriorAlgebra.map_apply_ιMulti, Function.comp.assoc]

/-- If a linear map has a retraction, then the map it induces on exterior powers is injective.-/
lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
    Function.Injective (map n f) :=
  let ⟨g, hgf⟩ := hf
  Function.RightInverse.injective (g := map n g)
    (fun _ ↦ by rw [← LinearMap.comp_apply, map_comp_map, hgf, map_id, LinearMap.id_coe, id_eq])

/-- If the base ring is a field, then any injective linear map induces an injective map on
exterior powers.-/
lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
    Function.Injective (map n f) :=
  map_injective n (LinearMap.exists_leftInverse_of_injective f hf)

/-- If a linear map is surjective, then the map it induces on exterior powers is surjective.-/
lemma map_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (map n f) := by
  rw [← LinearMap.range_eq_top, LinearMap.range_eq_map, ← ιMulti_span, ← ιMulti_span,
    Submodule.map_span, ← Set.range_comp, ← LinearMap.coe_compAlternatingMap, map_comp_ιMulti,
    AlternatingMap.coe_compLinearMap, Set.range_comp]
  conv_rhs => rw [← Set.image_univ]
  congr; apply congrArg
  exact Set.range_iff_surjective.mpr (fun y ↦ ⟨fun i => Classical.choose (hf (y i)),
    by ext i; simp only [Function.comp_apply]; exact Classical.choose_spec (hf (y i))⟩)

variable (R)

/-- Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, produce the
family of `n`fold exterior products of elements of `v`, seen as members of the
`n`th exterior power.-/
noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) :
    {s : Finset I // Finset.card s = n} → ExteriorPower R M n :=
  fun ⟨s, hs⟩ => ιMulti R n (fun i => v (Finset.orderIsoOfFin s hs i))

@[simp]
lemma ιMulti_family_coe {I : Type*} [LinearOrder I] (v : I → M) :
    ExteriorAlgebra.ιMulti_family R n v = (Submodule.subtype _) ∘ (ιMulti_family R n v) := by
  ext s
  unfold ιMulti_family
  simp only [Submodule.coeSubtype, Finset.coe_orderIsoOfFin_apply, Function.comp_apply,
    ιMulti_apply]
  rfl

lemma map_ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) (f : M →ₗ[R] N) :
    (map n f) ∘ (ιMulti_family R n v) = ιMulti_family R n (f ∘ v) := by
  ext ⟨s, hs⟩
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, Function.comp_apply, map_apply_ιMulti, ιMulti_apply]
  congr

/-! Generators of exterior powers.-/

open Finset in
/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`ExteriorPower R M n`. Here we work in the exterior algebra.-/
lemma span_top_of_span_top {I : Type*} [LinearOrder I] {v : I → M}
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti_family R n v)) = ExteriorPower R M n := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    exact fun _ ↦ by simp only [ιMulti_family_coe, Submodule.coeSubtype, Function.comp_apply,
                                SetLike.mem_coe, SetLike.coe_mem]
  · change (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n) ≤ _
    rw [LinearMap.range_eq_map, ← hv, Submodule.map_span, Submodule.span_pow, Submodule.span_le]
    intro u hu
    obtain ⟨f, hf⟩ := Set.mem_pow.mp hu
    set g : Fin n → M := fun i => ExteriorAlgebra.ιInv (f i).1
    have hfg : ∀ (i : Fin n), (f i).1 = ExteriorAlgebra.ι R (g i) := by
      intro i
      obtain ⟨_, hv⟩ := LinearMap.mem_range.mp (let ⟨y, hy⟩ := ((Set.mem_image _ _ _).mp (f i).2);
        LinearMap.mem_range.mpr ⟨y, hy.2⟩)
      simp only
      rw [← hv, ExteriorAlgebra.ι_inj]
      erw [ExteriorAlgebra.ι_leftInverse]
    have heq : u = ExteriorAlgebra.ιMulti R n g := by
      rw [ExteriorAlgebra.ιMulti_apply, ← hf]
      congr
      exact funext (fun i ↦ hfg i)
    rw [heq]
    have hg : ∀ (i : Fin n), ∃ (j : I), g i = v j := by
      intro i
      let ⟨x, hx⟩ := (Set.mem_image _ _ _).mp (f i).2
      let ⟨j, hj⟩ := Set.mem_range.mp hx.1
      rw [hfg i, ExteriorAlgebra.ι_inj] at hx
      exact ⟨j, by rw [hj, hx.2]⟩
    set α : Fin n → I := fun i => Classical.choose (hg i)
    set αprop := fun i => Classical.choose_spec (hg i)
    by_cases hinj : Function.Injective α
    · --set s := Finset.image α Finset.univ
      set h : Fin n → image α univ := fun i => ⟨α i, by simp only [mem_image, mem_univ, true_and,
        exists_apply_eq_apply]⟩
      have hbij : Function.Bijective h := by
        constructor
        · intro i j hij
          rw [Subtype.mk.injEq] at hij
          exact hinj hij
        · intro ⟨i, hi⟩
          rw [Finset.mem_image] at hi
          obtain ⟨a, ha⟩ := hi
          existsi a
          simp only [Subtype.mk.injEq]
          exact ha.2
      have hcard : (image α univ).card = n := by
        suffices h : Fintype.card (image α univ) = n
        · conv_rhs => rw [← h]
          simp only [mem_image, mem_univ, true_and, Fintype.card_coe]
        · rw [← Fintype.card_of_bijective hbij]
          simp only [Fintype.card_fin]
      set g' : Fin n → M := fun i => v (orderIsoOfFin _ hcard i)
      have hg' : ExteriorAlgebra.ιMulti R n g' ∈ Submodule.span R (Set.range
        (ExteriorAlgebra.ιMulti_family R n v)) := by
        apply Submodule.subset_span
        rw [Set.mem_range]
        existsi ⟨_, hcard⟩
        unfold ExteriorAlgebra.ιMulti_family
        simp only [coe_orderIsoOfFin_apply]
      set σ : Equiv.Perm (Fin n) := (Equiv.ofBijective h hbij).trans
        (orderIsoOfFin _ hcard).toEquiv.symm
      have hgg' : g = g' ∘ σ := by
        ext i
        rw [Function.comp_apply, Equiv.trans_apply]
        change g i = v (orderIsoOfFin _ hcard _)
        erw [Equiv.apply_symm_apply (orderIsoOfFin _ hcard).toEquiv]
        simp only [Equiv.ofBijective_apply]
        exact αprop i
      rw [hgg', AlternatingMap.map_perm]
      exact Submodule.smul_mem _ _ hg'
    · change ¬(∀ (a b : Fin n), _) at hinj
      push_neg at hinj
      obtain ⟨i, j, hij1, hij2⟩ := hinj
      have heq : g = Function.update g i (g j) := by
        ext k
        by_cases hk : k = i
        · rw [Function.update_apply]
          simp only [hk, ite_true]
          change g i = g j
          rw [αprop i, αprop j]
          change v (α i) = v (α j)
          rw [hij1]
        · simp only [ne_eq, hk, not_false_eq_true, Function.update_noteq]
      rw [heq, AlternatingMap.map_update_self _ _ hij2]
      simp only [SetLike.mem_coe, Submodule.zero_mem]

/-- If a family of vectors spans `M`, then the family of its `n`-fold exterior products spans
`ExteriorPower R M n`. This is a variant of `ExteriorPower.span_top_of_span_top` where we
work in the exterior power and not the exterior algebra.-/
lemma span_top_of_span_top' {I : Type*} [LinearOrder I]
{v : I → M} (hv : Submodule.span R (Set.range v) = ⊤) :
Submodule.span R  (Set.range (ιMulti_family R n v)) = ⊤ := by
  rw [eq_top_iff]
  intro ⟨u, hu⟩ _
  rw [← span_top_of_span_top R n hv, ιMulti_family_coe,
    Set.range_comp, ← Submodule.map_span, Submodule.mem_map] at hu
  obtain ⟨w, hw, huw⟩ := hu
  have heq : ⟨u, hu⟩ = w := by rw [← SetCoe.ext_iff]; simp only [Submodule.coeSubtype] at huw ⊢
                               exact (Eq.symm huw)
  rw [heq]
  exact hw

/-- If `v` is a family of vectors of `M` indexed by a linearly ordered type, then the span of the
range of `ExteriorPower.ιMult_family R n v`, i.e. of the family of `n`-fold exterior products
of elements of `v`, is the image of the map of exterior powers induced by the inclusion of
the span of `v` into `M`..-/
lemma span_of_span {I : Type*} [LinearOrder I] (v : I → M) :
LinearMap.range (map n (Submodule.subtype (Submodule.span R (Set.range v)))) =
  Submodule.span R (Set.range (ιMulti_family R n v)) := by
  rw [LinearMap.range_eq_map, ← (span_top_of_span_top' (I := I) (R := R) (v := fun i =>
    ⟨v i, by apply Submodule.subset_span; simp only [Set.mem_range, exists_apply_eq_apply]⟩)),
    Submodule.map_span, ← Set.range_comp]
  · congr; apply congrArg
    rw [map_ιMulti_family]
    congr
  · apply SetLike.coe_injective'
    apply Set.image_injective.mpr (Submodule.injective_subtype (Submodule.span R (Set.range v)))
    rw [← Submodule.map_coe, ← Submodule.span_image, ← Submodule.map_coe, ← LinearMap.range_eq_map,
      Submodule.range_subtype]
    rw [← Set.range_comp]
    congr

variable (M)

/-- The linear map from the `n`th exterior power to the `n`th tensor power induced by
`MultilinearMap.alternarization`.-/
noncomputable def toTensorPower : ExteriorPower R M n →ₗ[R] TensorPower R n M :=
  liftAlternatingEquiv R n
  (MultilinearMap.alternatization (PiTensorProduct.tprod R (s := fun (_ : Fin n) => M)))

variable {M}

@[simp]
lemma toTensorPower_apply_ιMulti (v : Fin n → M) : toTensorPower R M n (ιMulti R n v) =
    Finset.sum Finset.univ (fun (σ : Equiv.Perm (Fin n)) => Equiv.Perm.sign σ •
    (PiTensorProduct.tprod R (fun i => v (σ i)))) := by
  unfold toTensorPower
  simp only [liftAlternatingEquiv_apply, liftAlternating_apply_ιMulti]
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply]

/-- A family `f` indexed by `Fin n` of linear forms on `M` defines a linear form on the `n`th tensor
power of `M`, by multiplying the components of `f`.-/
noncomputable def _root_.TensorPower.linearFormOfFamily (f : (i : Fin n) → (M →ₗ[R] R)) :
    TensorPower R n M →ₗ[R] R :=
  PiTensorProduct.lift (MultilinearMap.compLinearMap (MultilinearMap.mkPiRing R (Fin n) 1) f)

@[simp]
lemma _root_.TensorPower.linearFormOfFamily_apply_tprod (f : (i : Fin n) → (M →ₗ[R] R)) (v : Fin n → M) :
    TensorPower.linearFormOfFamily R n f (PiTensorProduct.tprod R v) =
    Finset.prod Finset.univ (fun i => (f i (v i))) := by
  unfold TensorPower.linearFormOfFamily
  simp only [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one]

/-- A family `f` indexed by `Fin n` of linear forms on `M` defines a linear form on the `n`th
exterior power of `M`, by composing the map `ExteriorPower.toTensorPower` to the `n`th tensor
power and then applying `TensorPower.linearFormOfFamily` (which takes the product of the
components of `f`).-/
noncomputable def linearFormOfFamily (f : (i : Fin n) → (M →ₗ[R] R)) :
    ExteriorPower R M n →ₗ[R] R :=
  LinearMap.comp (TensorPower.linearFormOfFamily R n f) (toTensorPower R M n)

@[simp]
lemma linearFormOfFamily_apply (f : (i : Fin n) → (M →ₗ[R] R)) (x : ExteriorPower R M n) :
    linearFormOfFamily R n f x = TensorPower.linearFormOfFamily R n f (toTensorPower R M n x) := by
  unfold linearFormOfFamily
  simp only [LinearMap.coe_comp, Function.comp_apply]

@[simp]
lemma linearFormOfFamily_apply_ιMulti (f : (i : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    linearFormOfFamily R n f (ιMulti R n m) = ∑ σ : Equiv.Perm (Fin n),
    Equiv.Perm.sign σ • ∏ i, f i (m (σ i)) := by
  simp only [linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum,
    LinearMap.map_smul_of_tower, TensorPower.linearFormOfFamily_apply_tprod]

/-- If `f` is a family of linear forms on `M` (index by `Fin n`) and `p` is a linear map
from `N` to `M`, then the composition of `ExteriorPower.linearFormOfFamily R n f` and
of `ExteriorPower.map p` is equal to the linear form induced by the family
`fun i ↦ (f i).comp p`..-/
lemma linearFormOfFamily_comp_map (f : (i : Fin n) → (M →ₗ[R] R)) (p : N →ₗ[R] M) :
    (linearFormOfFamily R n f).comp (map n p) =
    linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) := by
  apply LinearMap.ext_on (ιMulti_span R n (M := N))
  intro x hx
  obtain ⟨y, h⟩ := Set.mem_range.mp hx
  simp only [← h, LinearMap.coe_comp, Function.comp_apply, map_apply_ιMulti,
    linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum, LinearMap.map_smul_of_tower,
    TensorPower.linearFormOfFamily_apply_tprod]

@[simp]
lemma linearFormOfFamily_comp_map_apply (f : (i : Fin n) → (M →ₗ[R] R))
    (p : N →ₗ[R] M) (x : ExteriorPower R N n) :
    (linearFormOfFamily R n f) (map n p x) =
    linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) x := by
  rw [← LinearMap.comp_apply, linearFormOfFamily_comp_map]

/-- A family `f` of linear forms on `M` indexed by `Fin n` defines an `n`-fold alternating form
on `M`, by composing the linear form on `ExteriorPower R M n` indeuced by `f` (defined in
`ExteriorPower.linearFormOfFamily`) with the canonical `n`-fold alternating map from `M` to its
`n`th exterior power.-/
noncomputable def alternatingFormOfFamily (f : (i : Fin n) → (M →ₗ[R] R)) :
    AlternatingMap R M R (Fin n) :=
  (linearFormOfFamily R n f).compAlternatingMap (ιMulti R n)

@[simp]
lemma alternatingFormOfFamily_apply (f : (i : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    alternatingFormOfFamily R n f m = linearFormOfFamily R n f (ιMulti R n m) := by
  unfold alternatingFormOfFamily
  rw [LinearMap.compAlternatingMap_apply]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `ExteriorPower.linearFormOfFamily` construction to the fanily of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`).-/
noncomputable def linearFormOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) : ExteriorPower R M n →ₗ[R] R :=
  linearFormOfFamily R n (fun i => b.coord (Finset.orderIsoOfFin s hs i))

@[simp]
lemma linearFormOfBasis_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) (v : Fin n → M) :
    linearFormOfBasis R n b hs (ιMulti R n v) = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
    ∏ i, b.coord (Finset.orderIsoOfFin s hs i) (v (σ i)) := by
  unfold linearFormOfBasis
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfFamily_apply, toTensorPower_apply_ιMulti,
    map_sum, LinearMap.map_smul_of_tower, TensorPower.linearFormOfFamily_apply_tprod,
    Basis.coord_apply]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. If we apply the linear form on `ExteriorPower R M n` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`.-/
lemma linearFormOfBasis_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
{s : Finset I} (hs : Finset.card s = n) :
    linearFormOfBasis R n b hs (ιMulti_family R n b ⟨s, hs⟩) = 1 := by
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfBasis_apply_ιMulti]
  have hzero : ∀ (σ : Equiv.Perm (Fin n)), σ ∈ Finset.univ → ¬σ ∈ ({Equiv.refl (Fin n)} :
    Finset (Equiv.Perm (Fin n))) → TensorPower.linearFormOfFamily R n (fun i => b.coord (Finset.orderIsoOfFin s hs i))
    (Equiv.Perm.sign σ • ⨂ₜ[R] (i : Fin n), b ((Finset.orderIsoOfFin s hs) (σ i))) = 0 := by
    intro σ _ hσ
    simp only [Finset.mem_singleton] at hσ
    erw [LinearMap.map_smul]
    apply smul_eq_zero_of_right
    simp only [Finset.coe_orderIsoOfFin_apply, TensorPower.linearFormOfFamily_apply_tprod]
    have h : ∃ (i : Fin n), ¬ σ i = i := by
      by_contra habs
      push_neg at habs
      apply hσ
      ext i
      simp only [Equiv.refl_apply]
      rw [habs i]
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _)
    rw [Basis.coord_apply, Basis.repr_self_apply]
    simp only [Finset.coe_orderIsoOfFin_apply, OrderEmbedding.eq_iff_eq, ite_eq_right_iff]
    simp only [hi, IsEmpty.forall_iff]
  have heq := Finset.sum_subset (s₁ := {Equiv.refl (Fin n)}) (Finset.subset_univ _) hzero
  simp only [Finset.coe_orderIsoOfFin_apply, LinearMap.map_smul_of_tower,
    TensorPower.linearFormOfFamily_apply_tprod, Basis.coord_apply, Basis.repr_self, ne_eq,
    RelEmbedding.inj, Finset.sum_singleton, Equiv.Perm.sign_refl, Equiv.refl_apply,
    Finsupp.single_eq_same, Finset.prod_const_one, one_smul] at heq ⊢
  rw [←heq]

lemma linearFormOfBasis_apply_nondiag_aux {I : Type*} [LinearOrder I] {s t : Finset I}
    (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) (σ : Equiv.Perm (Fin n)) :
    ∃ (i : Fin n), (Finset.orderIsoOfFin s hs i).1 ≠ (Finset.orderIsoOfFin t ht (σ i)).1 := by
  by_contra habs
  push_neg at habs
  apply hst
  apply Finset.eq_of_subset_of_card_le
  · intro a has
    set b := Finset.orderIsoOfFin t ht (σ ((Finset.orderIsoOfFin s hs).symm ⟨a, has⟩))
    have heq : a = b.1 := by
      rw [←habs]
      simp only [OrderIso.apply_symm_apply]
    rw [heq]
    exact b.2
  · rw [hs, ht]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠ t`. If we apply
the linear form on `ExteriorPower R M n` defined by `b` and `s` to the exterior product of the
`b i` for `i ∈ t`, then we get `0`.-/
lemma linearFormOfBasis_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s t : Finset I} (hs : Finset.card s = n) (ht : Finset.card t = n) (hst : s ≠ t) :
    linearFormOfBasis R n b hs (ιMulti_family R n b ⟨t, ht⟩) = 0 := by
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, linearFormOfBasis_apply_ιMulti]
  apply Finset.sum_eq_zero
  intro σ _
  erw [zsmul_eq_smul_cast R]
  apply smul_eq_zero_of_right
  obtain ⟨i, hi⟩ := linearFormOfBasis_apply_nondiag_aux n hs ht hst σ
  apply Finset.prod_eq_zero (a := i) (Finset.mem_univ _)
  rw [Basis.coord_apply, Basis.repr_self_apply]
  simp only [Finset.coe_orderIsoOfFin_apply, ne_eq] at hi
  simp only [Finset.coe_orderIsoOfFin_apply, Ne.symm hi, ite_false]

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`ExteriorPower.ιMulti R n b` of the `n`th fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`.-/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  linearIndependent_of_dualFamily R _ (fun s => linearFormOfBasis R n b s.2)
  (fun ⟨_, _⟩ ⟨_, _⟩ hst ↦
  by simp only [ne_eq, Subtype.mk.injEq] at hst; simp only [Function.comp_apply]
     exact linearFormOfBasis_apply_nondiag _ _ _ _ _ hst)
  (fun ⟨_, _⟩ ↦ by simp only [Function.comp_apply]; apply linearFormOfBasis_apply_diag)

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`th fold exterior products of elements of `b`..-/
noncomputable def BasisOfBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis {s : Finset I // Finset.card s = n} R (ExteriorPower R M n) :=
  Basis.mk (v := ιMulti_family R n b) (ιMulti_family_linearIndependent_ofBasis _ _ _)
  (by rw [span_top_of_span_top']; rw [Basis.span_eq])

@[simp]
lemma BasisOfBasis_coe {I : Type*} [LinearOrder I] (b : Basis I R M) :
    FunLike.coe (BasisOfBasis R n b) = ιMulti_family R n b := Basis.coe_mk _ _

@[simp]
lemma BasisOfBasis_apply {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    BasisOfBasis R n b ⟨s, hs⟩ = ιMulti_family R n b ⟨s, hs⟩ := by rw [BasisOfBasis_coe]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the corresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th exterior power
defined by `b` and `s` in `ExteriorPower.linearFormOfBasis`.-/
lemma BasisOfBasis_coord {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s : Finset I} (hs : Finset.card s = n) :
    Basis.coord (BasisOfBasis R n b) ⟨s, hs⟩ = linearFormOfBasis R n b hs := by
  apply LinearMap.ext_on (span_top_of_span_top' R n (Basis.span_eq b))
  intro x hx
  obtain ⟨⟨t, ht⟩, htx⟩ := Set.mem_range.mp hx
  rw [← htx]
  conv_lhs => rw [← BasisOfBasis_apply]
  by_cases heq : s = t
  · have heq' : (⟨s, hs⟩ : {s : Finset I // Finset.card s = n}) = ⟨t, ht⟩ := by
      simp only [Subtype.mk.injEq]; exact heq
    simp only [← heq', linearFormOfBasis_apply_diag, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same]
  · simp only [linearFormOfBasis_apply_nondiag R n b hs ht heq, Basis.coord_apply,
      Basis.repr_self_apply, Subtype.mk.injEq, Ne.symm heq, ite_false]

/-- If `M` is a free module, then so is its `n`th exterior power.-/
lemma FreeOfFree (hfree : Module.Free R M) : Module.Free R (ExteriorPower R M n) :=
  let ⟨I, b⟩ := (Classical.choice hfree.exists_basis)
  letI := WellFounded.wellOrderExtension (emptyWf (α := I)).wf
  Module.Free.of_basis (BasisOfBasis R n b)

variable [StrongRankCondition R]

/-- If `R` satisfies the strong rank condition and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`.-/
lemma FinrankOfFiniteFree (hfree : Module.Free R M) [Module.Finite R M] :
    FiniteDimensional.finrank R (ExteriorPower R M n) =
    Nat.choose (FiniteDimensional.finrank R M) n :=
  letI := WellFounded.wellOrderExtension (emptyWf (α := hfree.ChooseBasisIndex)).wf
  let B :=  BasisOfBasis R n (hfree.chooseBasis)
  by rw [FiniteDimensional.finrank_eq_card_basis hfree.chooseBasis,
    FiniteDimensional.finrank_eq_card_basis B, Fintype.card_finset_len]

-- TODO: Freeness, finite-dimensionality and dimension for the whole exterior algebra.

variable {R}

lemma range_map_comp_le (f : N' →ₗ[R] N) (g : N →ₗ[R] M) :
    LinearMap.range (map n (g.comp f)) ≤
    LinearMap.range (map n g) := by
  intro x hx
  rw [LinearMap.mem_range] at hx ⊢
  obtain ⟨y, hyx⟩ := hx
  rw [← hyx]
  have hy : y ∈ (⊤ : Submodule R (ExteriorPower R N' n)) := by simp only [Submodule.mem_top]
  rw [← ExteriorPower.ιMulti_span] at hy
  apply Submodule.span_induction hy (p := fun y => ∃ z, (map n g) z =
    (map n (g.comp f)) y)
  · intro x hx
    obtain ⟨m, hmx⟩ := Set.mem_range.mp hx
    existsi ExteriorPower.ιMulti R n (M := N) (fun i => f (m i))
    rw [ExteriorPower.map_apply_ιMulti, ← hmx, ExteriorPower.map_apply_ιMulti]
    apply congrArg
    ext i
    simp only [Function.comp_apply, LinearMap.coe_comp]
  · existsi 0
    simp only [map_zero]
  · intro x y ⟨z, hz⟩ ⟨z', hz'⟩
    existsi z + z'
    rw [LinearMap.map_add, LinearMap.map_add, hz, hz']
  · intro a y ⟨z, hz⟩
    existsi a • z
    rw [LinearMap.map_smul, LinearMap.map_smul, hz]

lemma map_subtype (P Q : Submodule R M) (hPQ : P ≤ Q) :
    ∃ (f : P →ₗ[R] Q), Submodule.subtype P = (Submodule.subtype Q).comp f := by
  existsi
   { toFun := fun x ↦ ⟨x.1, hPQ x.2⟩
     map_add' := fun x y ↦ by simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid,
       AddSubmonoid.mk_add_mk]
     map_smul' := fun a x ↦ by simp only [SetLike.val_smul, RingHom.id_apply, SetLike.mk_smul_mk]
     }
  ext x
  simp only [Submodule.coeSubtype, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply]

lemma mem_ExteriorPowerSup {P Q : Submodule R M} (x : ExteriorPower R P n) (y : ExteriorPower R Q n) :
    ExteriorPower.map n (Submodule.subtype P) x + ExteriorPower.map n (Submodule.subtype Q) y ∈
    LinearMap.range (ExteriorPower.map n (Submodule.subtype (P ⊔ Q))) := by
  apply Submodule.add_mem
  · let ⟨f, hf⟩ := map_subtype P (P ⊔ Q) le_sup_left
    rw [hf]
    apply range_map_comp_le n f (Submodule.subtype (P ⊔ Q))
    simp only [LinearMap.mem_range, exists_apply_eq_apply]
  · let ⟨f, hf⟩ := map_subtype Q (P ⊔ Q) le_sup_right
    rw [hf]
    apply range_map_comp_le n f (Submodule.subtype (P ⊔ Q))
    simp only [LinearMap.mem_range, exists_apply_eq_apply]

/-- Every element of ExteriorPower R M n is in the image of ExteriorPower R P n, for some finitely
generated submodule P of M.-/
lemma mem_exteriorPowerFiniteSubmodule (x : ExteriorPower R M n) :
    ∃ (P : Submodule R M), Submodule.FG P ∧ x ∈ LinearMap.range (ExteriorPower.map n
    (Submodule.subtype P)) := by
  have hx : x ∈ (⊤ : Submodule R (ExteriorPower R M n)) := by simp only [Submodule.mem_top]
  rw [←ExteriorPower.ιMulti_span] at hx
  apply Submodule.span_induction hx (p := fun x => ∃ (P : Submodule R M), Submodule.FG P ∧ x ∈ LinearMap.range
    (ExteriorPower.map n (Submodule.subtype P)))
  · intro x hx
    rw [Set.mem_range] at hx
    obtain ⟨m, hmx⟩ := hx
    existsi Submodule.span R (Set.range m)
    rw [and_iff_right (Submodule.fg_span (Set.finite_range m)), LinearMap.mem_range]
    have hm : ∀ (i : Fin n), m i ∈ Submodule.span R (Set.range m) := by
      intro i
      apply Submodule.subset_span
      simp only [Set.mem_range, exists_apply_eq_apply]
    existsi ιMulti R n (fun i => ⟨m i, hm i⟩)
    simp only [Subtype.mk.injEq, map_apply_ιMulti, Submodule.coeSubtype, Function.comp_apply]
    rw [←hmx]
    apply congrArg
    ext i
    simp only [Function.comp_apply]
  · existsi (⊥ : Submodule R M)
    exact ⟨Submodule.fg_bot, Submodule.zero_mem _⟩
  · intro x y ⟨Px, hx⟩ ⟨Py, hy⟩
    existsi Px ⊔ Py
    rw [and_iff_right (Submodule.FG.sup hx.1 hy.1)]
    rw [LinearMap.mem_range] at hx hy
    obtain ⟨x', hxx'⟩ := hx.2
    obtain ⟨y', hyy'⟩ := hy.2
    rw [←hxx', ←hyy']
    exact mem_ExteriorPowerSup n x' y'
  · intro a x ⟨P, h⟩
    existsi P
    exact ⟨h.1, Submodule.smul_mem _ a h.2⟩

/-! Results that only work over a field.-/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent.-/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  set W := Submodule.span K (Set.range v)
  set v' : I → W := fun i => ⟨v i, by apply Submodule.subset_span; simp only [Set.mem_range,
    exists_apply_eq_apply]⟩
  set f := Submodule.subtype W
  have hvv' : v = f ∘ v' := by
    ext i
    simp only [Submodule.coeSubtype, Function.comp_apply]
  have hv' : LinearIndependent K (ιMulti_family K n v') := by
    have hv'li : LinearIndependent K v' := by
      apply LinearIndependent.of_comp f; rw [←hvv']; exact hv
    have hv'span : ⊤ ≤ Submodule.span K (Set.range v') := by
      simp only [top_le_iff]
      ext x
      simp only [Submodule.mem_top, iff_true]
      rw [←(Submodule.apply_mem_span_image_iff_mem_span (Submodule.injective_subtype W)), ←Set.range_comp, ←hvv']
      simp only [Submodule.coeSubtype, SetLike.coe_mem]
    set B := BasisOfBasis K n (Basis.mk hv'li hv'span)
    have heq : ιMulti_family K n v' = B := by
      simp only [BasisOfBasis_coe, Basis.coe_mk]
    rw [heq]
    exact Basis.linearIndependent B
  rw [hvv', ←map_ιMulti_family]
  apply LinearIndependent.map' hv'
  rw [LinearMap.ker_eq_bot]
  apply map_injective_field
  simp only [Submodule.ker_subtype]

lemma nonemptyOfNonempty {I : Type*} [LinearOrder I]
    (hne : Nonempty {v : I → E // LinearIndependent K v}) :
    Nonempty {v : {s : Finset I // Finset.card s = n} →
    ExteriorPower K E n // LinearIndependent K v} := by
  set v := Classical.choice hne
  exact Nonempty.intro ⟨ιMulti_family K n v, ιMulti_family_linearIndependent_field n v.2⟩

end ExteriorPower
