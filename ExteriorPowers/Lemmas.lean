import Mathlib.Tactic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.PiTensorProduct

lemma Basis.constr_ker {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M' : Type u_7} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] (b : Basis ι R M) (S : Type u_10)
    [Semiring S] [Module S M'] [SMulCommClass R S M'] {v : ι → M'} (hv : LinearIndependent R v) :
    LinearMap.ker (Basis.constr b S v) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro _ hu
  rw [LinearMap.mem_ker, Basis.constr_apply, ← Finsupp.total_apply, ← LinearMap.mem_ker, hv,
    Submodule.mem_bot, AddEquivClass.map_eq_zero_iff] at hu
  exact hu

lemma LinearMap.graph_fst_injective {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) :
    Function.Injective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f)) := by
  intro ⟨v, hv⟩ ⟨v', hv'⟩ hvv'
  rw [LinearMap.mem_graph_iff] at hv hv'
  simp only [domRestrict_apply, fst_apply] at hvv'
  rw [Subtype.mk.injEq, Prod.ext_iff, and_iff_right hvv', hv, hv', hvv']

lemma LinearMap.graph_fst_surjective {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) :
    Function.Surjective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f)) :=
  fun v ↦ by simp only [domRestrict_apply, fst_apply, Subtype.exists, mem_graph_iff, exists_prop,
               Prod.exists, exists_eq_left, exists_eq]

noncomputable def LinearMap.graph_equiv_fst {R : Type u} {M : Type v} {M₂ : Type w} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) :
    LinearMap.graph f ≃ₗ[R] M :=
  LinearEquiv.ofBijective ((LinearMap.fst R M M₂).domRestrict (LinearMap.graph f))
  ⟨LinearMap.graph_fst_injective f, LinearMap.graph_fst_surjective f⟩

theorem contDiffOn_open_iff_contDiffAt_finite {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} {f : E → F} {n : ℕ} (hs : IsOpen s) :
    ContDiffOn 𝕜 n f s ↔ ∀ (x : s), ContDiffAt 𝕜 n f x := by
  constructor
  · exact fun h x ↦ ContDiffOn.contDiffAt h (IsOpen.mem_nhds hs x.2)
  · intro h
    apply contDiffOn_of_locally_contDiffOn
    intro x hxs
    obtain ⟨U, hU1, hU2, hU3⟩ := ContDiffWithinAt.contDiffOn' (m := n) (le_refl _)
      (ContDiffAt.contDiffWithinAt (s := ⊤) (h ⟨x, hxs⟩))
    existsi U
    simp only at hU2
    simp only [hU1, hU2, true_and]
    simp only [Set.top_eq_univ, Set.mem_univ, Set.insert_eq_of_mem, Set.univ_inter] at hU3
    exact ContDiffOn.mono hU3 (by simp only [Set.inter_subset_right])

theorem contDiffOn_open_iff_contDiffAt {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} {f : E → F} {n : ℕ∞} (hs : IsOpen s) :
    ContDiffOn 𝕜 n f s ↔ ∀ (x : s), ContDiffAt 𝕜 n f x := by
  by_cases hn : n = ⊤
  · constructor
    · exact fun h x ↦ ContDiffOn.contDiffAt h (IsOpen.mem_nhds hs x.2)
    · rw [hn, contDiffOn_top]
      intro h n
      rw [contDiffOn_open_iff_contDiffAt_finite hs]
      exact fun x ↦ by apply ContDiffAt.of_le (h x) (by simp only [le_top])
  · rw [← ne_eq, WithTop.ne_top_iff_exists] at hn
    obtain ⟨m, hm⟩ := hn
    rw [← hm]
    exact contDiffOn_open_iff_contDiffAt_finite hs

lemma contMDiff_of_contMDiffAt {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] {E' : Type u_5} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type u_6} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') {M' : Type u_7}
    [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M'] (n : ℕ)
    (f : M → M') (hdiff : ∀ (x : M), ContMDiffAt I I' n f x) : ContMDiff I I' n f := by
  apply contMDiff_of_locally_contMDiffOn
  intro x
  obtain ⟨s, hs1, hs2⟩ := contMDiffAt_iff_contMDiffOn_nhds.mp (hdiff x)
  obtain ⟨U, hUs, hUopen, hUx⟩:= mem_nhds_iff.mp hs1
  existsi U
  rw [and_iff_right hUopen, and_iff_right hUx]
  exact ContMDiffOn.mono hs2 hUs

lemma contMDiff_iff_contMDiffAt {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] {E' : Type u_5} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type u_6} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') {M' : Type u_7}
    [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M'] (n : ℕ∞)
    (f : M → M') : ContMDiff I I' n f ↔ ∀ (x : M), ContMDiffAt I I' n f x := by
  constructor
  · exact fun hdiff _ => ContMDiff.contMDiffAt hdiff
  · intro hdiff
    by_cases htop : n = ⊤
    · rw [htop] at hdiff ⊢
      change Smooth _ _ _
      rw [contMDiff_top]
      exact fun _ ↦ contMDiff_of_contMDiffAt _ _ _ _ (fun x ↦ ContMDiffAt.of_le (hdiff x) le_top)
    · rw [← ne_eq, WithTop.ne_top_iff_exists] at htop
      obtain ⟨m, hm⟩ := htop
      rw [← hm] at hdiff ⊢
      exact contMDiff_of_contMDiffAt _ _ _ _ (fun x ↦ ContMDiffAt.of_le (hdiff x) (le_refl _))

lemma linearIndependent_of_dualFamily {ι : Type*} (R : Type*) {M : Type*} (v : ι → M)
    [Semiring R] [AddCommMonoid M] [Module R M] (dv : ι → (M →ₗ[R] R))
    (h1 : ∀ (a : ι) (b : ι), a ≠ b → (dv a) (v b) = 0) (h2 : ∀ (a : ι), (dv a) (v a) = 1) :
    LinearIndependent R v := by
  rw [linearIndependent_iff']
  intro s g hrel i hi
  apply_fun (fun x => dv i x) at hrel
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hrel
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [h1 i j (Ne.symm hj), mul_zero])
    (fun hi' ↦ False.elim (hi' hi)), h2 i, mul_one] at hrel
  exact hrel

lemma vector_normalize (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x : E) : ∃ (y : E) (a : 𝕜), ‖y‖ ≤ 1 ∧ x = a • y  := by
  by_cases hx : ‖x‖ = 0
  · existsi x; existsi 1
    rw [hx, one_smul]
    simp only [zero_le_one, and_self]
  · have hx' : 0 < ‖x‖⁻¹ := by
      rw [lt_iff_le_and_ne]
      simp only [inv_nonneg, norm_nonneg, ne_eq, zero_eq_inv, Ne.symm hx, not_false_eq_true,
        and_self]
    obtain ⟨a, ha⟩ := NormedField.exists_norm_lt 𝕜 hx'
    existsi a • x; existsi a⁻¹
    rw [norm_smul, smul_smul, inv_mul_cancel, one_smul]
    · simp only [and_true]
      exact le_trans (mul_le_mul (le_of_lt ha.2) (le_refl _) (norm_nonneg _) (by simp only
        [inv_nonneg, norm_nonneg])) (by rw [inv_mul_cancel hx])
    · exact fun h ↦ by rw [h, norm_zero] at ha; exact lt_irrefl 0 ha.1

/- These next two results would be nice to have but I don't need them.-/
/-
lemma Cardinal.le_of_map (α β : Type u) (f : α → β) [Infinite β] (hcard : ∀ (b :β), Cardinal.mk (f ⁻¹' {b}) ≤ Cardinal.mk β) :
Cardinal.mk α ≤  Cardinal.mk β := sorry

lemma Cardinal.mk_finset_len_infinite (I : Type*) [Infinite I] {n : ℕ} (hn : n > 0) :
Cardinal.mk {s : Finset I // Finset.card s = n} = Cardinal.mk α := by sorry
-/
