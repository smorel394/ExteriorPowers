import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.Multilinear


open Classical



universe u v w w₂

variable (R : Type u) (M : Type w) [Semiring R] [AddCommMonoid M]
[Module R M] [TopologicalSpace M] (N : Type w₂) [AddCommMonoid N] [Module R N] [TopologicalSpace N]
(ι : Type v)

structure ContinuousAlternatingMap extends AlternatingMap R M N ι where
cont : Continuous toFun

namespace ContinuousAlternatingMap

variable {R M N ι}

section Basic

variable (f g : ContinuousAlternatingMap R M N ι)

instance funLike : FunLike (ContinuousAlternatingMap R M N ι) (ι → M) (fun _ => N) where
  coe f := f.toFun
  coe_injective' := fun f g h ↦ by
    rcases f with ⟨_, _⟩
    rcases g with ⟨_, _⟩
    congr
    simp only [MultilinearMap.toFun_eq_coe, AlternatingMap.coe_multilinearMap, FunLike.coe_fn_eq] at h
    exact h


instance coeFun : CoeFun (ContinuousAlternatingMap R M N ι) fun _ => (ι → M) → N :=
  ⟨FunLike.coe⟩

@[simp]
theorem toFun_eq_coe : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : AlternatingMap R M N ι) (h) :
    ⇑(⟨f, h⟩ : ContinuousAlternatingMap R M N ι) = f :=
  rfl

theorem congr_fun {f g : ContinuousAlternatingMap R M N ι} (h : f = g) (x : ι → M) : f x = g x :=
  congr_arg (fun h : ContinuousAlternatingMap R M N ι => h x) h


theorem congr_arg (f : ContinuousAlternatingMap R M N ι) {x y : ι → M} (h : x = y) : f x = f y :=
  _root_.congr_arg (fun x : ι → M => f x) h

theorem coe_injective : Function.Injective ((↑) : ContinuousAlternatingMap R M N ι → (ι → M) → N) :=
  FunLike.coe_injective

@[norm_cast]
theorem coe_inj {f g : ContinuousAlternatingMap R M N ι} : (f : (ι → M) → N) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext {f f' : ContinuousAlternatingMap R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
  FunLike.ext _ _ H

theorem ext_iff {f g : ContinuousAlternatingMap R M N ι} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h _ => h ▸ rfl, fun h => ext h⟩

lemma toAlternatingMap_injective :
Function.Injective (ContinuousAlternatingMap.toAlternatingMap (R := R) (M := M) (N := N) (ι := ι)) := by
  intro f g heq
  ext x
  apply_fun (fun h => h.toFun) at heq
  change f.toFun = g.toFun at heq
  change f.toFun x = g.toFun x
  rw [heq]


def toContinuousMultilinearMap (m : ContinuousAlternatingMap R M N ι) :
ContinuousMultilinearMap R (fun (_ : ι) => M) N :=
{m.toAlternatingMap.toMultilinearMap with
 cont := m.cont}


lemma toContinuousMultilinearMap_injective :
Function.Injective (ContinuousAlternatingMap.toContinuousMultilinearMap (R := R) (M := M) (N := N) (ι := ι)) := by
  intro f g heq
  ext x
  apply_fun (fun h => h.toFun) at heq
  change f.toFun = g.toFun at heq
  change f.toFun x = g.toFun x
  rw [heq]


instance continuousMapClass : ContinuousMapClass (ContinuousAlternatingMap R M N ι) (ι → M) N
    where
  coe f := f.toFun
  coe_injective' _ _ h := ContinuousAlternatingMap.coe_injective h
  map_continuous := ContinuousAlternatingMap.cont

def Simps.apply (L₁ : ContinuousAlternatingMap R M N ι) (v : ι → M) : N :=
  L₁ v

initialize_simps_projections ContinuousAlternatingMap (-toMultilinearMap,
  toMultilinearMap_toFun → apply)

@[continuity]
theorem coe_continuous : Continuous (f : (ι → M) → N) :=
  f.cont

@[simp]
theorem coe_coe : (f.toAlternatingMap : (ι → M) → N) = f :=
  rfl

variable (v : ι → M)

@[simp]
theorem map_add [DecidableEq ι] (i : ι) (x y : M) :
    f (Function.update v i (x + y)) = f (Function.update v i x) + f (Function.update v i y) :=
  f.toAlternatingMap.map_add' v i x y


@[simp]
theorem map_smul [DecidableEq ι] (i : ι) (r : R) (x : M) :
    f (Function.update v i (r • x)) = r • f (Function.update v i x) :=
  f.toAlternatingMap.map_smul' v i r x

@[simp]
theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toAlternatingMap.map_coord_zero i h

@[simp]
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (Function.update m i 0) = 0 :=
  f.toAlternatingMap.map_update_zero m i

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toAlternatingMap.map_zero

theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 :=
f.toAlternatingMap.map_eq_zero_of_not_injective v hv

instance : Zero (ContinuousAlternatingMap R M N ι) :=
  ⟨{ (0 : AlternatingMap R M N ι) with cont := continuous_const }⟩

instance : Inhabited (ContinuousAlternatingMap R M N ι) :=
  ⟨0⟩

@[simp]
theorem zero_apply (m : ι → M) : (0 : ContinuousAlternatingMap R M N ι) m = 0 :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_zero : toContinuousMultilinearMap (0 : ContinuousAlternatingMap R M N ι) = 0 :=
  rfl

@[simp]
theorem toAlternatingMap_zero : (0 : ContinuousAlternatingMap R M N ι).toAlternatingMap = 0 :=
  rfl

section SMul

variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [Module A M]
  [Module A N] [DistribMulAction R' N] [ContinuousConstSMul R' N] [SMulCommClass A R' N]
  [DistribMulAction R'' N] [ContinuousConstSMul R'' N] [SMulCommClass A R'' N]

instance : SMul R' (ContinuousAlternatingMap A M N ι) :=
  ⟨fun c f => { c • f.toAlternatingMap with cont := f.cont.const_smul c }⟩

@[simp]
theorem smul_apply (f : ContinuousAlternatingMap A M N ι) (c : R') (m : ι → M) :
    (c • f) m = c • f m :=
  rfl

@[simp]
theorem toAlternatingMap_smul (c : R') (f : ContinuousAlternatingMap A M N ι) :
   (c • f).toAlternatingMap = c • f.toAlternatingMap :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_smul (c : R') (f : ContinuousAlternatingMap A M N ι) :
   toContinuousMultilinearMap (c • f) = c • (toContinuousMultilinearMap f) :=
  rfl

instance [SMulCommClass R' R'' N] : SMulCommClass R' R'' (ContinuousAlternatingMap A M N ι) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

instance [SMul R' R''] [IsScalarTower R' R'' N] :
    IsScalarTower R' R'' (ContinuousAlternatingMap A M N ι) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

instance [DistribMulAction R'ᵐᵒᵖ N] [IsCentralScalar R' N] :
    IsCentralScalar R' (ContinuousAlternatingMap A M N ι) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

instance : MulAction R' (ContinuousAlternatingMap A M N ι) :=
  Function.Injective.mulAction toContinuousMultilinearMap toContinuousMultilinearMap_injective fun _ _ => rfl

end SMul

section ContinuousAdd

variable [ContinuousAdd N]

instance : Add (ContinuousAlternatingMap R M N ι) :=
  ⟨fun f g => ⟨f.toAlternatingMap + g.toAlternatingMap, f.cont.add g.cont⟩⟩

@[simp]
theorem add_apply (m : ι → M) : (f + g) m = f m + g m :=
  rfl


@[simp]
theorem toAlternatingMap_add (f g : ContinuousAlternatingMap R M N ι) :
    (f + g).toAlternatingMap = f.toAlternatingMap + g.toAlternatingMap :=
  rfl

@[simp]
theorem toContinuousMultilinearMap_add (f g : ContinuousAlternatingMap R M N ι) :
    toContinuousMultilinearMap (f + g) = toContinuousMultilinearMap f + toContinuousMultilinearMap g :=
  rfl

instance addCommMonoid : AddCommMonoid (ContinuousAlternatingMap R M N ι) :=
  toContinuousMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl


def toContinuousMultilinearMapAddMonoidHom : AddMonoidHom (ContinuousAlternatingMap R M N ι)
(ContinuousMultilinearMap R (fun (_ : ι) => M) N) :=
{toFun := toContinuousMultilinearMap
 map_zero' := toContinuousMultilinearMap_zero
 map_add' := toContinuousMultilinearMap_add}

/-- Evaluation of a `ContinuousAlternatingMap` at a vector as an `AddMonoidHom`. -/
def applyAddHom (m : ι → M) : ContinuousAlternatingMap R M N ι →+ N where
  toFun f := f m
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem sum_apply {α : Type*} (f : α → ContinuousAlternatingMap R M N ι) (m : ι → M)
    {s : Finset α} : (Finset.sum s f) m = Finset.sum s (fun a => f a m) :=
  (applyAddHom m).map_sum f s

end ContinuousAdd

section SubNeg

variable {R' M' N' : Type*} [Ring R'] [AddCommGroup M'] [AddCommGroup N']
[Module R' M'] [Module R' N'] [TopologicalSpace M'] [TopologicalSpace N']
(v' : ι → M') (f' g' : ContinuousAlternatingMap R' M' N' ι)

@[simp]
theorem map_sub [DecidableEq ι] (i : ι) (x y : M') :
    g' (Function.update v' i (x - y)) = g' (Function.update v' i x) - g' (Function.update v' i y) :=
  g'.toAlternatingMap.map_sub v' i x y


@[simp]
theorem map_neg [DecidableEq ι] (i : ι) (x : M') : g' (Function.update v' i (-x)) = -g' (Function.update v' i x) :=
  g'.toAlternatingMap.map_neg v' i x

variable [TopologicalAddGroup N']

instance : Neg (ContinuousAlternatingMap R' M' N' ι) :=
  ⟨fun f => { -f.toAlternatingMap with cont := f.cont.neg }⟩

@[simp]
theorem neg_apply (m : ι → M') : (-g') m = -g' m :=
  rfl

instance subContinuousAlternatingMap : Sub (ContinuousAlternatingMap R' M' N' ι) :=
  ⟨fun f g => { f.toAlternatingMap - g.toAlternatingMap with cont := f.cont.sub g.cont }⟩

@[simp]
theorem sub_apply (m : ι → M') : (f' - g') m = f' m - g' m :=
  rfl

instance : AddCommGroup (ContinuousAlternatingMap R' M' N' ι) :=
  toContinuousMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl


end SubNeg

section DistribMulAction

variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [Module A M]
  [Module A N] [DistribMulAction R' N] [ContinuousConstSMul R' N] [SMulCommClass A R' N]
  [DistribMulAction R'' N] [ContinuousConstSMul R'' N] [SMulCommClass A R'' N]


instance [ContinuousAdd N] : DistribMulAction R' (ContinuousAlternatingMap A M N ι) :=
  Function.Injective.distribMulAction
    { toFun := toContinuousMultilinearMap,
      map_zero' := toContinuousMultilinearMap_zero,
      map_add' := toContinuousMultilinearMap_add }
    toContinuousMultilinearMap_injective
    fun _ _ => rfl

end DistribMulAction

section Module

variable {R' A : Type*} [Semiring R'] [Semiring A] [ContinuousAdd N] [Module A M]
  [Module A N] [Module R' N] [ContinuousConstSMul R' N] [SMulCommClass A R' N]

/-- The space of continuous alternating maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
instance : Module R' (ContinuousAlternatingMap A M N ι) :=
  Function.Injective.module _
    { toFun := toContinuousMultilinearMap,
      map_zero' := toContinuousMultilinearMap_zero,
      map_add' := toContinuousMultilinearMap_add }
    toContinuousMultilinearMap_injective fun _ _ => rfl

/-- Linear map version of the map `toAlternatingMap` associating to a continuous alternating map
the corresponding alternating map. -/
@[simps]
def toAlternatingMapLinear : ContinuousAlternatingMap A M N ι →ₗ[R'] AlternatingMap A M N ι where
  toFun f := f.toAlternatingMap
  map_add' := toAlternatingMap_add
  map_smul' := toAlternatingMap_smul

/-- Linear map version of the map `toContinuousMultilinearMap` associating to a continuous alternating map
the corresponding continuous multilinear map. -/
def toContinuousMultilinearMapLinear : ContinuousAlternatingMap A M N ι →ₗ[R']
ContinuousMultilinearMap A (fun (_ : ι) => M) N where
  toFun := toContinuousMultilinearMap
  map_add' := toContinuousMultilinearMap_add
  map_smul' := toContinuousMultilinearMap_smul

end Module

@[simps! toMultilinearMap apply_coe]
def codRestrict (f : ContinuousAlternatingMap R M N ι) (p : Submodule R N) (h : ∀ v, f v ∈ p) :
    ContinuousAlternatingMap R M p ι :=
  ⟨f.1.codRestrict p h, f.cont.subtype_mk _⟩

/- If `g` is continuous alternating and `f` is a continuous linear maps,
then `g (f m₁, ..., f mₙ)` is again a continuous alternating map, that we call
`g.compContinuousLinearMap f`. -/
variable {P} [AddCommMonoid P] [Module R P] [TopologicalSpace P]

def compContinuousLinearMap (g : ContinuousAlternatingMap R M N ι)
    (f : P →L[R] M) : ContinuousAlternatingMap R P N ι :=
  { g.toAlternatingMap.compLinearMap f.toLinearMap with
    cont := g.cont.comp <| continuous_pi fun _ => f.cont.comp <| continuous_apply _ }

@[simp]
theorem compContinuousLinearMap_apply (g : ContinuousAlternatingMap R M N ι)
    (f : P →L[R] M) (p : ι → P) :
    compContinuousLinearMap g f p = g (fun i => f (p i)) :=
    rfl


/-- Composing a continuous alternating map with a continuous linear map gives again a
continuous alternating map. -/
def _root_.ContinuousLinearMap.compContinuousAlternatingMap (g : N →L[R] P)
    (f : ContinuousAlternatingMap R M N ι) : ContinuousAlternatingMap R M P ι :=
  { g.toLinearMap.compAlternatingMap f.toAlternatingMap with cont := g.cont.comp f.cont }

@[simp]
theorem _root_.ContinuousLinearMap.compContinuousAlternatingMap_coe (g : N →L[R] P)
    (f : ContinuousAlternatingMap R M N ι) :
    (g.compContinuousAlternatingMap f : (ι → M) → P) =
      (g : N → P) ∘ (f : (ι → M) → N) := by
  ext m
  rfl

end Basic

section Norm

variable {𝕜 ι E F : Type*} [Fintype ι] [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
[NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable instance instNormedAddCommGroupContinuousAlternatingMap : NormedAddCommGroup
(ContinuousAlternatingMap 𝕜 E F ι) :=
NormedAddCommGroup.induced (ContinuousAlternatingMap 𝕜 E F ι) (ContinuousMultilinearMap 𝕜 (fun (_ : ι) => E) F)
toContinuousMultilinearMapAddMonoidHom toContinuousMultilinearMap_injective


noncomputable instance instNormedSpaceContinuousAlternatingMap : NormedSpace 𝕜 (ContinuousAlternatingMap 𝕜 E F ι) :=
NormedSpace.induced 𝕜 (ContinuousAlternatingMap 𝕜 E F ι) (ContinuousMultilinearMap 𝕜 (fun (_ : ι) => E) F)
toContinuousMultilinearMapLinear

end Norm

end ContinuousAlternatingMap

open BigOperators Finset

theorem MultilinearMap.norm_image_sub_le_of_bound'_sn {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG}
[Fintype ι] [NontriviallyNormedField 𝕜] [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
[SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (f : MultilinearMap 𝕜 E G) [DecidableEq ι] {C : ℝ} (hC : 0 ≤ C)
(H : ∀ (m : (i : ι) → E i), ‖f m‖ ≤ C * Finset.prod Finset.univ fun (i : ι) => ‖m i‖) (m₁ : (i : ι) → E i) (m₂ : (i : ι) → E i) :
‖f m₁ - f m₂‖ ≤   C *     Finset.sum Finset.univ fun (i : ι) =>
      Finset.prod Finset.univ fun (j : ι) => if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
  have A :
    ∀ s : Finset ι,
      ‖f m₁ - f (s.piecewise m₂ m₁)‖ ≤
        C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
    intro s
    induction' s using Finset.induction with i s his Hrec
    · simp
    have I :
      ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ ≤
        C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
      have A : (insert i s).piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₂ i) :=
        s.piecewise_insert _ _ _
      have B : s.piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₁ i) := by
        ext j
        by_cases h : j = i
        · rw [h]
          simp [his]
        · simp [h]
      rw [B, A, ← f.map_sub]
      apply le_trans (H _)
      gcongr with j
      · exact fun j _ => norm_nonneg _
      by_cases h : j = i
      · rw [h]
        simp
      · by_cases h' : j ∈ s <;> simp [h', h, le_refl]
    calc
      ‖f m₁ - f ((insert i s).piecewise m₂ m₁)‖ ≤
          ‖f m₁ - f (s.piecewise m₂ m₁)‖ +
            ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle _ _ _
      _ ≤
          (C * ∑ i in s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) +
            C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
        (add_le_add Hrec I)
      _ = C * ∑ i in insert i s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
        simp [his, add_comm, left_distrib]
  convert A univ
  simp


theorem MultilinearMap.norm_image_sub_le_of_bound_sn {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} [Fintype ι]
[NontriviallyNormedField 𝕜] [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)] [SeminormedAddCommGroup G]
[NormedSpace 𝕜 G] (f : MultilinearMap 𝕜 E G) {C : ℝ} (hC : 0 ≤ C) (H : ∀ (m : (i : ι) → E i),
‖f m‖ ≤ C * Finset.prod Finset.univ fun (i : ι) => ‖m i‖) (m₁ : (i : ι) → E i) (m₂ : (i : ι) → E i) :
‖f m₁ - f m₂‖ ≤ C * ↑(Fintype.card ι) * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
  classical
  have A :
    ∀ i : ι,
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) ≤
        ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
    intro i
    calc
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) ≤
          ∏ j : ι, Function.update (fun _ => max ‖m₁‖ ‖m₂‖) i ‖m₁ - m₂‖ j := by
        apply prod_le_prod
        · intro j _
          by_cases h : j = i <;> simp [h, norm_nonneg]
        · intro j _
          by_cases h : j = i
          · rw [h]
            simp only [ite_true, Function.update_same]
            exact norm_le_pi_norm (m₁ - m₂) i
          · simp [h, -le_max_iff, -max_le_iff, max_le_max, norm_le_pi_norm (_ : ∀ i, E i)]
      _ = ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
        rw [prod_update_of_mem (Finset.mem_univ _)]
        simp [card_univ_diff]
  calc
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
      f.norm_image_sub_le_of_bound'_sn hC H m₁ m₂
    _ ≤ C * ∑ _i, ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by gcongr; apply A
    _ = C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring



theorem MultilinearMap.continuous_of_bound_sn {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} [Fintype ι]
[NontriviallyNormedField 𝕜] [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)] [SeminormedAddCommGroup G]
[NormedSpace 𝕜 G] (f : MultilinearMap 𝕜 E G) (C : ℝ) (H : ∀ (m : (i : ι) → E i), ‖f m‖ ≤ C * Finset.prod Finset.univ
fun (i : ι) => ‖m i‖) :
Continuous f.toFun := by
  let D := max C 1
  have D_pos : 0 ≤ D := le_trans zero_le_one (le_max_right _ _)
  replace H : ∀ (m : (i : ι) → E i), ‖f m‖ ≤ D * Finset.prod Finset.univ (fun (i : ι) => ‖m i‖)
  · intro m
    apply le_trans (H m) (mul_le_mul_of_nonneg_right (le_max_left _ _) _)
    exact Finset.prod_nonneg fun (i : ι) _ => norm_nonneg (m i)
  refine' continuous_iff_continuousAt.2 fun m => _
  refine'
    continuousAt_of_locally_lipschitz zero_lt_one
      (D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1)) fun m' h' => _
  rw [dist_eq_norm, dist_eq_norm]
  have : max ‖m'‖ ‖m‖ ≤ ‖m‖ + 1 := by
    simp [zero_le_one, norm_le_of_mem_closedBall (le_of_lt h')]
  calc
    ‖f m' - f m‖ ≤ D * Fintype.card ι * max ‖m'‖ ‖m‖ ^ (Fintype.card ι - 1) * ‖m' - m‖ :=
      f.norm_image_sub_le_of_bound_sn D_pos H m' m
    _ ≤ D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1) * ‖m' - m‖ := by gcongr


namespace AlternatingMap

variable {𝕜 ι E F : Type*} [Fintype ι] [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
[SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Constructing a continuous alternating map from an alternating map satisfying a boundedness
condition. -/
def mkContinuousAlternating (f : AlternatingMap 𝕜 E F ι) (C : ℝ)
(H : ∀ (m : ι → E), ‖f m‖ ≤ C * Finset.prod Finset.univ (fun (i : ι) => ‖m i‖)) : ContinuousAlternatingMap 𝕜 E F ι :=
  { f with cont := f.continuous_of_bound_sn C H }


@[simp]
theorem coe_mkContinuousAlternating (f : AlternatingMap 𝕜 E F ι) (C : ℝ)
(H : ∀ (m : ι → E), ‖f m‖ ≤ C * Finset.prod Finset.univ (fun (i : ι) => ‖m i‖)) :
(AlternatingMap.mkContinuousAlternating f C H).toAlternatingMap = f :=
  rfl

end AlternatingMap
