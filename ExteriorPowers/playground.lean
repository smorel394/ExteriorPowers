import Mathlib.Data.Set.Finite

variable (n : ℕ)

def s := ((Finset.range n).sigma fun k =>
           (Finset.univ.filter (fun (l : Finset.range n) => k + l < n)).sigma fun l =>
           (Finset.univ : Finset ({s : Finset (Fin (k + l)) // s.card = l})))

#check s

example (n : ℕ) :
    Set.Finite {p : (k : ℕ) × (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l} |
    p.1 < n ∧ p.2.1 < n} := by
  convert_to Set.Finite ((Finset.range n).sigma fun k =>
    (Finset.range n).sigma fun l =>
      (Finset.univ : Finset ({s : Finset (Fin (k + l)) // s.card = l}))).toSet
  · ext ⟨k, l, s⟩
    simp
  apply Finset.finite_toSet


def f : (k : ℕ) × (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l} → ℕ × ℕ := fun p ↦ ⟨p.1, p.2.1⟩

def g (k l : ℕ) : f ⁻¹' {⟨k, l⟩} → Finset (Fin (k + l)) :=
          fun x ↦ by have h := Prod.eq_iff_fst_eq_snd_eq.mp
                       (Set.mem_singleton_iff.mp (Set.mem_preimage.mp x.2))
                     simp only at h
                     refine cast ?_ x.1.2.2.1
                     simp_rw [← h.1, ← h.2, f]

example (k l : ℕ) : Function.Injective (g k l) := by
  intro x y
  have hx := Prod.eq_iff_fst_eq_snd_eq.mp (Set.mem_singleton_iff.mp (Set.mem_preimage.mp x.2))
  have hy := Prod.eq_iff_fst_eq_snd_eq.mp (Set.mem_singleton_iff.mp (Set.mem_preimage.mp y.2))
  unfold f at hx hy
  simp only at hx hy
  intro h
  unfold g at h
  simp only at h
  have hx1 := hx.1
  ext
  · rw [hx.1, hy.1]
  · apply heq_of_cast_eq
    sorry
    sorry


theorem Set.Finite.of_finite_image_of_finite_fibers {α : Type*} {β : Type*} {s : Set α}
    {f : α → β} (hfin1 : Set.Finite (f '' s)) (hfin2 : ∀ y ∈ f '' s, Set.Finite (f ⁻¹' {y})) :
    Set.Finite s :=
  Set.Finite.subset (Set.Finite.biUnion hfin1 hfin2) (fun x hx ↦ Set.mem_biUnion
  (Set.mem_image_of_mem f hx) (by rw [Set.mem_preimage, Set.mem_singleton_iff]))

open Set in
example (n : ℕ) :
    Set.Finite {p : (k : ℕ) × (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l} |
    p.1 < n ∧ p.2.1 < n} := by
  set s := {p : (k : ℕ) × (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l} |
      p.1 < n ∧ p.2.1 < n}
  rw [Set.finite_def]
  apply Nonempty.intro
  set g : s → (k : Finset.range n) × (l : Finset.range n) ×
        {s : Finset (Fin (k + l)) | s.card = l} := (fun p =>
          ⟨⟨p.1.1, Finset.mem_range.mpr p.2.1⟩, ⟨p.1.2.1, Finset.mem_range.mpr p.2.2⟩, p.1.2.2⟩)
  set h : (k : Finset.range n) × (l : Finset.range n) ×
        {s : Finset (Fin (k + l)) | s.card = l} → s :=
        fun p => by refine ⟨⟨p.1, p.2.1, p.2.2⟩, ?_⟩
                    simp only [coe_setOf, mem_setOf_eq]
                    exact ⟨Finset.mem_range.mp p.1.property, Finset.mem_range.mp p.2.1.property⟩
  have h1 : ∀ x, h (g x) = x := by
        intro ⟨p, hp⟩
        simp only [coe_setOf, mem_setOf_eq, Sigma.eta]
  have h2 : ∀ x, g (h x) = x := by
        intro ⟨k, l, t⟩
        simp only [coe_setOf, mem_setOf_eq, id_eq]
  set e : s ≃ (k : Finset.range n) × (l : Finset.range n) ×
        {s : Finset (Fin (k + l)) | s.card = l} :=
        {toFun := g
         invFun := h
         left_inv := h1
         right_inv := h2}
  apply Fintype.ofEquiv _ e.symm


example (n : ℕ) :
    Set.Finite {p : (k : ℕ) × (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l} |
    p.1 < n ∧ p.2.1 < n} := by sorry


example (k l : ℕ) : Function.Injective (g k l) := by
  intro x y
  have hx := Prod.eq_iff_fst_eq_snd_eq.mp (Set.mem_singleton_iff.mp (Set.mem_preimage.mp x.2))
  have hy := Prod.eq_iff_fst_eq_snd_eq.mp (Set.mem_singleton_iff.mp (Set.mem_preimage.mp y.2))
  unfold f at hx hy
  simp only at hx hy
  intro h
  ext
  · rw [hx.1, hy.1]
  · apply heq_of_cast_eq
    sorry

open Set

example (n : ℕ) :
    Set.Finite {p : (k : ℕ) × (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l} |
    p.1 < n ∧ p.2.1 < n} := by
  set s := {p : (k : ℕ) × (l : ℕ) × {s : Finset (Fin (k + l)) // s.card = l} |
      p.1 < n ∧ p.2.1 < n}
  rw [Set.finite_def]
  apply Nonempty.intro
  set g : s → (k : Finset.range n) × (l : Finset.range n) ×
        {s : Finset (Fin (k + l)) | s.card = l} := (fun p =>
          ⟨⟨p.1.1, Finset.mem_range.mpr p.2.1⟩, ⟨p.1.2.1, Finset.mem_range.mpr p.2.2⟩, p.1.2.2⟩)
  set h : (k : Finset.range n) × (l : Finset.range n) ×
        {s : Finset (Fin (k + l)) | s.card = l} → s :=
        fun p => by refine ⟨⟨p.1, p.2.1, p.2.2⟩, ?_⟩
                    simp only [coe_setOf, mem_setOf_eq]
                    exact ⟨Finset.mem_range.mp p.1.property, Finset.mem_range.mp p.2.1.property⟩
  have h1 : ∀ x, h (g x) = x := by
        intro ⟨p, hp⟩
        simp only [coe_setOf, mem_setOf_eq, Sigma.eta]
  have h2 : ∀ x, g (h x) = x := by
        intro ⟨k, l, t⟩
        simp only [coe_setOf, mem_setOf_eq, id_eq]
  set e : s ≃ (k : Finset.range n) × (l : Finset.range n) ×
        {s : Finset (Fin (k + l)) | s.card = l} :=
        {toFun := g
         invFun := h
         left_inv := h1
         right_inv := h2}
  apply Fintype.ofEquiv _ e.symm
