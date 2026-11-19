import FiniteAvalanches.Support.Plane.ReachabilityPath

/-!
# Walk paths and an omitted edge

A walk using selected edges meets an omitted edge only at its endpoints.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical

/-- The selected drawing trace meets an omitted edge only at its endpoints. -/
theorem Drawing.trace_inter_omitted_edge {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (A : Finset E) (e : E) (he : e ∉ A) :
    D.trace Set.univ A ∩ range (D.curve e) ⊆
      {D.point (G.left e), D.point (G.right e)} := by
  rintro z ⟨hz, ⟨t, ht⟩⟩
  have hends : t.val = 0 ∨ t.val = 1 := by
    rcases hz with ⟨v, _, hv⟩ | ⟨f, hf, s, hs⟩
    · rcases (D.curve_vertex_iff e t v).mp (ht.trans hv.symm) with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · have hef : e ≠ f := fun h => he (h ▸ hf)
      exact (D.intersects e f hef t s (ht.trans hs.symm)).1
  rcases hends with h0 | h1
  · have ht0 : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext h0
    rw [← ht, ht0, D.start]
    simp
  · have ht1 : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h1
    rw [← ht, ht1, D.finish]
    simp

/-- A walk between an omitted edge's endpoints has a drawing path which meets
that edge only at the endpoints. -/
theorem Drawing.exists_path_of_reaches_inter_omitted_edge {V E : Type}
    [Fintype V] [Fintype E] {G : CopiedGraph V E} (D : Drawing G)
    (A : Finset E) (e : E) (he : e ∉ A)
    (h : G.reaches A (G.left e) (G.right e)) :
    ∃ p : Path (D.point (G.left e)) (D.point (G.right e)),
      range p ⊆ D.trace Set.univ A ∧
      range p ∩ range (D.curve e) ⊆ {D.point (G.left e), D.point (G.right e)} := by
  obtain ⟨p, hp⟩ := D.exists_path_of_reaches A h
  exact ⟨p, hp, (inter_subset_inter_left _ hp).trans (D.trace_inter_omitted_edge A e he)⟩

end FiniteAvalanches.Electrical.StatementGeometry
