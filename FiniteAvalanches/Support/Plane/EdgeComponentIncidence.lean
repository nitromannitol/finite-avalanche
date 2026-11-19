import FiniteAvalanches.Support.Plane.ReachabilityTrace

/-!
# Edges joining distinct graph components

An omitted edge whose endpoints lie in distinct reachability components meets
the two component traces only at its respective endpoints.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical

/-- An omitted edge joining distinct selected-edge components meets their two
traces only at its corresponding endpoints. -/
theorem Drawing.edge_inter_reachable_traces {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (A : Finset E) (e : E)
    (he : e ∉ A) (hnot : ¬ G.reaches A (G.left e) (G.right e)) :
    range (D.curve e) ∩
        D.trace (reachableVertices G A (G.left e)) (reachableEdges G A (G.left e)) ⊆
      {D.point (G.left e)} ∧
    range (D.curve e) ∩
        D.trace (reachableVertices G A (G.left e))ᶜ (A \ reachableEdges G A (G.left e)) ⊆
      {D.point (G.right e)} := by
  let C := reachableVertices G A (G.left e)
  let S := reachableEdges G A (G.left e)
  have hleft : G.left e ∈ C := Relation.ReflTransGen.refl
  have hright : G.right e ∉ C := hnot
  have hS : ∀ f ∈ S, G.left f ∈ C ∧ G.right f ∈ C := by
    intro f hf
    have hh := Finset.mem_filter.mp hf
    exact ⟨hh.2, (reachableVertices_edge_iff G A (G.left e) f hh.1).mp hh.2⟩
  have hT : ∀ f ∈ A \ S, G.left f ∈ Cᶜ ∧ G.right f ∈ Cᶜ := by
    intro f hf
    have hh := Finset.mem_sdiff.mp hf
    have hl : G.left f ∉ C := fun h => hh.2 (Finset.mem_filter.mpr ⟨hh.1, h⟩)
    exact ⟨hl, fun h => hl ((reachableVertices_edge_iff G A (G.left e) f hh.1).mpr h)⟩
  have hpoints (f : E) (hf : f ∈ A) (t s : ArcParameter)
      (h : D.curve e t = D.curve f s) : t.val = 0 ∨ t.val = 1 := by
    have hef : e ≠ f := fun h => he (h ▸ hf)
    exact (D.intersects e f hef t s h).1
  constructor
  · rintro z ⟨⟨t, ht⟩, hz⟩
    rcases hz with ⟨v, hv, hp⟩ | ⟨f, hf, s, hs⟩
    · rcases (D.curve_vertex_iff e t v).mp (ht.trans hp.symm) with ⟨h0, hv'⟩ | ⟨h1, hv'⟩
      · have ht0 : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext h0
        rw [← ht, ht0, D.start]
        exact mem_singleton _
      · exact (hright (hv' ▸ hv)).elim
    · have hfA : f ∈ A := (Finset.mem_filter.mp hf).1
      rcases hpoints f hfA t s (ht.trans hs.symm) with h0 | h1
      · have ht0 : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext h0
        rw [← ht, ht0, D.start]
        exact mem_singleton _
      · have ht1 : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h1
        have hvertex : D.curve f s = D.point (G.right e) := by
          have hh := (ht.trans hs.symm).symm
          rw [ht1, D.finish] at hh
          exact hh
        exact (hright (D.curve_vertex_mem hS f hf s _ hvertex)).elim
  · rintro z ⟨⟨t, ht⟩, hz⟩
    rcases hz with ⟨v, hv, hp⟩ | ⟨f, hf, s, hs⟩
    · rcases (D.curve_vertex_iff e t v).mp (ht.trans hp.symm) with ⟨h0, hv'⟩ | ⟨h1, hv'⟩
      · exact (hv (hv' ▸ hleft)).elim
      · have ht1 : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h1
        rw [← ht, ht1, D.finish]
        exact mem_singleton _
    · have hfA : f ∈ A := (Finset.mem_sdiff.mp hf).1
      rcases hpoints f hfA t s (ht.trans hs.symm) with h0 | h1
      · have ht0 : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext h0
        have hvertex : D.curve f s = D.point (G.left e) := by
          have hh := (ht.trans hs.symm).symm
          rw [ht0, D.start] at hh
          exact hh
        exact ((D.curve_vertex_mem hT f hf s _ hvertex) hleft).elim
      · have ht1 : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h1
        rw [← ht, ht1, D.finish]
        exact mem_singleton _

end FiniteAvalanches.Electrical.StatementGeometry
