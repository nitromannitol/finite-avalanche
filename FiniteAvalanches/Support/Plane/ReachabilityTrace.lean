import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import Mathlib.Topology.Order.Compact

/-!
# Drawing traces of graph components

The edges of a copied graph stay within its reachability components. A finite
drawing therefore splits into disjoint compact traces for a component and its
complement.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

/-- Vertices reachable from a root using the selected copied edges. -/
def reachableVertices (G : CopiedGraph V E) (A : Finset E) (root : V) : Set V :=
  {v | G.reaches A root v}

/-- Selected edges whose endpoints belong to the root component. -/
noncomputable def reachableEdges (G : CopiedGraph V E) (A : Finset E) (root : V) : Finset E :=
  A.filter fun e => G.left e ∈ reachableVertices G A root

omit [Fintype V] [Fintype E] in
/-- A selected edge has either both endpoints in a reachable component or neither. -/
theorem reachableVertices_edge_iff (G : CopiedGraph V E) (A : Finset E) (root : V)
    (e : E) (he : e ∈ A) :
    G.left e ∈ reachableVertices G A root ↔ G.right e ∈ reachableVertices G A root := by
  constructor
  · intro h
    exact h.tail ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · intro h
    exact h.tail ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩

/-- The trace of finitely many vertices and copied edge curves is compact. -/
theorem Drawing.trace_isCompact {G : CopiedGraph V E} (D : Drawing G)
    (C : Set V) (A : Finset E) : IsCompact (D.trace C A) := by
  have hpoints : IsCompact (D.point '' C) := (Set.toFinite C).image D.point |>.isCompact
  have hedges : IsCompact {z | ∃ e ∈ A, ∃ t, D.curve e t = z} := by
    have heq : {z | ∃ e ∈ A, ∃ t, D.curve e t = z} =
        ⋃ e ∈ A, range (D.curve e) := by
      ext z
      simp only [mem_setOf_eq, mem_iUnion, mem_range]
      constructor
      · rintro ⟨e, he, t, ht⟩
        exact ⟨e, he, t, ht⟩
      · rintro ⟨e, he, t, ht⟩
        exact ⟨e, he, t, ht⟩
    rw [heq]
    exact A.isCompact_biUnion fun e _ => isCompact_range (D.continuous e)
  exact hpoints.union hedges

/-- The trace of a selected drawing is the union of the traces of a reachable
vertex component and its complement. -/
theorem Drawing.trace_reachable_partition {G : CopiedGraph V E} (D : Drawing G)
    (A : Finset E) (root : V) :
    D.trace Set.univ A =
      D.trace (reachableVertices G A root) (reachableEdges G A root) ∪
        D.trace (reachableVertices G A root)ᶜ (A \ reachableEdges G A root) := by
  ext z
  constructor
  · rintro (⟨v, _, rfl⟩ | ⟨e, he, t, rfl⟩)
    · by_cases hv : v ∈ reachableVertices G A root
      · exact Or.inl (Or.inl ⟨v, hv, rfl⟩)
      · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
    · by_cases hleft : G.left e ∈ reachableVertices G A root
      · exact Or.inl (Or.inr ⟨e, Finset.mem_filter.mpr ⟨he, hleft⟩, t, rfl⟩)
      · exact Or.inr (Or.inr ⟨e, Finset.mem_sdiff.mpr
          ⟨he, fun h => hleft (Finset.mem_filter.mp h).2⟩, t, rfl⟩)
  · rintro ((⟨v, hv, rfl⟩ | ⟨e, he, t, rfl⟩) | (⟨v, hv, rfl⟩ | ⟨e, he, t, rfl⟩))
    · exact Or.inl ⟨v, mem_univ v, rfl⟩
    · exact Or.inr ⟨e, (Finset.mem_filter.mp he).1, t, rfl⟩
    · exact Or.inl ⟨v, mem_univ v, rfl⟩
    · exact Or.inr ⟨e, (Finset.mem_sdiff.mp he).1, t, rfl⟩

/-- Reachability-component traces in a proper drawing are disjoint. -/
theorem Drawing.disjoint_reachable_traces {G : CopiedGraph V E} (D : Drawing G)
    (A : Finset E) (root : V) :
    Disjoint (D.trace (reachableVertices G A root) (reachableEdges G A root))
      (D.trace (reachableVertices G A root)ᶜ (A \ reachableEdges G A root)) := by
  apply D.traces_disjoint disjoint_compl_right
  · intro e he
    have h := Finset.mem_filter.mp he
    exact ⟨h.2, (reachableVertices_edge_iff G A root e h.1).mp h.2⟩
  · intro e he
    have h := Finset.mem_sdiff.mp he
    have hl : G.left e ∉ reachableVertices G A root := by
      intro hl
      exact h.2 (Finset.mem_filter.mpr ⟨h.1, hl⟩)
    exact ⟨hl, fun hr => hl ((reachableVertices_edge_iff G A root e h.1).mpr hr)⟩

end FiniteAvalanches.Electrical.StatementGeometry
