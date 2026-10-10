module

public import FiniteAvalanches.Sandpile.Burning.Fields
public import FiniteAvalanches.Sandpile.Burning.ForbiddenTransport

@[expose] public section

/-! Specialize the deterministic packet to one literal sink: every vertex other
than s is active and retains its original degree. Shapes are finite subsets of
that actual carrier. Their exclusion of s is derived, not added to a paper claim. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

abbrev SourceVertex := InducedVertex (Finset.univ.erase s)
abbrev SourceHeights := Heights G (Finset.univ.erase s)

theorem source_vertex_ne_sink (v : SourceVertex s) : v.val ≠ s :=
  (Finset.mem_erase.mp v.property).1

theorem source_shape_avoids_sink (A : Finset (SourceVertex s)) :
    s ∉ A.image Subtype.val := by
  intro hs
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hs
  exact source_vertex_ne_sink s v hv

theorem source_shape_subset (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    B.image Subtype.val ⊆ A.image Subtype.val := Finset.image_subset_image hBA

/-- The actual H_{A,B}: original copies, original held degrees, one contracted sink. -/
def sourceHeldGraph (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :=
  heldGraph G s (A.image Subtype.val) (B.image Subtype.val)
    (source_shape_avoids_sink s A) (source_shape_subset s B A hBA)

theorem source_held_degree (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (v : InducedVertex (A.image Subtype.val)) :
    degree (sourceHeldGraph G s B A hBA) (some v) =
      if v.val ∈ B.image Subtype.val then degree G v.val
      else degreeInto G (A.image Subtype.val) v.val :=
  degree_held_graph G s _ _ (source_shape_avoids_sink s A) (source_shape_subset s B A hBA) v

/-- Complete source-height carrier; no recurrent, tree, or probability law is inferred. -/
def sourceHeldFieldEquiv (B A : Finset (SourceVertex s)) (hBA : B ⊆ A) :
    {h : SourceHeights G s // noForbidden G (Finset.univ.erase s) h ∧
      heldBurning G (Finset.univ.erase s) h B = A} ≃
      ({a : InnerField G (Finset.univ.erase s) B A //
          InnerAllowed G (Finset.univ.erase s) B A a} ×
        {d : OuterField G (Finset.univ.erase s) A //
          OuterAllowed G (Finset.univ.erase s) A d}) :=
  heldFieldEquiv G (Finset.univ.erase s) B A hBA

/-- Empty held set burns every active vertex of every allowed stable field. -/
theorem source_empty_held (h : SourceHeights G s)
    (hn : noForbidden G (Finset.univ.erase s) h) :
    heldBurning G (Finset.univ.erase s) h ∅ = ∅ :=
  held_burning_empty_of_noForbidden G (Finset.univ.erase s) h hn

/-- A concrete operational stopping set supplies its own held inclusion. -/
def actualSourceHeldGraph (h : SourceHeights G s) (B : Finset (SourceVertex s)) :=
  sourceHeldGraph G s B (heldBurning G (Finset.univ.erase s) h B)
    (held_burning_largest G (Finset.univ.erase s) h B).1.1

end
end FiniteAvalanches.Sandpile.Burning
