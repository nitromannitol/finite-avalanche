import FiniteAvalanches.Trees.PathCopies

/-! A source-to-root path copy has exactly one genuine rootward tail.
Every statement retains the individual copy and its literal deletion component. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Trees.Multigraph.CurrentCopyTail
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
variable (G : Multigraph V E)

/-- The inside endpoint of an actual separating copy is its unique tail. -/
theorem existsUnique_tail (t : G.SpanningTree) (o r : V) (e : E)
    (he : e ∈ G.rootPathCopies t o r) :
    ∃! x : V, x ∈ G.componentAfter t.val e o ∧ (G.left e = x ∨ G.right e = x) := by
  have hp := (G.mem_rootPathCopies t o r e).mp he
  have hc := G.cut_components_at_source t e hp.1 o
  rcases hc.2.1 with hc | hc
  · refine ⟨G.left e, ⟨hc.1, Or.inl rfl⟩, ?_⟩
    rintro y ⟨hy, hyl | hyr⟩
    · exact hyl.symm
    · exact (hc.2 (hyr.symm ▸ hy)).elim
  · refine ⟨G.right e, ⟨hc.2, Or.inr rfl⟩, ?_⟩
    rintro y ⟨hy, hyl | hyr⟩
    · exact (hc.1 (hyl.symm ▸ hy)).elim
    · exact hyr.symm

/-- Actual cut geometry identifies the same tail's complete root-oriented past. -/
theorem past_eq_source_component (t : G.SpanningTree) (o r : V) (e : E)
    (he : e ∈ G.rootPathCopies t o r) (x : V)
    (hx : x ∈ G.componentAfter t.val e o) (hxe : G.left e = x ∨ G.right e = x)
    (hxr : x ≠ r) : G.past t r x hxr = G.componentAfter t.val e o := by
  have hp := (G.mem_rootPathCopies t o r e).mp he
  have hc := G.cut_components_at_source t e hp.1 o
  rw [G.past_eq_descendants]
  exact G.descendants_eq_cut ⟨(t.val, e), t.property, hc⟩ r x hp.2 hx hxe

/-- It is that actual tail's parent COPY, not merely the same unordered endpoints. -/
theorem copy_eq_parent (t : G.SpanningTree) (o r : V) (e : E)
    (he : e ∈ G.rootPathCopies t o r) (x : V)
    (hx : x ∈ G.componentAfter t.val e o) (hxe : G.left e = x ∨ G.right e = x)
    (hxr : x ≠ r) : e = G.parentEdge t r x hxr := by
  have hp := (G.mem_rootPathCopies t o r e).mp he
  have hc := G.cut_components_at_source t e hp.1 o
  have hpar := G.parentEdge_spec t r x hxr
  have hpc := G.cut_components_at_source t (G.parentEdge t r x hxr) hpar.1 x
  have hpast := past_eq_source_component G t o r e he x hx hxe hxr
  have hcross : G.crosses (G.componentAfter t.val e o) (G.parentEdge t r x hxr) := by
    rw [← hpast]
    exact hpc.2.1
  by_contra hne
  have hside := hc.2.2.1 _ (Finset.mem_erase.mpr ⟨Ne.symm hne, hpar.1⟩)
  rcases hcross with hcross | hcross
  · exact hcross.2 (hside.mp hcross.1)
  · exact hcross.1 (hside.mpr hcross.2)

/-- Different qualifying copies cannot leave the same actual tail. -/
theorem copies_eq_of_same_tail (t : G.SpanningTree) (o r : V) (e f : E)
    (he : e ∈ G.rootPathCopies t o r) (hf : f ∈ G.rootPathCopies t o r) (x : V)
    (heX : x ∈ G.componentAfter t.val e o ∧ (G.left e = x ∨ G.right e = x))
    (hfX : x ∈ G.componentAfter t.val f o ∧ (G.left f = x ∨ G.right f = x))
    (hxr : x ≠ r) : e = f := by
  exact (copy_eq_parent G t o r e he x heX.1 heX.2 hxr).trans
    (copy_eq_parent G t o r f hf x hfX.1 hfX.2 hxr).symm

end
end FiniteAvalanches.Trees.Multigraph.CurrentCopyTail

#print FiniteAvalanches.Trees.Multigraph.CurrentCopyTail.existsUnique_tail
#print axioms FiniteAvalanches.Trees.Multigraph.CurrentCopyTail.existsUnique_tail
#print FiniteAvalanches.Trees.Multigraph.CurrentCopyTail.past_eq_source_component
#print axioms FiniteAvalanches.Trees.Multigraph.CurrentCopyTail.past_eq_source_component
#print FiniteAvalanches.Trees.Multigraph.CurrentCopyTail.copy_eq_parent
#print axioms FiniteAvalanches.Trees.Multigraph.CurrentCopyTail.copy_eq_parent
#print FiniteAvalanches.Trees.Multigraph.CurrentCopyTail.copies_eq_of_same_tail
#print axioms FiniteAvalanches.Trees.Multigraph.CurrentCopyTail.copies_eq_of_same_tail
