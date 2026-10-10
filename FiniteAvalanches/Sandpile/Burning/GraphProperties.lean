module

public import FiniteAvalanches.Sandpile.Burning.GraphFields

@[expose] public section

/-! Pointwise consumers verify the graph-indexed maps: unchanged inner heights,
exact outer shift, and reconstruction with the actual operational stopping set. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (s : V)

theorem held_graph_field_equiv_inside (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (h : HeldFiber G (Finset.univ.erase s) B A) (x : InsideVertex s A) :
    ((heldGraphFieldEquiv G s B A hBA h).2.val (heldVertexEquiv s A x)).val = (h.val x.val).val := by
  change (insideHeightsGraphEquiv G s B A hBA (splitField G (Finset.univ.erase s) B A hBA h).1.val
    (heldVertexEquiv s A x)).val = _
  unfold insideHeightsGraphEquiv
  rw [reindex_heights_val]
  rfl

theorem held_graph_field_equiv_outside (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (h : HeldFiber G (Finset.univ.erase s) B A) (x : OutsideVertex s A) :
    ((heldGraphFieldEquiv G s B A hBA h).1.val (outsideVertexEquiv s A x)).val =
      (h.val x.val).val - activeDegree G (Finset.univ.erase s) A x.val := by
  change (outsideHeightsGraphEquiv G s A (splitField G (Finset.univ.erase s) B A hBA h).2.val
    (outsideVertexEquiv s A x)).val = _
  unfold outsideHeightsGraphEquiv
  rw [reindex_heights_val]
  rfl

theorem held_graph_field_reconstruct_stops (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (d : {d : SourceHeights (complementGraph G s A) (complementSink s A) //
      noForbidden (complementGraph G s A) (Finset.univ.erase (complementSink s A)) d})
    (a : {a : SourceHeights (sourceHeldGraph G s B A hBA) none //
      noForbidden (sourceHeldGraph G s B A hBA) (Finset.univ.erase none) a}) :
    heldBurning G (Finset.univ.erase s) ((heldGraphFieldEquiv G s B A hBA).symm (d, a)).val B = A :=
  ((heldGraphFieldEquiv G s B A hBA).symm (d, a)).property.2

theorem held_graph_field_reconstruct_no_forbidden (B A : Finset (SourceVertex s)) (hBA : B ⊆ A)
    (d : {d : SourceHeights (complementGraph G s A) (complementSink s A) //
      noForbidden (complementGraph G s A) (Finset.univ.erase (complementSink s A)) d})
    (a : {a : SourceHeights (sourceHeldGraph G s B A hBA) none //
      noForbidden (sourceHeldGraph G s B A hBA) (Finset.univ.erase none) a}) :
    noForbidden G (Finset.univ.erase s) ((heldGraphFieldEquiv G s B A hBA).symm (d, a)).val :=
  ((heldGraphFieldEquiv G s B A hBA).symm (d, a)).property.1

end
end FiniteAvalanches.Sandpile.Burning
