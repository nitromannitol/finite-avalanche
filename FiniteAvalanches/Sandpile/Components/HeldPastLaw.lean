import FiniteAvalanches.Sandpile.Components.Conditioning
import FiniteAvalanches.Sandpile.Burning.PastAdapter

/-! Apply the proved held-past law on the actual induced core graph, after
conditioning only on the core shape. No transition event occurs in the carrier,
conditioning event, or observable. All original wired edge IDs remain subtypes. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

instance innerVertexShapeMeasurableSpace {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) : MeasurableSpace (Finset (insideSupport C)) := ⊤

theorem inner_tree_nonempty_of_core {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [Nonempty (CoreField o C.val)]
    [LinearOrder (InducedEdge (insideSupport C))] :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    Nonempty (inducedGraph (insideSupport C)).SpanningTree := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  change Nonempty (Burning.copiedTreeGraph
    (Burning.originalGraph (inducedGraph (insideSupport C)))).SpanningTree
  have hf : Nonempty (Burning.AllowedField
      (Burning.originalGraph (inducedGraph (insideSupport C))) (innerRoot C)) := by
    change Nonempty (InnerGraphAllowed C)
    infer_instance
  exact hf.map (fun h => Burning.burningEquiv
    (Burning.originalGraph (inducedGraph (insideSupport C))) (innerRoot C) h)

/-- Under the actual shape-only conditional fiber, the held unburnt set has the
law of the union of actual pasts in a uniform original-copy induced-core tree. -/
theorem core_shape_held_past_law {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) [Nonempty (CoreField o C.val)]
    [LinearOrder (InducedEdge (insideSupport C))]
    (B : Finset (Burning.SourceVertex (innerRoot C))) :
    letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
    letI : Nonempty (inducedGraph (insideSupport C)).SpanningTree := inner_tree_nonempty_of_core C
    Measure.map (fun h : CoreField o C.val =>
      (Burning.heldBurning (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C))
        (coreGraphFieldEquiv C h).2.val B).image Subtype.val)
      (FiniteAvalanches.uniformMeasure (CoreField o C.val)) =
      Measure.map (fun t : (inducedGraph (insideSupport C)).SpanningTree =>
        Burning.canonicalPastUnion (inducedGraph (insideSupport C)) (innerRoot C) t B)
        (inducedGraph (insideSupport C)).treeLaw := by
  letI : DecidableEq (InducedEdge (insideSupport C)) := LinearOrder.toDecidableEq
  letI := inner_tree_nonempty_of_core C
  have h := congrArg (Measure.map (fun r : InnerGraphAllowed C =>
    (Burning.heldBurning (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C))
      r.val B).image Subtype.val)) (core_shape_inner_uniform C)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at h
  exact h.trans (Burning.canonical_uniform_held_past_law
    (inducedGraph (insideSupport C)) (innerRoot C) B)

end
end FiniteAvalanches.Sandpile.Components
