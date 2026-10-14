import FiniteAvalanches.Sandpile.Recurrence.RawGraphLaw
import FiniteAvalanches.Trees.CertificateLaw

/-! Certificate-only transport from the internally chosen auxiliary edge order
back to the consumer's original edge equality. Every E copy remains identical. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open FiniteAvalanches.Trees
open MeasureTheory
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [LinearOrder E]
    (G : Multigraph V E) (s : V)

noncomputable abbrev sourceEdgeEquality : DecidableEq E :=
  @LinearOrder.toDecidableEq E (chosenEdgeOrder (E := E))

abbrev SourceTree := @Multigraph.SpanningTree V E _ _ (sourceEdgeEquality (E := E))
  (Burning.copiedTreeGraph G)

def originalTreeEquiv : SourceTree G ≃ (Burning.copiedTreeGraph G).SpanningTree :=
  (Burning.copiedTreeGraph G).spanningTreeDecidableEquiv (sourceEdgeEquality (E := E)) inferInstance

omit [DecidableEq V] in
theorem original_tree_equiv_edges (t : SourceTree G) : (originalTreeEquiv G t).val = t.val := rfl

abbrev originalTreeNonempty (hc : Connected G) : Nonempty (Burning.copiedTreeGraph G).SpanningTree :=
  Nonempty.map (originalTreeEquiv G) (treeNonempty G s hc)

def originalTreeLaw (hc : Connected G) : Measure (Burning.copiedTreeGraph G).SpanningTree := by
  letI := originalTreeNonempty G s hc
  exact (Burning.copiedTreeGraph G).treeLaw

theorem original_tree_law_transport (hc : Connected G) :
    Measure.map (originalTreeEquiv G) (copiedTreeLaw G s hc) = originalTreeLaw G s hc := by
  letI := treeNonempty G s hc
  letI := originalTreeNonempty G s hc
  exact FiniteAvalanches.uniform_measure_map_equiv (originalTreeEquiv G)

/-- Past membership does not depend on equality certificates or auxiliary edge sorting. -/
theorem original_tree_past_transport (B : Finset (Burning.SourceVertex s)) (t : SourceTree G) :
    Burning.treePastUnion G s (originalTreeEquiv G t) B =
      @Burning.treePastUnion V E _ _ _ (chosenEdgeOrder (E := E)) G s t B := by
  ext x
  rw [Burning.mem_tree_past_union,
    @Burning.mem_tree_past_union V E _ _ _ (chosenEdgeOrder (E := E)) G s t B x]
  rfl

/-- Source held law at the actual consumer tree carrier, after proved certificate transport. -/
theorem recurrent_original_held_past_law (hc : Connected G)
    (B : Finset (Burning.SourceVertex s)) [MeasurableSpace (Finset V)] :
    Measure.map (fun η : RecurrentState G s => (heldStop G s B η).image Subtype.val)
      (recurrentLaw G s hc) =
      Measure.map (fun t : (Burning.copiedTreeGraph G).SpanningTree => Burning.treePastUnion G s t B)
        (originalTreeLaw G s hc) := by
  have hm : Measure.map
      (fun t : (Burning.copiedTreeGraph G).SpanningTree => Burning.treePastUnion G s t B)
        (originalTreeLaw G s hc) =
      Measure.map (fun t : SourceTree G =>
        @Burning.treePastUnion V E _ _ _ (chosenEdgeOrder (E := E)) G s t B)
        (copiedTreeLaw G s hc) := by
    rw [← original_tree_law_transport G s hc,
      Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    congr 1
    funext t
    exact original_tree_past_transport G s B t
  exact (recurrent_held_past_law G s hc B).trans hm.symm

end
end FiniteAvalanches.Sandpile.RawGraph
