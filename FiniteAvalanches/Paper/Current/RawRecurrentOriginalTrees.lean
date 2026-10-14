import FiniteAvalanches.Paper.Current.RawRecurrentHeld

/-! Source laws at the original caller's E equality. Finite edge ordering is
chosen internally; both certificate transports keep each actual edge subset. -/
namespace FiniteAvalanches.Paper.CurrentRawBurning
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees MeasureTheory
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [dE : DecidableEq E]
    (G : Multigraph V E) (s : V)

def sourceTreeEquiv : RawGraph.SourceTree G ≃ G.SpanningTree := by
  letI : LinearOrder E := RawGraph.chosenEdgeOrder (E := E)
  exact (RawGraph.originalTreeEquiv G).trans
    ((Burning.copiedTreeGraph G).spanningTreeDecidableEquiv
      (@LinearOrder.toDecidableEq E (RawGraph.chosenEdgeOrder (E := E))) dE)

omit [DecidableEq V] in
theorem source_tree_equiv_edges (t : RawGraph.SourceTree G) :
    (sourceTreeEquiv G t).val = t.val := rfl

abbrev sourceTreePopulation (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    Nonempty G.SpanningTree :=
  Nonempty.map (sourceTreeEquiv G)
    (RawGraph.treeNonempty G s ((connected_iff_reaches G).mpr hconn))

def sourceTreeLaw (hconn : ∀ x y : V, G.reaches Finset.univ x y) : Measure G.SpanningTree := by
  letI := sourceTreePopulation G s hconn
  exact G.treeLaw

theorem source_tree_law_transport (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    Measure.map (sourceTreeEquiv G)
      (RawGraph.copiedTreeLaw G s ((connected_iff_reaches G).mpr hconn)) =
      sourceTreeLaw G s hconn := by
  letI : LinearOrder E := RawGraph.chosenEdgeOrder (E := E)
  let hc := (connected_iff_reaches G).mpr hconn
  letI := RawGraph.treeNonempty G s hc
  letI := RawGraph.originalTreeNonempty G s hc
  letI := sourceTreePopulation G s hconn
  letI : Nonempty (@Multigraph.SpanningTree V E _ _ dE (Burning.copiedTreeGraph G)) :=
    sourceTreePopulation G s hconn
  let e2 := (Burning.copiedTreeGraph G).spanningTreeDecidableEquiv
    (@LinearOrder.toDecidableEq E (RawGraph.chosenEdgeOrder (E := E))) dE
  have hm := congrArg (Measure.map e2) (RawGraph.original_tree_law_transport G s hc)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at hm
  have hf : Measure.map e2 (RawGraph.originalTreeLaw G s hc) =
      @Multigraph.treeLaw V E _ _ dE (Burning.copiedTreeGraph G)
        (sourceTreePopulation G s hconn) :=
    (Burning.copiedTreeGraph G).tree_law_map_spanning_tree_decidable_equiv
      (@LinearOrder.toDecidableEq E (RawGraph.chosenEdgeOrder (E := E))) dE
  exact hm.trans hf

/-- Literal union of the pasts of held vertices toward the original sink. -/
def sourcePastUnion (t : G.SpanningTree) (B : Finset (Burning.SourceVertex s)) : Finset V :=
  Finset.univ.filter fun x => ∃ b ∈ B,
    x ∈ G.past t s b.val (Burning.source_vertex_ne_sink s b)

theorem source_past_mem (t : G.SpanningTree) (B : Finset (Burning.SourceVertex s)) (x : V) :
    x ∈ sourcePastUnion G s t B ↔ ∃ b ∈ B,
      x ∈ G.past t s b.val (Burning.source_vertex_ne_sink s b) := by
  simp only [sourcePastUnion, Finset.mem_filter, Finset.mem_univ, true_and]

theorem source_past_characterization (t : G.SpanningTree)
    (B : Finset (Burning.SourceVertex s)) (A : Finset V) :
    sourcePastUnion G s t B = A ↔ ∀ x,
      x ∈ A ↔ ∃ b ∈ B, x ∈ G.past t s b.val (Burning.source_vertex_ne_sink s b) := by
  constructor
  · rintro rfl
    exact source_past_mem G s t B
  · intro h
    ext x
    exact (source_past_mem G s t B x).trans (h x).symm

theorem source_past_transport (B : Finset (Burning.SourceVertex s)) (t : RawGraph.SourceTree G) :
    sourcePastUnion G s (sourceTreeEquiv G t) B =
      @Burning.treePastUnion V E _ _ _ (RawGraph.chosenEdgeOrder (E := E)) G s t B := by
  letI : LinearOrder E := RawGraph.chosenEdgeOrder (E := E)
  have he : sourcePastUnion G s (sourceTreeEquiv G t) B =
      Burning.treePastUnion G s (RawGraph.originalTreeEquiv G t) B := by
    ext x
    rw [source_past_mem, Burning.mem_tree_past_union]
    simp only [Multigraph.past_eq_descendants, Multigraph.descendants, Set.mem_setOf_eq]
    rfl
  exact he.trans (RawGraph.original_tree_past_transport G s B t)

theorem source_recurrent_count (hconn : ∀ x y : V, G.reaches Finset.univ x y) :
    Nat.card (RawGraph.RecurrentState G s) = Nat.card G.SpanningTree :=
  (RawGraph.card_recurrent_eq_trees G s ((connected_iff_reaches G).mpr hconn)).trans
    (Nat.card_congr (sourceTreeEquiv G))

/-- Actual accessibility recurrence and the literal stable-integer parallel endpoint.
The only mathematical input is source connectedness, never a distribution or criterion. -/
theorem source_recurrent_held_past_law
    (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (B : Finset (Burning.SourceVertex s)) [MeasurableSpace (Finset V)] :
    Measure.map (fun η : RawGraph.RecurrentState G s =>
      (RawGraph.sourceHeldBurning G s η.val B).image Subtype.val)
      (sourceRecurrentLaw G s hconn) =
      Measure.map (fun t : G.SpanningTree => sourcePastUnion G s t B) (sourceTreeLaw G s hconn) := by
  letI : LinearOrder E := RawGraph.chosenEdgeOrder (E := E)
  let hc := (connected_iff_reaches G).mpr hconn
  have he : (fun η : RawGraph.RecurrentState G s =>
      (RawGraph.sourceHeldBurning G s η.val B).image Subtype.val) =
      (fun η : RawGraph.RecurrentState G s => (RawGraph.heldStop G s B η).image Subtype.val) := by
    funext η
    exact congrArg (fun A => A.image Subtype.val) (source_stop_of_recurrent G s η B)
  rw [he]
  have hm : Measure.map (fun t : G.SpanningTree => sourcePastUnion G s t B)
      (sourceTreeLaw G s hconn) =
      Measure.map (fun t : RawGraph.SourceTree G =>
        @Burning.treePastUnion V E _ _ _ (RawGraph.chosenEdgeOrder (E := E)) G s t B)
        (RawGraph.copiedTreeLaw G s hc) := by
    rw [← source_tree_law_transport G s hconn,
      Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    congr 1
    funext t
    exact source_past_transport G s B t
  exact (RawGraph.recurrent_held_past_law G s hc B).trans hm.symm

end
end FiniteAvalanches.Paper.CurrentRawBurning
