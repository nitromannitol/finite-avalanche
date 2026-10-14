import FiniteAvalanches.Paper.Current.RawRecurrentOriginalTrees

/-! The law of held burning on recurrent integer sandpiles. -/

open FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Paper.CurrentRawBurning

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanchesCurrent.HeldBurning

/-- Burning a uniform recurrent integer sandpile while holding vertices unburned
has the law of their pasts in a uniform spanning tree oriented toward the sink. -/
theorem held_burning {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (G : FiniteAvalanches.Trees.Multigraph V E)
    (s : V) (hconn : ∀ x y : V, G.reaches Finset.univ x y)
    (B : Finset (Burning.SourceVertex s)) [MeasurableSpace (Finset V)] :
    Measure.map (fun η : RawGraph.RecurrentState G s =>
      (RawGraph.sourceHeldBurning G s η.val B).image Subtype.val)
      (sourceRecurrentLaw G s hconn) =
      Measure.map (fun t : G.SpanningTree => sourcePastUnion G s t B)
        (sourceTreeLaw G s hconn) := by
  exact source_recurrent_held_past_law G s hconn B

end FiniteAvalanchesCurrent.HeldBurning
