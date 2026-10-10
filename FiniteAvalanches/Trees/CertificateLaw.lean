import FiniteAvalanches.Probability.UniformMap
import FiniteAvalanches.Sandpile.Burning.CanonicalEquiv

/-! The canonical certificate-only equivalence retains every edge copy. Its
connecting span is unchanged, and its entire uniform measure transports. -/
namespace FiniteAvalanches.Trees.Multigraph
open MeasureTheory
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E]

theorem spanning_tree_decidable_equiv_span (G : Multigraph V E) (d f : DecidableEq E)
    (t : @SpanningTree V E _ _ d G) (S : Set V) :
    @span V E _ _ f G (G.spanningTreeDecidableEquiv d f t) S =
      @span V E _ _ d G t S := rfl

theorem tree_law_map_spanning_tree_decidable_equiv (G : Multigraph V E) (d f : DecidableEq E)
    [nd : Nonempty (@SpanningTree V E _ _ d G)]
    [nf : Nonempty (@SpanningTree V E _ _ f G)] :
    (@treeLaw V E _ _ d G nd).map (G.spanningTreeDecidableEquiv d f) =
      @treeLaw V E _ _ f G nf :=
  FiniteAvalanches.uniform_measure_map_equiv (G.spanningTreeDecidableEquiv d f)

end
end FiniteAvalanches.Trees.Multigraph
