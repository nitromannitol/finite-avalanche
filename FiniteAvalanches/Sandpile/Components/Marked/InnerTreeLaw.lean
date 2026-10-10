import FiniteAvalanches.Probability.UniformMap
import FiniteAvalanches.Sandpile.Components.Marked.ContactEvents

/-! Literal restriction/lifting preserves every original copied edge and is a
proved equivalence. Its full uniform-law transport is independent of marks
and of any wave transition; positive actual tree counts form the carriers. -/
namespace FiniteAvalanches.Sandpile.Components.Marked
open FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

theorem inner_induced_tree_law {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (ho : o ∈ S) (C : PositiveCoreShape o S) :
    letI : Nonempty (InnerTrees C.val) := Fintype.card_pos_iff.mp C.property.2.1
    letI : Nonempty (inducedGraph (insideSupport C.val)).SpanningTree :=
      Nonempty.map (innerInducedTreeEquiv C.val).symm inferInstance
    ((inducedGraph (insideSupport C.val)).treeLaw).map (innerInducedTreeEquiv C.val) =
      (WiredTrees.graph N).componentLaw (positiveSupportEquiv S ho C) := by
  letI : Nonempty (InnerTrees C.val) := Fintype.card_pos_iff.mp C.property.2.1
  letI : Nonempty (inducedGraph (insideSupport C.val)).SpanningTree :=
    Nonempty.map (innerInducedTreeEquiv C.val).symm inferInstance
  change (FiniteAvalanches.uniformMeasure _).map (innerInducedTreeEquiv C.val) =
    FiniteAvalanches.uniformMeasure _
  exact FiniteAvalanches.uniform_measure_map_equiv (innerInducedTreeEquiv C.val)

end
end FiniteAvalanches.Sandpile.Components.Marked
