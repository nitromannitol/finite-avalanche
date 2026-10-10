import FiniteAvalanches.Sandpile.Components.SourceFields
import FiniteAvalanches.Trees.Induced
import FiniteAvalanches.Sandpile.Burning.CanonicalEquiv
import FiniteAvalanches.Sandpile.Components.Properties

/-! Apply the proved global burning bijection and actual edge-subset transport
on the two original copied induced components. Every component shape is retained. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

def innerInducedTreeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    (inducedGraph (insideSupport C)).SpanningTree ≃ InnerTrees C :=
  (WiredTrees.graph N).restrictedTreeEquiv (insideSupport C)

def outerInducedTreeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    (inducedGraph (outsideSupport C)).SpanningTree ≃ OuterTrees C :=
  (WiredTrees.graph N).restrictedTreeEquiv (outsideSupport C)

theorem inner_induced_tree_edges {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (t : (inducedGraph (insideSupport C)).SpanningTree) :
    (innerInducedTreeEquiv C t).val = t.val.image Subtype.val := rfl

theorem outer_induced_tree_edges {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (t : (inducedGraph (outsideSupport C)).SpanningTree) :
    (outerInducedTreeEquiv C t).val = t.val.image Subtype.val := rfl

def innerGraphTreeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    InnerGraphAllowed C ≃ InnerTrees C := by
  let dE : DecidableEq (InducedEdge (insideSupport C)) := inferInstance
  letI : LinearOrder (InducedEdge (insideSupport C)) :=
    LinearOrder.lift' (Fintype.equivFin (InducedEdge (insideSupport C)))
      (Fintype.equivFin (InducedEdge (insideSupport C))).injective
  exact (Burning.canonicalBurningEquiv (dE := dE) (inducedGraph (insideSupport C)) (innerRoot C)).trans
    (innerInducedTreeEquiv C)

def outerGraphTreeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    OuterGraphAllowed C ≃ OuterTrees C := by
  let dE : DecidableEq (InducedEdge (outsideSupport C)) := inferInstance
  letI : LinearOrder (InducedEdge (outsideSupport C)) :=
    LinearOrder.lift' (Fintype.equivFin (InducedEdge (outsideSupport C)))
      (Fintype.equivFin (InducedEdge (outsideSupport C))).injective
  exact (Burning.canonicalBurningEquiv (dE := dE) (inducedGraph (outsideSupport C)) (outerRoot C)).trans
    (outerInducedTreeEquiv C)

def innerAllowedTreeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    InnerAllowed o C ≃ InnerTrees C :=
  (innerAllowedSourceEquiv C).trans (innerGraphTreeEquiv C)

def outerAllowedTreeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    OuterAllowed C ≃ OuterTrees C :=
  (outerAllowedSourceEquiv C).trans (outerGraphTreeEquiv C)

/-- Complete complement-first core product on the original E-subset tree carriers. -/
def coreTreeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    CoreField o C.val ≃ OuterTrees C × InnerTrees C :=
  (coreGraphFieldEquiv C).trans (Equiv.prodCongr (outerGraphTreeEquiv C) (innerGraphTreeEquiv C))

theorem card_core_tree_product {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Nat.card (CoreField o C.val) = Nat.card (OuterTrees C) * Nat.card (InnerTrees C) := by
  rw [Nat.card_congr (coreTreeEquiv C), Nat.card_prod]

end
end FiniteAvalanches.Sandpile.Components
