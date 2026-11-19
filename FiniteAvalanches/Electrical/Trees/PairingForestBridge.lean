import FiniteAvalanches.Electrical.Trees.PairingGroves
import LatticeProb.Graph.CopiedGraph.PairingForest

/-! Pairing groves are rooted copied forests with a prescribed terminal matching. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph

open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]

/-- The two copied-graph presentations retain the same edge carrier and endpoints. -/
def latticeProbGraph (J : CopiedGraph V E) : LatticeProb.Graph.CopiedGraph V E :=
  ⟨J.left, J.right⟩

/-- A pairing grove is exactly a forest rooted at the first terminal list with
the prescribed pairing; all original edge copies, including loops, are retained. -/
def pairingGroveEquivRootedMatching (J : CopiedGraph V E) {k : ℕ}
    (a b : Fin k → V) (ha : Function.Injective a) (π : Equiv.Perm (Fin k)) :
    J.PairingGrove a b π ≃
      {F : Finset E // (J.latticeProbGraph.IsRootedForest (Set.range a) F) ∧
        ∀ r, J.latticeProbGraph.reaches F (a r) (b (π r))} :=
  Equiv.subtypeEquivRight fun F => by
    change (J.latticeProbGraph.IsForest F ∧
      (∀ x, ∃ r, J.latticeProbGraph.reaches F x (a r) ∨
        J.latticeProbGraph.reaches F x (b r)) ∧
      (∀ r s, J.latticeProbGraph.reaches F (a r) (b s) ↔ s = π r) ∧
      (∀ r s, r ≠ s → ¬J.latticeProbGraph.reaches F (a r) (a s))) ↔ _
    exact (J.latticeProbGraph.isRootedForest_range_and_matching_iff a b ha π F).symm

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
