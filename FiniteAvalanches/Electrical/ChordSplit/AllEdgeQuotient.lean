import FiniteAvalanches.Electrical.ChordSplit.CopiedDiagram
import FiniteAvalanches.Electrical.Trees.AllEdgeRootContraction

/-! Identifying both grounded split terminals recovers the all-edge root quotient. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.ChordSplit
open StatementGeometry Trees
open FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- The two original roots, with their nonemptiness witnessed by alpha. -/
def pairRoots (alpha beta : V) : Roots (V := V) :=
  ⟨{alpha, beta}, ⟨alpha, Or.inl rfl⟩⟩

/-- Forget only the Boolean split tag. Every free vertex keeps its original value. -/
def identifyGroundedTerminals (alpha beta : V) :
    GroundedSplitVertex alpha beta → NonemptyQuotient.Vertex (pairRoots alpha beta)
  | .inl v => some ⟨v.val, by
      simpa only [pairRoots, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        using v.property⟩
  | .inr _ => none

omit [Fintype V] [Fintype E] in
theorem identify_grounded_splitEndpoint (alpha beta : V) (side : E → Bool)
    (x : V) (e : E) :
    identifyGroundedTerminals alpha beta (groundMap alpha beta (splitEndpoint alpha side x e)) =
      NonemptyQuotient.project (pairRoots alpha beta) x := by
  by_cases ha : x = alpha
  · subst x
    simp only [splitEndpoint, groundMap, identifyGroundedTerminals,
      NonemptyQuotient.project, pairRoots, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or, dif_pos]
  · by_cases hb : x = beta
    · subst x
      simp only [splitEndpoint, dif_neg ha, groundMap,
        identifyGroundedTerminals, NonemptyQuotient.project, pairRoots,
        Set.mem_insert_iff, Set.mem_singleton_iff, or_true, dif_pos]
    · simp only [splitEndpoint, groundMap,
        identifyGroundedTerminals, NonemptyQuotient.project, pairRoots,
        Set.mem_insert_iff, Set.mem_singleton_iff, ha, hb, or_self, ↓reduceDIte]

/-- The quotient of the actual grounded split retains all IDs, including all root-root loops. -/
theorem identify_grounded_graph (G : Multigraph V E) (alpha beta : V) (side : E → Bool) :
    (⟨fun e => identifyGroundedTerminals alpha beta
        ((groundedSplitGraph (⟨G.left, G.right⟩ : CopiedGraph V E) alpha beta side).left e),
      fun e => identifyGroundedTerminals alpha beta
        ((groundedSplitGraph (⟨G.left, G.right⟩ : CopiedGraph V E) alpha beta side).right e)⟩ :
        CopiedGraph (NonemptyQuotient.Vertex (pairRoots alpha beta)) E) =
      NonemptyQuotient.allEdgeGraph G (pairRoots alpha beta) := by
  have hl := fun e => identify_grounded_splitEndpoint alpha beta side (G.left e) e
  have hr := fun e => identify_grounded_splitEndpoint alpha beta side (G.right e) e
  exact congrArg₂ CopiedGraph.mk (funext hl) (funext hr)

end
end FiniteAvalanches.Electrical.ChordSplit
