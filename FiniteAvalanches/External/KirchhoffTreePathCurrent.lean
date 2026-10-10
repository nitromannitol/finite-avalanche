import FiniteAvalanches.Electrical.Trees.SignedPathTraversal

namespace FiniteAvalanches.External
open scoped Classical BigOperators
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry

/-- The mean signed source-to-ground path in the uniform spanning tree is unit current.
Lyons–Peres (2016 hardback), Exercise 4.23, p.125; finite unit-conductance specialization. -/
axiom kirchhoff_meanTreePathCurrent
    {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (v : V)
    (hc : (supportGraph J.left J.right).Preconnected)
    (u : V) (hu : u ≠ v) (e : E) :
    (∑ T : J.SpanningTree, J.signedPathTraversal T u v e) /
      (Fintype.card J.SpanningTree : ℝ) =
    groundedGreen J.left J.right v hc u (J.left e) -
      groundedGreen J.left J.right v hc u (J.right e)

end FiniteAvalanches.External
