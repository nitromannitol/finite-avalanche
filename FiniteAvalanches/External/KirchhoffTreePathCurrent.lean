import FiniteAvalanches.Electrical.Trees.CountCurrent

namespace FiniteAvalanches.External
open scoped Classical BigOperators
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry

/-- The mean signed source-to-ground path in the uniform spanning tree is unit current.
Lyons–Peres (2016 hardback), Exercise 4.23, p.125; finite unit-conductance specialization. -/
theorem kirchhoff_meanTreePathCurrent
    {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (v : V)
    (hc : (supportGraph J.left J.right).Preconnected)
    (u : V) (hu : u ≠ v) (e : E) :
    (∑ T : J.SpanningTree, J.signedPathTraversal T u v e) /
      (Fintype.card J.SpanningTree : ℝ) =
    groundedGreen J.left J.right v hc u (J.left e) -
      groundedGreen J.left J.right v hc u (J.right e) := by
  have hmean := J.mean_signedPathTraversal_eq_forestCountPotential_drop u v hu e
  have hgreen := congrArg (fun f : V → ℝ => f (J.left e) - f (J.right e))
    (J.forestCountPotential_eq_groundedGreen v hc u hu)
  have hfull := hmean.trans hgreen
  exact CopiedGraph.mean_fintype_transfer _
    (inferInstance : Fintype J.SpanningTree)
    (fun T => J.signedPathTraversal T u v e) _ hfull

end FiniteAvalanches.External
