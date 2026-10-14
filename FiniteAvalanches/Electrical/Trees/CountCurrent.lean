import LatticeProb.Graph.CopiedGraph.ForestCountPotential
import FiniteAvalanches.Electrical.Trees.SignedPathTraversal
import FiniteAvalanches.Electrical.Geometry.CopiedGraphConnectivity
import FiniteAvalanches.Electrical.Green.Grounded

namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical BigOperators
noncomputable section
variable {V E : Type}

/-- Keep the original vertex and copy carriers and both stored endpoint maps. -/
def asLatticeProbGraph (J : CopiedGraph V E) : LatticeProb.Graph.CopiedGraph V E :=
  ⟨J.left, J.right⟩

/-- The copied positive operator is the existing production incidence operator. -/
theorem asLatticeProbGraph_positiveLaplacian [Fintype E] (J : CopiedGraph V E)
    (f : V → ℝ) (x : V) :
    J.asLatticeProbGraph.positiveLaplacian f x = laplacian J.left J.right f x := rfl

/-- Count two-root forests whose component of the given vertex contains the first root,
normalized by the number of spanning trees on the original copy carrier. -/
def forestCountPotential [Fintype E] (J : CopiedGraph V E) (u v x : V) : ℝ :=
  J.asLatticeProbGraph.forestCountPotential u v x

/-- The generic count potential has the identical forest predicate and normalization. -/
theorem asLatticeProbGraph_forestCountPotential [Fintype E] (J : CopiedGraph V E)
    (u v x : V) :
    J.asLatticeProbGraph.forestCountPotential u v x = J.forestCountPotential u v x := rfl

/-- Support-graph connectivity supplies reachability using the original copies. -/
theorem asLatticeProbGraph_reaches_univ [Fintype E] (J : CopiedGraph V E)
    (hc : (supportGraph J.left J.right).Preconnected) (x y : V) :
    J.asLatticeProbGraph.reaches Finset.univ x y :=
  J.reaches_univ_of_supportGraph_reachable (hc x y)

/-- The count potential satisfies the grounded unit-source Poisson data. -/
theorem forestCountPotential_poisson [Fintype E] (J : CopiedGraph V E)
    (u v : V) (hu : u ≠ v) (hc : (supportGraph J.left J.right).Preconnected) :
    J.forestCountPotential u v v = 0 ∧
      ∀ x, x ≠ v → laplacian J.left J.right (J.forestCountPotential u v) x =
        if x = u then (1 : ℝ) else 0 :=
  LatticeProb.Graph.CopiedGraph.forestCountPotential_poisson J.asLatticeProbGraph u v hu
    (J.asLatticeProbGraph_reaches_univ hc)

/-- The original signed tree-path average is the drop of the same count potential. -/
theorem mean_signedPathTraversal_eq_forestCountPotential_drop [Fintype E]
    (J : CopiedGraph V E) (u v : V) (hu : u ≠ v) (e : E) :
    (∑ T : J.SpanningTree, J.signedPathTraversal T u v e) /
        (Fintype.card J.SpanningTree : ℝ) =
      J.forestCountPotential u v (J.left e) - J.forestCountPotential u v (J.right e) :=
  LatticeProb.Graph.CopiedGraph.mean_signedPathTraversal_eq_potential_drop
    J.asLatticeProbGraph u v hu e

/-- Grounded Poisson uniqueness identifies the count potential with the existing Green
function, without an additional existence or positivity hypothesis. -/
theorem forestCountPotential_eq_groundedGreen [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (v : V) (hc : (supportGraph J.left J.right).Preconnected)
    (u : V) (hu : u ≠ v) :
    J.forestCountPotential u v = groundedGreen J.left J.right v hc u :=
  groundedPoisson_eq J.left J.right v hc (fun x => if x = u then 1 else 0)
    (J.forestCountPotential u v) (J.forestCountPotential_poisson u v hu hc)

/-- A finite mean is independent of the chosen enumeration of its carrier. -/
theorem mean_fintype_transfer {α : Type*} (I₁ I₂ : Fintype α)
    (f : α → ℝ) (r : ℝ)
    (h : ((@Finset.univ α I₁).sum f) / (@Fintype.card α I₁ : ℝ) = r) :
    ((@Finset.univ α I₂).sum f) / (@Fintype.card α I₂ : ℝ) = r := by
  cases Subsingleton.elim I₁ I₂
  exact h

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
