import FiniteAvalanches.Wilson.ClassicalProtocol
import FiniteAvalanches.Trees.Ancestors

set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Trees FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical ENNReal

/-- Wilson's theorem on a finite connected network whose parallel edge copies are distinct
elements: run an independent walk (each step a uniform incident copy) from the first
unretained vertex of an ordering of the non-root vertices, loop-erase it chronologically and
attach it. The result is a uniform spanning tree of edge copies.
Lyons–Peres, *Probability on Trees and Networks* (2016), Theorem 4.1 and pp. 96–100. -/
axiom wilson_classical_tree_probability
    {V E I : Type} [Fintype V] [Fintype E] [Nontrivial V]
    (G : Multigraph V E) (hconn : ∀ x y : V, G.reaches Finset.univ x y) (ι : E ↪ I)
    (r : V) (order : List V) (hnodup : order.Nodup) (hspan : ∀ v : V, v ∈ order ↔ v ≠ r)
    (T : G.SpanningTree) :
    driversLaw G (uniformLetterLaw G hconn)
        {ω | ∃ s, classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω =
            some s ∧ s.edges = T.val} =
      (Fintype.card G.SpanningTree : ℝ≥0∞)⁻¹

end FiniteAvalanches.External
