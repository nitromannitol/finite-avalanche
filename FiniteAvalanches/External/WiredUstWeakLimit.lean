import FiniteAvalanches.Trees.Lattice.WiredLaw

set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Trees.Lattice MeasureTheory LatticeProb

/-- Pemantle (1991), Häggström (1998), BLPS (2001); Lyons–Peres §10.1, Járai (2012) Theorem 2:
the wired uniform spanning tree measures of the boxes `[-N,N]²` converge weakly.
Wiring removes loops and retains all multiple edges: LP p.26, BLPS p.16. -/
axiom square_lattice_wired_ust_weak_limit :
    ∃ ν : ProbabilityMeasure EdgeField,
      Filter.Tendsto finiteProbability Filter.atTop (nhds ν)

end FiniteAvalanches.External
