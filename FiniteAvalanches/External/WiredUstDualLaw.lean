import FiniteAvalanches.Trees.Lattice.Dual
import FiniteAvalanches.Trees.Lattice.WiredLaw

set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Trees.Lattice MeasureTheory LatticeProb

/-- Planar self-duality (BLPS Theorem 12.2 with Proposition 5.6; Lyons–Peres §10.3). The
absent edges of the lattice UST, transported to `ℤ²` by naming faces by their lower-left
corners, form a field with the same law. -/
axiom square_lattice_ust_dual_law
    (ν : ProbabilityMeasure EdgeField)
    (hν : Filter.Tendsto finiteProbability Filter.atTop (nhds ν)) :
    (ν : Measure EdgeField).map dualField = (ν : Measure EdgeField)

end FiniteAvalanches.External
