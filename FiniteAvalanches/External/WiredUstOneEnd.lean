import FiniteAvalanches.Trees.Lattice.Topology
import FiniteAvalanches.Trees.Lattice.WiredLaw

set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Trees.Lattice MeasureTheory LatticeProb

/-- The limit is almost surely a single tree with one end (Pemantle; Benjamini–Lyons–Peres–
Schramm; Lyons–Peres Theorems 10.30, 10.36, 10.41; BLPS Theorem12.4;
Járai Theorem3(i)). One end uses LP p.242's finite-complement component criterion.
It mathematically implies unique rays from each vertex in this locally finite tree
(LP Example7.1 p.236, ray definition p.364), but this input supplies only the
component criterion: the Lean ray/orientation bridge remains an internal proof. -/
axiom square_lattice_wired_ust_one_tree_one_end
    (ν : ProbabilityMeasure EdgeField)
    (hν : Filter.Tendsto finiteProbability Filter.atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), IsTree ω ∧
      ∀ K : Finset (Site 2),
        ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)),
          (SimpleGraph.ComponentCompl.supp C).Infinite

end FiniteAvalanches.External
