import FiniteAvalanches.Trees.Lattice.Topology
import FiniteAvalanches.Trees.Lattice.WiredLaw

set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Trees.Lattice MeasureTheory LatticeProb

                                                                                           
                                                                    
                                                                                  
                                                                                  
                                                                             
                                                                                  
axiom square_lattice_wired_ust_one_tree_one_end
    (ν : ProbabilityMeasure EdgeField)
    (hν : Filter.Tendsto finiteProbability Filter.atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), IsTree ω ∧
      ∀ K : Finset (Site 2),
        ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)),
          (SimpleGraph.ComponentCompl.supp C).Infinite

end FiniteAvalanches.External
