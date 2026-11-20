import FiniteAvalanches.Trees.Lattice.Topology
import FiniteAvalanches.Trees.Lattice.WiredLaw
import FiniteAvalanches.Wilson.Lattice.WiredLimitOneEnd

set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Trees.Lattice MeasureTheory LatticeProb

                                                                                           
                                                                    
                                                                                  
                                                                                  
                                                                             
                                                                                  
theorem square_lattice_wired_ust_one_tree_one_end
    (ν : ProbabilityMeasure EdgeField)
    (hν : Filter.Tendsto finiteProbability Filter.atTop (nhds ν)) :
    ∀ᵐ ω ∂(ν : Measure EdgeField), IsTree ω ∧
      ∀ K : Finset (Site 2),
        ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)),
          (SimpleGraph.ComponentCompl.supp C).Infinite :=
  FiniteAvalanches.Wilson.Lattice.wiredLimit_ae_tree_and_existsUnique_infinite_componentCompl ν hν

end FiniteAvalanches.External
