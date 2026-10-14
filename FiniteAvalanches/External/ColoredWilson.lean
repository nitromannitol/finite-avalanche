import FiniteAvalanches.Wilson.Lattice.SamplerEvents

/-! One independently audited derived standard-literature input. Finite Wilson plus planar recurrence/common-increment coupling
identifies the arbitrary-root recurrent law and the fixed-root wired weak limit.
This is not a paper contact, conditional-law, or changing-root continuity input. -/
set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Wilson.Lattice

                                                                             
                                                                               
                                                                                   
                                                                                
                                                                                               
axiom wilson_two_color_law_existsUnique (R : RootPair) :
    (∃! ν : MeasureTheory.ProbabilityMeasure ForestField, IsWilsonLaw R ν) ∧
    ∀ ν : MeasureTheory.ProbabilityMeasure ForestField, IsWilsonLaw R ν →
      Filter.Tendsto (finiteForestProbability R) Filter.atTop (nhds ν)

end FiniteAvalanches.External
