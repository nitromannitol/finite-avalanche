import FiniteAvalanches.Wilson.Lattice.WiredRootedSupport

/-! Two-color Wilson forests on the recurrent square lattice. -/
set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Wilson.Lattice

                                                                             
                                                                               
                                                                                   
                                                                                
                                                                                               
theorem wilson_two_color_law_existsUnique (R : RootPair) :
    (∃! ν : MeasureTheory.ProbabilityMeasure ForestField, IsWilsonLaw R ν) ∧
    ∀ ν : MeasureTheory.ProbabilityMeasure ForestField, IsWilsonLaw R ν →
      Filter.Tendsto (finiteForestProbability R) Filter.atTop (nhds ν) := by
  obtain ⟨ν, hν, _⟩ := existsUnique_wilsonCylinderLaw R
  exact wilsonLaw_existsUnique_of_cylinder_rooted_support R ν hν (hν.ae_rooted R ν)

end FiniteAvalanches.External
