import FiniteAvalanches.External.WiredUstWeakLimit

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb MeasureTheory FiniteAvalanches.External FiniteAvalanches.Sandpile
open scoped Classical ENNReal
noncomputable section

theorem existsUnique_wired_ust_limit :
    ∃! ν : ProbabilityMeasure EdgeField,
      Filter.Tendsto finiteProbability Filter.atTop (nhds ν) := by
  obtain ⟨ν, hν⟩ := square_lattice_wired_ust_weak_limit
  exact ⟨ν, hν, fun μ hμ => tendsto_nhds_unique hμ hν⟩

/-- The wired uniform spanning tree of `ℤ²`, chosen from the proved `∃!`. -/
def squareLatticeUST : ProbabilityMeasure EdgeField :=
  Classical.choose existsUnique_wired_ust_limit.exists

theorem squareLatticeUST_tendsto :
    Filter.Tendsto finiteProbability Filter.atTop (nhds squareLatticeUST) :=
  Classical.choose_spec existsUnique_wired_ust_limit.exists

theorem squareLatticeUST_unique (μ : ProbabilityMeasure EdgeField)
    (hμ : Filter.Tendsto finiteProbability Filter.atTop (nhds μ)) : μ = squareLatticeUST :=
  tendsto_nhds_unique hμ squareLatticeUST_tendsto

theorem squareLatticeUST_full_characterization (ν : ProbabilityMeasure EdgeField) :
    ν = squareLatticeUST ↔ Filter.Tendsto finiteProbability Filter.atTop (nhds ν) := by
  constructor
  · rintro rfl
    exact squareLatticeUST_tendsto
  · exact squareLatticeUST_unique ν

end
end FiniteAvalanches.Trees.Lattice
