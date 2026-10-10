import FiniteAvalanches.Wilson.Lattice.SamplerEvents

/-! One independently audited derived standard-literature input. Finite Wilson plus planar recurrence/common-increment coupling
identifies the arbitrary-root recurrent law and the fixed-root wired weak limit.
This is not a paper contact, conditional-law, or changing-root continuity input. -/
set_option autoImplicit false
namespace FiniteAvalanches.External
open FiniteAvalanches.Wilson.Lattice

/-- Full JOINT finite-query Wilson characterization, including present/absent
original lattice edges, and convergence of the actual copied wired forest laws.
Primary sources: Lyons–Peres (2016), Theorem 4.1 and §4.2; BLPS (2001), Proposition
5.6. Arbitrary nonempty root sets use ordinary recurrent lattice walks, never an
infinite-degree contracted walk. The exact input is registered in audit/trusted-inputs.json. -/
axiom wilson_two_color_law_existsUnique (R : RootPair) :
    (∃! ν : MeasureTheory.ProbabilityMeasure ForestField, IsWilsonLaw R ν) ∧
    ∀ ν : MeasureTheory.ProbabilityMeasure ForestField, IsWilsonLaw R ν →
      Filter.Tendsto (finiteForestProbability R) Filter.atTop (nhds ν)

end FiniteAvalanches.External
