import LatticeProb.Walk.RecurrenceHitting
import FiniteAvalanches.Wilson.Lattice.BeurlingGeometry

                                                                              
namespace FiniteAvalanches.ProvedStandards

open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice

/-- The actual four-direction project walk hits every fixed site almost surely,
from every start, including a hit at time zero. -/
theorem polya_square_lattice_hits_every_site (x a : Site 2) :
    FiniteAvalanches.Wilson.Lattice.walkLaw {ξ | ∃ t : ℕ, position x ξ t = a} = 1 := by
  rw [← FiniteAvalanches.External.Beurling.pathLaw_eq_walkLaw]
  simpa only [FiniteAvalanches.External.Beurling.position_sum] using
    LatticeProb.pathLaw_two_dim_hit_site x a

end FiniteAvalanches.ProvedStandards
