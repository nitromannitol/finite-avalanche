import FiniteAvalanches.External.PolyaSquareLattice
import FiniteAvalanches.Wilson.Lattice.SimpleWalk

set_option autoImplicit false
namespace FiniteAvalanches.External.ProvedConsumers
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice

/-- Direct consumption of the unchanged complete external signature. -/
theorem polya_exact_type (x a : Site 2) :
    walkLaw {ξ | ∃ t : ℕ, position x ξ t = a} = 1 :=
  FiniteAvalanches.External.polya_square_lattice_hits_every_site x a

end FiniteAvalanches.External.ProvedConsumers
