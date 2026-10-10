import FiniteAvalanches.External.PolyaSquareLatticeProof
import FiniteAvalanches.Wilson.Lattice.SimpleWalk

set_option autoImplicit false
namespace FiniteAvalanches.External
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice

/-- Pólya (1921): simple random walk on `ℤ²` has the classical arbitrary-start/site hitting form.
Return recurrence (LP Pólya theorem p.38) plus irreducibility gives this equivalent
hitting probability1 formulation (recurrence convention LP pp.6–7); LP does not
state a numbered theorem with this exact sentence. Time zero is included. -/
theorem polya_square_lattice_hits_every_site (x a : Site 2) :
    walkLaw {ξ | ∃ t : ℕ, position x ξ t = a} = 1 :=
  FiniteAvalanches.ProvedStandards.polya_square_lattice_hits_every_site x a


end FiniteAvalanches.External
