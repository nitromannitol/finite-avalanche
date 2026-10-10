import FiniteAvalanches.External.KilledWiredVoltageProof
import FiniteAvalanches.Wilson.Lattice.HittingTimes
import FiniteAvalanches.Needle.Conductance

set_option autoImplicit false
namespace FiniteAvalanches.External
open LatticeProb FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile.FiniteWired
open scoped Classical

/-- Finite unit-conductance wired SRW: the first-exit-before-zero hitting
probability equals the uniquely characterized zero/one Dirichlet voltage.
The iid direction word chooses each original incident copy with probability 1/4;
only its prefix through the first zero hit or exterior exit is observed. -/
theorem wired_srw_firstHit_voltage (N : ℕ) (S : Finset (Active N)) (x : Site 2) :
    walkLaw (hitBefore (↑(S.image site) : Set (Site 2)) (box 2 N)ᶜ x) =
      ENNReal.ofReal (FiniteAvalanches.Needle.voltage N S
        (if hx : inBox N x then some (activeOfSite N x hx) else none)) :=
  FiniteAvalanches.WiredHitting.wired_srw_firstHit_voltage N S x

end FiniteAvalanches.External
