import FiniteAvalanches.External.KilledWiredVoltage
import FiniteAvalanches.Wilson.Lattice.HittingTimes
import FiniteAvalanches.Needle.Conductance

set_option autoImplicit false
namespace FiniteAvalanches.External.ProvedConsumers
open LatticeProb FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile.FiniteWired
open scoped Classical

/-- Direct consumption of the unchanged complete external signature. -/
theorem voltage_exact_type (N : ℕ) (S : Finset (Active N)) (x : Site 2) :
    walkLaw (hitBefore (↑(S.image site) : Set (Site 2)) (box 2 N)ᶜ x) =
      ENNReal.ofReal (FiniteAvalanches.Needle.voltage N S
        (if hx : inBox N x then some (activeOfSite N x hx) else none)) :=
  FiniteAvalanches.External.wired_srw_firstHit_voltage N S x

end FiniteAvalanches.External.ProvedConsumers
