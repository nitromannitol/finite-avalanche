import CurrentSource.SignedMinimumSquares
import CurrentSource.HeightGauge

/-! Exact gauge translation of each original copied square and its angular oscillation. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Geometry
open CurrentRegularPhysical
open scoped Classical BigOperators
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

/-- The signed, grounded height uses the original characterized stream for packing. -/
theorem source_gauged_edgeOsc_sum_sixteen
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked)) (A : OuterArc Q (alpha D P) (beta D P))
    (psi : A.embedding.Face → ℝ)
    (hpsi : stream_spec Q (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) (gauge : ℝ) (j : Copy D P marked)
    (hpj : 0 < |Repair8.voltage D P hD marked (copyA D P marked j)-
      Repair8.voltage D P hD marked (copyB D P marked j)|) (y0 : ℝ) :
    let phi := Repair8.voltage D P hD marked
    let p := |phi (copyA D P marked j)-phi (copyB D P marked j)|
    (∑ e, (edgeOsc D P marked Q A phi (fun F => sigma*(psi F-gauge)) (p/2)
      (sigma*(y0-gauge)) (by positivity) e)^2) ≤ 16*(1+Real.log (2/p)) := by
  intro phi p
  have hfun : (fun F => sigma*(psi F-gauge)) = (fun F => sigma*psi F-(sigma*gauge)) := by
    funext F; ring
  have hcenter : sigma*(y0-gauge) = sigma*y0-(sigma*gauge) := by ring
  rw [hfun,hcenter]
  simp only [edgeOsc_shiftHeight D P marked Q A phi (fun F => sigma*psi F)]
  exact source_signed_edgeOsc_sum_sixteen D P marked hD Q A psi hpsi sigma hsigma j hpj y0

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
