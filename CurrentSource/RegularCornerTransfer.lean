import CurrentSource.MinimumFaceCorners
import FiniteAvalanches.Electrical.Reference.Voltage
import FiniteAvalanches.Electrical.Plane.Ranges

/-! The degree-four corner transfer on the original regular-to-regular copies. -/

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

/-- Three squared corner increments give the exact local factor three. -/
theorem minimum_corner_edge_sq_le
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) (hepsilon : 0 < epsilon)
    (e : Copy D P marked)
    (ha : isRegular D P (copyA D P marked e))
    (hb : isRegular D P (copyB D P marked e)) :
    (angular epsilon y0 (minimumPoint D P marked Q A phi psi (copyA D P marked e)) -
      angular epsilon y0 (minimumPoint D P marked Q A phi psi (copyB D P marked e)))^2 ≤
      3 * ((edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e)^2 +
        otherIncidentCharge (copyA D P marked) (copyB D P marked) (isRegular D P)
          (fun q => (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon q)^2)
            (copyA D P marked e) e +
        otherIncidentCharge (copyA D P marked) (copyB D P marked) (isRegular D P)
          (fun q => (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon q)^2)
            (copyB D P marked e) e) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  obtain ⟨z, hz, ha'⟩ := minimum_corner_error D P marked hD Q A phi psi epsilon y0 hepsilon
    x e (Or.inl hx)
  obtain ⟨t, ht, hb'⟩ := minimum_corner_error D P marked hD Q A phi psi epsilon y0 hepsilon
    y e (Or.inr hy)
  rw [← hx] at ha'
  rw [← hy] at hb'
  have hm := corner_difference_sq_le D P marked Q A phi psi epsilon y0 hepsilon e z t hz ht
  have h3 := sum_three_sq_le
    (angular epsilon y0 (minimumPoint D P marked Q A phi psi (copyA D P marked e)) - angular epsilon y0 z)
    (angular epsilon y0 z - angular epsilon y0 t)
    (angular epsilon y0 t - angular epsilon y0 (minimumPoint D P marked Q A phi psi (copyB D P marked e)))
  have heq :
      (angular epsilon y0 (minimumPoint D P marked Q A phi psi (copyA D P marked e)) - angular epsilon y0 z) +
      (angular epsilon y0 z - angular epsilon y0 t) +
      (angular epsilon y0 t - angular epsilon y0 (minimumPoint D P marked Q A phi psi (copyB D P marked e))) =
      angular epsilon y0 (minimumPoint D P marked Q A phi psi (copyA D P marked e)) -
      angular epsilon y0 (minimumPoint D P marked Q A phi psi (copyB D P marked e)) := by ring
  rw [heq] at h3
  rw [← neg_sub (angular epsilon y0 t), neg_sq] at hb'
  linarith only [h3, ha', hb', hm]

/-- The actual source voltage puts every original endpoint weight in the unit interval. -/
theorem source_voltage_weights
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (x : Vertex D P) :
    0 ≤ 1 - Repair8.voltage D P hD marked x ∧ 1 - Repair8.voltage D P hD marked x ≤ 1 := by
  have hs := Repair8.voltage_spec D P hD marked
  have hr := FiniteAvalanches.Electrical.Plane.voltage_range
    (copyA D P marked) (copyB D P marked) (alpha D P) (beta D P)
    (Repair8.graph_connected D P hD marked).preconnected
    (Repair8.voltage D P hD marked) hs.1 hs.2.1 hs.2.2 x
  constructor <;> linarith only [hr.1, hr.2]

/-- Current corner charging on every original regular-to-regular copy, with no geometric
comparison, degree, voltage-range, or summed bound supplied as a premise. -/
theorem source_regular_weighted_transfer21
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P))
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) (hepsilon : 0 < epsilon) :
    let phi := Repair8.voltage D P hD marked
    let f := fun x => angular epsilon y0 (minimumPoint D P marked Q A phi psi x)
    (∑ e : Copy D P marked, if isRegular D P (copyA D P marked e) ∧
        isRegular D P (copyB D P marked e) then
      (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) *
        (f (copyA D P marked e) - f (copyB D P marked e))^2 else 0) ≤
      21 * ∑ e, (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e)^2 := by
  intro phi f
  let B := fun q => (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon q)^2
  let C := otherIncidentCharge (copyA D P marked) (copyB D P marked) (isRegular D P) B
  have hB (e : Copy D P marked) : 0 ≤ B e := sq_nonneg _
  have hC (x : Vertex D P) (e : Copy D P marked) : 0 ≤ C x e :=
    otherIncidentCharge_nonneg _ _ _ B hB x e
  have hterm (e : Copy D P marked) :
      (if isRegular D P (copyA D P marked e) ∧ isRegular D P (copyB D P marked e) then
        (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) *
          (f (copyA D P marked e) - f (copyB D P marked e))^2 else 0) ≤
      3 * (B e + C (copyA D P marked e) e + C (copyB D P marked e) e) := by
    by_cases he : isRegular D P (copyA D P marked e) ∧ isRegular D P (copyB D P marked e)
    · rw [if_pos he]
      have ha := source_voltage_weights D P marked hD (copyA D P marked e)
      have hb := source_voltage_weights D P marked hD (copyB D P marked e)
      have hw : (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) ≤ 1 := by
        exact (mul_le_mul_of_nonneg_right ha.2 hb.1).trans (by simpa only [one_mul] using hb.2)
      have hweighted :
          (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) *
            (f (copyA D P marked e) - f (copyB D P marked e))^2 ≤
          (f (copyA D P marked e) - f (copyB D P marked e))^2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hw
          (sq_nonneg (f (copyA D P marked e) - f (copyB D P marked e)))
      exact hweighted.trans
        (minimum_corner_edge_sq_le D P marked hD Q A phi psi epsilon y0 hepsilon e he.1 he.2)
    · rw [if_neg he]
      exact mul_nonneg (by norm_num)
        (add_nonneg (add_nonneg (hB e) (hC (copyA D P marked e) e)) (hC (copyB D P marked e) e))
  have hcharge := source_neighbor_charge_le_six D P marked B hB
  calc
    _ ≤ ∑ e, 3 * (B e + C (copyA D P marked e) e + C (copyB D P marked e) e) :=
      Finset.sum_le_sum (fun e _ => hterm e)
    _ = 3 * ((∑ e, B e) + ∑ e, (C (copyA D P marked e) e + C (copyB D P marked e) e)) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
      ring
    _ ≤ 21 * ∑ e, B e := by linarith only [hcharge]

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
