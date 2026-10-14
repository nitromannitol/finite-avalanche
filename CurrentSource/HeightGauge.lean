import CurrentSource.MinimumFaceCorners

/-! Canonical vertical gauge: subtract the parameter from both heights and centers. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners

open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Geometry
open CurrentRegularPhysical
open scoped Classical BigOperators
noncomputable section

def shiftHeight (c : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1, z.2 - c)

theorem angular_shiftHeight (epsilon y0 c : ℝ) (z : ℝ × ℝ) :
    angular epsilon (y0-c) (shiftHeight c z) = angular epsilon y0 z := by
  simp only [angular, radialDistance, shiftHeight, sub_sub_sub_cancel_right]

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

theorem shiftHeight_mem_edgeSquare (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (c : ℝ) (e : Copy D P marked) (z : ℝ × ℝ) :
    shiftHeight c z ∈ edgeSquare Q (alpha D P) (beta D P) A phi (fun F => psi F-c) e ↔
      z ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e := by
  simp only [edgeSquare, shiftHeight, Set.mem_prod, Set.mem_Icc,
    min_sub_sub_right, max_sub_sub_right, sub_le_sub_iff_right]

theorem edgeOsc_shiftHeight (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 c : ℝ) (hepsilon : 0 < epsilon)
    (e : Copy D P marked) :
    edgeOsc D P marked Q A phi (fun F => psi F-c) epsilon (y0-c) hepsilon e =
      edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e := by
  apply le_antisymm
  · apply oscillation_le (edge_square_nonempty D P marked Q A phi (fun F => psi F-c) e)
      ⟨1, fun u _ v _ => angular_sub_le_one epsilon (y0-c) hepsilon u v⟩
    intro z hz w hw
    let z' : ℝ × ℝ := (z.1,z.2+c)
    let w' : ℝ × ℝ := (w.1,w.2+c)
    have hz' : z' ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e := by
      apply (shiftHeight_mem_edgeSquare D P marked Q A phi psi c e z').mp
      simpa only [shiftHeight, z', add_sub_cancel_right] using hz
    have hw' : w' ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e := by
      apply (shiftHeight_mem_edgeSquare D P marked Q A phi psi c e w').mp
      simpa only [shiftHeight, w', add_sub_cancel_right] using hw
    have heq : |angular epsilon (y0-c) z - angular epsilon (y0-c) w| =
        |angular epsilon y0 z' - angular epsilon y0 w'| := by
      have hz0 := angular_shiftHeight epsilon y0 c z'
      have hw0 := angular_shiftHeight epsilon y0 c w'
      simp only [shiftHeight, z', w', add_sub_cancel_right] at hz0 hw0
      rw [hz0,hw0]
    exact heq.trans_le (abs_sub_le_oscillation hz' hw'
      ⟨1,fun u _ v _ => angular_sub_le_one epsilon y0 hepsilon u v⟩)
  · apply oscillation_le (edge_square_nonempty D P marked Q A phi psi e)
      ⟨1,fun u _ v _ => angular_sub_le_one epsilon y0 hepsilon u v⟩
    intro z hz w hw
    have hz' := (shiftHeight_mem_edgeSquare D P marked Q A phi psi c e z).mpr hz
    have hw' := (shiftHeight_mem_edgeSquare D P marked Q A phi psi c e w).mpr hw
    have h := abs_sub_le_oscillation hz' hw'
      ⟨1,fun u _ v _ => angular_sub_le_one epsilon (y0-c) hepsilon u v⟩
    calc
      _ = |angular epsilon (y0-c) (shiftHeight c z) -
          angular epsilon (y0-c) (shiftHeight c w)| := by
        rw [angular_shiftHeight,angular_shiftHeight]
      _ ≤ _ := h

/-- The former additive convention is exactly the canonical gauge at the negated parameter. -/
theorem shiftHeight_neg_eq_add (c : ℝ) (z : ℝ × ℝ) :
    shiftHeight (-c) z = (z.1, z.2 + c) := by
  simp only [shiftHeight, sub_neg_eq_add]

/-- Negating the parameter also recovers every canonical subtraction from addition. -/
theorem shiftHeight_eq_add_neg (c : ℝ) (z : ℝ × ℝ) :
    shiftHeight c z = (z.1, z.2 + (-c)) := by
  simp only [shiftHeight, sub_eq_add_neg]

/-- The former additive angular statement follows with no new hypothesis. -/
theorem angular_add_height (epsilon y0 c : ℝ) (z : ℝ × ℝ) :
    angular epsilon (y0 + c) (z.1, z.2 + c) = angular epsilon y0 z := by
  simpa only [sub_neg_eq_add, shiftHeight_neg_eq_add] using
    angular_shiftHeight epsilon y0 (-c) z

/-- Every copied square, including point squares, satisfies the former additive statement. -/
theorem add_height_mem_edgeSquare (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (c : ℝ) (e : Copy D P marked) (z : ℝ × ℝ) :
    (z.1, z.2 + c) ∈ edgeSquare Q (alpha D P) (beta D P) A phi (fun F => psi F + c) e ↔
      z ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e := by
  simpa only [sub_neg_eq_add, shiftHeight_neg_eq_add] using
    shiftHeight_mem_edgeSquare D P marked Q A phi psi (-c) e z

/-- Exact real oscillation for the former additive convention, derived from the shared owner. -/
theorem edgeOsc_add_height (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 c : ℝ) (hepsilon : 0 < epsilon)
    (e : Copy D P marked) :
    edgeOsc D P marked Q A phi (fun F => psi F + c) epsilon (y0 + c) hepsilon e =
      edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e := by
  simpa only [sub_neg_eq_add] using
    edgeOsc_shiftHeight D P marked Q A phi psi epsilon y0 (-c) hepsilon e

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
