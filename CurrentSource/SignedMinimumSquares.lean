import CurrentSource.SharpCornerPhysical
import CurrentSource.TerminalCornerPlacement

/-! Vertical reflection preserves the original undilated oscillations. The trial takes
the attained minimum in the signed height field, without asserting a reflected stream law. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners

open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Geometry
open CurrentRegularPhysical
open scoped Classical BigOperators
noncomputable section

/-- Reflection acts on the geometric coordinates, including the cutoff center. -/
def reflectHeight (z : ℝ × ℝ) : ℝ × ℝ := (z.1, -z.2)

theorem reflectHeight_involutive (z : ℝ × ℝ) :
    reflectHeight (reflectHeight z) = z := by simp [reflectHeight]

theorem angular_reflectHeight (epsilon y0 : ℝ) (z : ℝ × ℝ) :
    angular epsilon (-y0) (reflectHeight z) = 1 - angular epsilon y0 z := by
  have hy : -z.2 - -y0 = -(z.2 - y0) := by ring
  simp only [angular, radialDistance, reflectHeight, hy, abs_neg, neg_div]
  ring

theorem angular_reflectHeight_abs_sub (epsilon y0 : ℝ) (z w : ℝ × ℝ) :
    |angular epsilon (-y0) (reflectHeight z) - angular epsilon (-y0) (reflectHeight w)| =
      |angular epsilon y0 z - angular epsilon y0 w| := by
  rw [angular_reflectHeight, angular_reflectHeight]
  have h : (1 - angular epsilon y0 z) - (1 - angular epsilon y0 w) =
      angular epsilon y0 w - angular epsilon y0 z := by ring
  rw [h, abs_sub_comm]

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

/-- Every original copied-square carrier is reflected exactly, including point squares. -/
theorem reflectHeight_mem_edgeSquare (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (e : Copy D P marked) (z : ℝ × ℝ) :
    reflectHeight z ∈ edgeSquare Q (alpha D P) (beta D P) A phi (fun F => -psi F) e ↔
      z ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e := by
  simp only [edgeSquare, reflectHeight, Set.mem_prod, Set.mem_Icc, min_neg_neg,
    max_neg_neg, neg_le_neg_iff]
  tauto

/-- Reflection leaves the real oscillation on each undilated original copy unchanged. -/
theorem edgeOsc_reflectHeight (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) (hepsilon : 0 < epsilon)
    (e : Copy D P marked) :
    edgeOsc D P marked Q A phi (fun F => -psi F) epsilon (-y0) hepsilon e =
      edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e := by
  apply le_antisymm
  · apply oscillation_le (edge_square_nonempty D P marked Q A phi (fun F => -psi F) e)
      ⟨1, fun u _ v _ => angular_sub_le_one epsilon (-y0) hepsilon u v⟩
    intro z hz w hw
    have hz' : reflectHeight z ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e := by
      apply (reflectHeight_mem_edgeSquare D P marked Q A phi psi e (reflectHeight z)).mp
      simpa only [reflectHeight_involutive] using hz
    have hw' : reflectHeight w ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e := by
      apply (reflectHeight_mem_edgeSquare D P marked Q A phi psi e (reflectHeight w)).mp
      simpa only [reflectHeight_involutive] using hw
    have heq := angular_reflectHeight_abs_sub epsilon y0 (reflectHeight z) (reflectHeight w)
    simp only [reflectHeight_involutive] at heq
    exact heq.trans_le (abs_sub_le_oscillation hz' hw'
      ⟨1, fun u _ v _ => angular_sub_le_one epsilon y0 hepsilon u v⟩)
  · apply oscillation_le (edge_square_nonempty D P marked Q A phi psi e)
      ⟨1, fun u _ v _ => angular_sub_le_one epsilon y0 hepsilon u v⟩
    intro z hz w hw
    have hz' := (reflectHeight_mem_edgeSquare D P marked Q A phi psi e z).mpr hz
    have hw' := (reflectHeight_mem_edgeSquare D P marked Q A phi psi e w).mpr hw
    exact (angular_reflectHeight_abs_sub epsilon y0 z w).symm.trans_le
      (abs_sub_le_oscillation hz' hw'
        ⟨1, fun u _ v _ => angular_sub_le_one epsilon (-y0) hepsilon u v⟩)

/-- Both allowed stream orientations have the same copied oscillations. -/
theorem edgeOsc_signedHeight (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (epsilon y0 : ℝ) (hepsilon : 0 < epsilon) (e : Copy D P marked) :
    edgeOsc D P marked Q A phi (fun F => sigma * psi F) epsilon (sigma * y0) hepsilon e =
      edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e := by
  rcases hsigma with rfl | rfl
  · simp only [one_mul]
  · simpa only [neg_one_mul] using edgeOsc_reflectHeight D P marked Q A phi psi
      epsilon y0 hepsilon e

/-- Square16 applies to the signed-height minimum trial through exact oscillation equality;
the original stream law is used only on the original field. -/
theorem source_signed_edgeOsc_sum_sixteen
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked)) (A : OuterArc Q (alpha D P) (beta D P))
    (psi : A.embedding.Face → ℝ)
    (hpsi : stream_spec Q (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) (j : Copy D P marked)
    (hpj : 0 < |Repair8.voltage D P hD marked (copyA D P marked j) -
      Repair8.voltage D P hD marked (copyB D P marked j)|) (y0 : ℝ) :
    let phi := Repair8.voltage D P hD marked
    let p := |phi (copyA D P marked j) - phi (copyB D P marked j)|
    (∑ e, (edgeOsc D P marked Q A phi (fun F => sigma * psi F) (p / 2)
      (sigma * y0) (by positivity) e)^2) ≤ 16 * (1 + Real.log (2 / p)) := by
  intro phi p
  simp only [edgeOsc_signedHeight D P marked Q A phi psi sigma hsigma]
  exact source_edgeOsc_sum_sixteen D P marked hD Q A psi hpsi j hpj y0

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
