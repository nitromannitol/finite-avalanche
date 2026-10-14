import FiniteAvalanches.Electrical.Physical.CurrentRegularStar
import CurrentSource.CornerCharging
import FiniteAvalanches.Electrical.Geometry.PhysicalFaceStar

/-! The actual minimum incident-face point and undilated copied-square comparisons. -/

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

/-- The original regular vertices, excluding both contracted terminals. -/
def isRegular (x : Vertex D P) : Prop := ∃ y : {y : D // y ∉ P.val}, x = Sum.inr y

/-- The source point uses the actual horizontal voltage and smallest incident face height. -/
def minimumPoint (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (x : Vertex D P) : ℝ × ℝ :=
  (phi x, sInf (incidentValues A.embedding.drawing psi x))

theorem edge_square_nonempty (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (e : Copy D P marked) :
    (edgeSquare Q (alpha D P) (beta D P) A phi psi e).Nonempty :=
  ⟨(phi (copyA D P marked e), psi (A.embedding.leftFace (.inl e))),
    ⟨⟨min_le_left _ _, le_max_left _ _⟩, ⟨min_le_left _ _, le_max_left _ _⟩⟩⟩

/-- Oscillation on each literal undilated original copied square. -/
def edgeOsc (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) (hepsilon : 0 < epsilon)
    (e : Copy D P marked) : ℝ :=
  oscillation (angular epsilon y0) (edgeSquare Q (alpha D P) (beta D P) A phi psi e)
    (edge_square_nonempty D P marked Q A phi psi e)
    ⟨1, fun u _ v _ => angular_sub_le_one epsilon y0 hepsilon u v⟩

theorem edgeOsc_nonneg (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) (hepsilon : 0 < epsilon)
    (e : Copy D P marked) : 0 ≤ edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e := by
  obtain ⟨z, hz⟩ := edge_square_nonempty D P marked Q A phi psi e
  have h := abs_sub_le_oscillation (F := angular epsilon y0) hz hz
    ⟨1, fun u _ v _ => angular_sub_le_one epsilon y0 hepsilon u v⟩
  simpa only [edgeOsc, sub_self, abs_zero] using h

theorem corner_difference_sq_le (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) (hepsilon : 0 < epsilon)
    (e : Copy D P marked) (z t : ℝ × ℝ)
    (hz : z ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e)
    (ht : t ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e) :
    (angular epsilon y0 z - angular epsilon y0 t)^2 ≤
      (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e)^2 := by
  have h := abs_sub_le_oscillation hz ht
    ⟨1, fun u _ v _ => angular_sub_le_one epsilon y0 hepsilon u v⟩
  have hs := (sq_le_sq₀ (abs_nonneg _) (edgeOsc_nonneg D P marked Q A phi psi epsilon y0 hepsilon e)).mpr h
  simpa only [sq_abs] using hs

/-- The minimum-face evaluation needs at most one different original square at a regular endpoint. -/
theorem minimum_corner_error
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (epsilon y0 : ℝ) (hepsilon : 0 < epsilon)
    (x : {x : D // x ∉ P.val}) (e : Copy D P marked)
    (he : copyA D P marked e = .inr x ∨ copyB D P marked e = .inr x) :
    ∃ z ∈ edgeSquare Q (alpha D P) (beta D P) A phi psi e,
      (angular epsilon y0 (minimumPoint D P marked Q A phi psi (.inr x)) -
        angular epsilon y0 z)^2 ≤
      otherIncidentCharge (copyA D P marked) (copyB D P marked) (isRegular D P)
        (fun q => (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon q)^2) (.inr x) e := by
  let hc := (Repair8.graph_connected D P hD marked).preconnected
  let x' : {v : Vertex D P // v ≠ alpha D P ∧ v ≠ beta D P} :=
    ⟨.inr x, by simp [alpha, beta]⟩
  obtain ⟨_hfinite, _hne, F, _G, hF, _hG, _hlo, _hhi, hmin, _hmax, _hsegment⟩ :=
    PhysicalFaceStar14.physical_incident_values_extrema (sourceGraph D P marked)
      Q hc (alpha D P) (beta D P) A psi x'
  have hp : minimumPoint D P marked Q A phi psi (.inr x) = (phi (.inr x), psi F) := by
    change (phi (.inr x), sInf (incidentValues A.embedding.drawing psi x'.val)) = _
    rw [hmin]
  have hB (q : Copy D P marked) : 0 ≤ (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon q)^2 :=
    sq_nonneg _
  rcases source_regular_square_one_neighbor D P marked hD Q A phi psi x e he F hF with
    h | ⟨q, hqe, hqx, hFq, G, hGe, hGq⟩
  · refine ⟨(phi (.inr x), psi F), h, ?_⟩
    rw [hp, sub_self, zero_pow (by decide : 2 ≠ 0)]
    exact otherIncidentCharge_nonneg _ _ _ _ hB _ _
  · refine ⟨(phi (.inr x), psi G), hGe, ?_⟩
    rw [hp]
    exact (corner_difference_sq_le D P marked Q A phi psi epsilon y0 hepsilon q _ _ hFq hGq).trans
      (le_otherIncidentCharge (copyA D P marked) (copyB D P marked) (isRegular D P)
        (fun q => (edgeOsc D P marked Q A phi psi epsilon y0 hepsilon q)^2)
        hB (Sum.inr x) e q hqe ⟨x, rfl⟩ hqx)

/-- Each neighboring square can be charged at most three times at either actual regular endpoint. -/
theorem source_neighbor_charge_le_six (B : Copy D P marked → ℝ) (hB : ∀ e, 0 ≤ B e) :
    (∑ e, (otherIncidentCharge (copyA D P marked) (copyB D P marked) (isRegular D P)
      B (copyA D P marked e) e +
      otherIncidentCharge (copyA D P marked) (copyB D P marked) (isRegular D P)
        B (copyB D P marked e) e)) ≤ 6 * ∑ e, B e := by
  apply sum_otherIncidentCharge_le_six _ _ _ B (copy_loopless D P marked) hB
  rintro x ⟨y, rfl⟩
  exact le_of_eq (free_degree D P marked y)

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
