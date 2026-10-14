import CurrentSource.MinimumCornerTransfer
import FiniteAvalanches.Electrical.Physical.Undilated.Meaning

/-! The undilated physical square sum consumes the minimum-face corner transfer. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Geometry
open FiniteAvalanches.Electrical.Physical.Unscaled
open FiniteAvalanches.Electrical.Physical.Undilated
open CurrentRegularPhysical
open scoped Classical BigOperators
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

/-- Uniqueness identifies the physical two-terminal solve with the original source voltage. -/
theorem source_voltage_eq_physical
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) :
    Source.voltage (sourceGraph D P marked) (alpha D P) (beta D P)
      (Repair8.graph_connected D P hD marked).preconnected = Repair8.voltage D P hD marked :=
  Repair8.voltage_unique D P hD marked _
    (Source.voltage_spec _ _ _ (by simp [alpha, beta]) _)

/-- The corner oscillation is the literal undilated physical-square oscillation. -/
theorem edgeOsc_eq_physicalSquare (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (phi : Vertex D P → ℝ)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec Q (alpha D P) (beta D P) A phi psi)
    (epsilon y0 : ℝ) (hepsilon : 0 < epsilon) (e : Copy D P marked) :
    edgeOsc D P marked Q A phi psi epsilon y0 hepsilon e =
      (physicalSquare (sourceGraph D P marked) Q (alpha D P) (beta D P) A phi psi e).angularOsc
        epsilon y0 1 (by norm_num) hepsilon := by
  unfold edgeOsc Square.angularOsc Geometry.oscillation
  rw [square_dilate_one, physicalSquare_carrier _ _ _ _ _ _ _ hpsi]

/-- Source voltage and physical packing supply the same copied-square sum16. -/
theorem source_edgeOsc_sum_sixteen
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (psi : A.embedding.Face → ℝ)
    (hpsi : stream_spec Q (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi)
    (j : Copy D P marked)
    (hpj : 0 < |Repair8.voltage D P hD marked (copyA D P marked j) -
      Repair8.voltage D P hD marked (copyB D P marked j)|) (y0 : ℝ) :
    let phi := Repair8.voltage D P hD marked
    let p := |phi (copyA D P marked j) - phi (copyB D P marked j)|
    (∑ e, (edgeOsc D P marked Q A phi psi (p / 2) y0 (by positivity) e)^2) ≤
      16 * (1 + Real.log (2 / p)) := by
  intro phi p
  have hv := source_voltage_eq_physical D P marked hD
  let hc := (Repair8.graph_connected D P hD marked).preconnected
  have hs : stream_spec Q (alpha D P) (beta D P) A
      (Source.voltage (sourceGraph D P marked) (alpha D P) (beta D P) hc) psi := by
    rw [hv]; exact hpsi
  have hp : 0 < |Source.voltage (sourceGraph D P marked) (alpha D P) (beta D P) hc
      (copyA D P marked j) -
      Source.voltage (sourceGraph D P marked) (alpha D P) (beta D P) hc (copyB D P marked j)| := by
    rw [hv]; exact hpj
  have h := physical_copy_cutoff_square_sum_le_sixteen (sourceGraph D P marked) Q hc
    (alpha D P) (beta D P) (by simp [alpha, beta]) A psi hs j hp y0
  dsimp only at h
  simp only [hv] at h
  simpa only [edgeOsc_eq_physicalSquare D P marked Q A phi psi hpsi] using h

/-- The current corner21 and undilated16 estimates give the precise 336 energy constant.
Only the separate placement of terminal corners remains a conditional premise. -/
theorem source_split_transfer336_of_terminal_corners
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (psi : A.embedding.Face → ℝ)
    (hpsi : stream_spec Q (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi)
    (side : Copy D P marked → Bool) (j : Copy D P marked)
    (hpj : 0 < |Repair8.voltage D P hD marked (copyA D P marked j) -
      Repair8.voltage D P hD marked (copyB D P marked j)|) (y0 : ℝ)
    (hheight : ∀ e, e ≠ j →
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P →
      if side e then y0 + |Repair8.voltage D P hD marked (copyA D P marked j) -
          Repair8.voltage D P hD marked (copyB D P marked j)| / 2 ≤
        max (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e)))
      else min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e))) ≤
        y0 - |Repair8.voltage D P hD marked (copyA D P marked j) -
          Repair8.voltage D P hD marked (copyB D P marked j)| / 2) :
    let phi := Repair8.voltage D P hD marked
    let p := |phi (copyA D P marked j) - phi (copyB D P marked j)|
    let f := splitMinimumTrial D P marked Q A phi psi (p / 2) y0
    let a := fun e => splitEndpoint (alpha D P) side (copyA D P marked e) e
    let b := fun e => splitEndpoint (alpha D P) side (copyB D P marked e) e
    (∑ e, (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) *
      (f (a e) - f (b e))^2) ≤ 1 + 336 * (1 + Real.log (2 / p)) := by
  intro phi p f a b
  have h21 := source_split_transfer21_of_terminal_corners D P marked hD Q A psi side j
    (p / 2) y0 (by positivity) hheight
  have h16 := source_edgeOsc_sum_sixteen D P marked hD Q A psi hpsi j hpj y0
  dsimp only at h21 h16
  linarith only [h21, h16]

/-- On the real characterized physical stream, regular copies already satisfy the sharp336 bound. -/
theorem source_regular_transfer336
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (Q : PlaneEmbedding (sourceGraph D P marked))
    (A : OuterArc Q (alpha D P) (beta D P)) (psi : A.embedding.Face → ℝ)
    (hpsi : stream_spec Q (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi)
    (j : Copy D P marked)
    (hpj : 0 < |Repair8.voltage D P hD marked (copyA D P marked j) -
      Repair8.voltage D P hD marked (copyB D P marked j)|) (y0 : ℝ) :
    let phi := Repair8.voltage D P hD marked
    let p := |phi (copyA D P marked j) - phi (copyB D P marked j)|
    let f := fun x => angular (p / 2) y0 (minimumPoint D P marked Q A phi psi x)
    (∑ e : Copy D P marked, if isRegular D P (copyA D P marked e) ∧
        isRegular D P (copyB D P marked e) then
      (1 - phi (copyA D P marked e)) * (1 - phi (copyB D P marked e)) *
        (f (copyA D P marked e) - f (copyB D P marked e))^2 else 0) ≤
      336 * (1 + Real.log (2 / p)) := by
  intro phi p f
  have h21 := source_regular_weighted_transfer21 D P marked hD Q A psi (p / 2) y0 (by positivity)
  have h16 := source_edgeOsc_sum_sixteen D P marked hD Q A psi hpsi j hpj y0
  dsimp only at h21 h16
  linarith only [h21, h16]

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentMinimumCorners
