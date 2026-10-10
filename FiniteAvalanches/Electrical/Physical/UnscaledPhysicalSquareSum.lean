import FiniteAvalanches.Electrical.Physical.UnscaledSquareSum
import FiniteAvalanches.Electrical.Geometry.PhysicalTilingStream
import FiniteAvalanches.Electrical.Plane.SquareSlices

/-! The sharp sum on the existing physical BSST carrier, without constructing a new drawing. -/

open Set
open scoped BigOperators Classical
open FiniteAvalanches.Electrical.Geometry
open FiniteAvalanches.Electrical.StatementGeometry

namespace FiniteAvalanches.Electrical.Physical.Unscaled

/-- The literal original copied voltage/stream coordinates as an ordinary square.
Its carrier equals the source edge square when the actual stream equation holds. -/
noncomputable def physicalSquare {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (e : E) : Square where
  x := min (phi (J.left e)) (phi (J.right e))
  y := min (psi (A.embedding.leftFace (.inl e))) (psi (A.embedding.rightFace (.inl e)))
  side := |phi (J.left e) - phi (J.right e)|
  side_nonneg := abs_nonneg _

private theorem min_add_abs_sub (u v : ℝ) : min u v + |u - v| = max u v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Full closed carriers match the actual source squares, including the side-zero point. -/
theorem physicalSquare_carrier {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A phi psi) (e : E) :
    (physicalSquare J D alpha beta A phi psi e).carrier =
      Source.edgeSquare D alpha beta A phi psi e := by
  dsimp only [physicalSquare, Square.carrier, Source.edgeSquare]
  rw [min_add_abs_sub, ← hpsi.1 e, min_add_abs_sub]

/-- BSST provides disjointness on these exact faces/copy IDs; closed-carrier containment
comes from its existing physical rectangle theorem. No packing estimate is a premise. -/
theorem physical_angular_square_sum_le_144 {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V) (hne : alpha ≠ beta)
    (A : Source.OuterArc D alpha beta) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (epsilon y0 : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    (∑ e : E, ((physicalSquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).angularOsc
      epsilon y0 3 (by norm_num) he) ^ 2) ≤ 144 * (1 + Real.log (1 / epsilon)) := by
  let Q := physicalSquare J D alpha beta A (Source.voltage J alpha beta hc) psi
  have hcarrier := physicalSquare_carrier J D alpha beta A (Source.voltage J alpha beta hc) psi hpsi
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset E)) (fun e => (Q e).openCarrier) := by
    intro e _ f _ hef
    change Disjoint (Q e).openCarrier (Q f).openCarrier
    rw [← Plane.Square.interior_carrier, ← Plane.Square.interior_carrier, hcarrier e, hcarrier f]
    exact ((PhysicalTiling.physical_stream_tiling J D hc alpha beta hne A).2 psi hpsi).2.1 e f hef
  have hQ : ∀ e ∈ (Finset.univ : Finset E),
      (Q e).carrier ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    intro e _ z hz
    rw [hcarrier e] at hz
    have hrect := PhysicalTiling.physical_edgeSquare_subset_rectangle J D hc alpha beta hne A psi hpsi e hz
    exact ⟨hrect.1, mem_univ z.2⟩
  exact angular_square_sum_le_144 Finset.univ Q hd epsilon y0 he he1 hQ

/-- A positive selected original copied current uses its own half-current cutoff.
Its unit upper bound is produced by the actual voltage maximum principle. -/
theorem physical_copy_cutoff_square_sum_le_144 {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V) (hne : alpha ≠ beta)
    (A : Source.OuterArc D alpha beta) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (j : E) (hpj : 0 < |Source.voltage J alpha beta hc (J.left j) -
      Source.voltage J alpha beta hc (J.right j)|) (y0 : ℝ) :
    let p := |Source.voltage J alpha beta hc (J.left j) - Source.voltage J alpha beta hc (J.right j)|
    (∑ e : E, ((physicalSquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).angularOsc
      (p / 2) y0 3 (by norm_num) (by positivity)) ^ 2) ≤
        144 * (1 + Real.log (2 / p)) := by
  intro p
  obtain ⟨hpa, hpb, hh⟩ := Source.voltage_spec J alpha beta hne hc
  have hv := Plane.voltage_range J.left J.right alpha beta hc (Source.voltage J alpha beta hc) hpa hpb hh
  have hp1 : p ≤ 1 := abs_le.mpr
    ⟨by linarith only [(hv (J.left j)).1, (hv (J.right j)).2],
      by linarith only [(hv (J.left j)).2, (hv (J.right j)).1]⟩
  have he : 0 < p / 2 := by positivity
  have he1 : p / 2 ≤ 1 := by linarith only [hp1]
  have hrecip : 1 / (p / 2) = 2 / p := by ring
  simpa only [hrecip] using physical_angular_square_sum_le_144 J D hc alpha beta hne A psi hpsi
    (p / 2) y0 he he1

end FiniteAvalanches.Electrical.Physical.Unscaled
