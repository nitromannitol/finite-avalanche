import OriginalGreenTiling
import FiniteAvalanches.Electrical.Physical.Undilated.Square

namespace FiniteAvalanches.Electrical.LovaszApplication
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep
open Geometry LovaszStream
open scoped Classical BigOperators
noncomputable section

/-- The concrete Green rectangles supply literal undilated squares. Their
coordinates, side lengths, full closed carriers and zero-current points are all checked. -/
theorem constructed_original_square_family (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    [Fintype (Face Q)] (v0 vm : Face Q)
    (hc : (supportGraph (sourceDeletedDualGraph D P marked Q charts).left
      (sourceDeletedDualGraph D P marked Q charts).right).Preconnected)
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vm) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vm)) :
    let J := originalGraph D P marked
    let K := sourceDeletedDualGraph D P marked Q charts
    let phi := Repair8.voltage D P hD marked
    let G := groundedGreen K.left K.right vm hc v0
    ∃ R : Copy D P marked → Square,
      (∀ e, (R e).x = min (phi (J.left e)) (phi (J.right e)) ∧
        (R e).y = min (-G (K.left e)) (-G (K.right e)) ∧
        (R e).side = |phi (J.left e) - phi (J.right e)| ∧
        (R e).carrier = copiedSquare J phi (fun F => -G F) K.left K.right e) ∧
      (∀ e f, e ≠ f → Disjoint (R e).openCarrier (R f).openCarrier) ∧
      (⋃ e, (R e).carrier) = Set.Icc 0 1 ×ˢ Set.Icc (-mass J phi) 0 ∧
      (∀ e, phi (J.left e) = phi (J.right e) →
        (R e).side = 0 ∧ (R e).carrier = {(phi (J.left e), -G (K.left e))}) ∧
      (∀ epsilon y0 : ℝ, ∀ he : 0 < epsilon, epsilon ≤ 1 →
        (∑ e : Copy D P marked, ((R e).angularOsc epsilon y0 1 (by norm_num) he)^2) ≤
          16 * (1 + Real.log (1 / epsilon))) := by
  dsimp only
  let J := originalGraph D P marked
  let K := sourceDeletedDualGraph D P marked Q charts
  let phi := Repair8.voltage D P hD marked
  let G := groundedGreen K.left K.right vm hc v0
  let R : Copy D P marked → Square := fun e =>
    ⟨min (phi (J.left e)) (phi (J.right e)), min (-G (K.left e)) (-G (K.right e)),
      |phi (J.left e) - phi (J.right e)|, abs_nonneg _⟩
  obtain ⟨hlength, hd, hcover, hzero, _hquarterTurn⟩ :=
    constructed_original_green_tiling D P hD marked Q charts v0 vm hc hmarked
  have hmax (a b : ℝ) : min a b + |a - b| = max a b := by
    rw [← max_sub_min_eq_abs']
    ring
  have hcarrier (e : Copy D P marked) : (R e).carrier =
      copiedSquare J phi (fun F => -G F) K.left K.right e := by
    change Set.Icc _ (min (phi (J.left e)) (phi (J.right e)) + |phi (J.left e)-phi (J.right e)|) ×ˢ
      Set.Icc _ (min (-G (K.left e)) (-G (K.right e)) + |phi (J.left e)-phi (J.right e)|) = _
    rw [hmax, ← hlength e, hmax]
    rfl
  have hdisj (e f : Copy D P marked) (hef : e ≠ f) :
      Disjoint (R e).openCarrier (R f).openCarrier := by
    rw [← Plane.Square.interior_carrier, ← Plane.Square.interior_carrier,
      hcarrier e, hcarrier f]
    exact hd e f hef
  have hp := Repair8.voltage_spec D P hD marked
  have hv := Plane.voltage_range J.left J.right (alpha D P) (beta D P)
    (Repair8.graph_connected D P hD marked).preconnected phi hp.1 hp.2.1 hp.2.2
  have hstrip (e : Copy D P marked) : (R e).carrier ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ := by
    rw [hcarrier e]
    intro z hz
    exact ⟨⟨(le_min (hv (J.left e)).1 (hv (J.right e)).1).trans hz.1.1,
      hz.1.2.trans (max_le (hv (J.left e)).2 (hv (J.right e)).2)⟩, Set.mem_univ _⟩
  refine ⟨R, ?_, hdisj, ?_, ?_, ?_⟩
  · intro e
    exact ⟨rfl, rfl, rfl, hcarrier e⟩
  · simpa only [hcarrier] using hcover
  · intro e hz
    refine ⟨?_, (hcarrier e).trans (hzero e hz)⟩
    change phi (J.left e) = phi (J.right e) at hz
    change |phi (J.left e) - phi (J.right e)| = 0
    rw [hz, sub_self, abs_zero]
  · intro epsilon y0 he he1
    exact Physical.Undilated.angular_square_sum_le_sixteen Finset.univ R
      (fun e _ f _ hef => hdisj e f hef) epsilon y0 he he1 (fun e _ => hstrip e)

end
end FiniteAvalanches.Electrical.LovaszApplication

#print axioms FiniteAvalanches.Electrical.LovaszApplication.constructed_original_square_family
