import FiniteAvalanches.Support.Plane.BoundaryTripleSmall
import FiniteAvalanches.Support.Plane.CrossingMultiplicity
import FiniteAvalanches.Support.Plane.CrossingStubSeparation

/-!
# Crossing arms in small faces

A face incident to at most three crossing sides admits separated rooted arms
that retain the crossing stubs with their parametrization.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Set unitInterval Source BSST
open scoped Classical

/-- In a face incident to at most three crossing sides, the crossing stubs can be
joined to one root by separated arms with their terminal speed preserved. -/
theorem exists_crossing_arms_in_face_of_card_le_three {V E : Type}
    [Fintype V] [Fintype E] {J : CopiedGraph V E} (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) (q : E → unitInterval → Plane)
    (hq : ∀ e, Continuous (q e) ∧ Function.Injective (q e))
    (hd : ∀ e f, e ≠ f → Disjoint (range (q e)) (range (q f)))
    (hface : ∀ e t, (t.val < 1 / 2 → q e t ∈ faceRegion D (negativeChartFace D e (charts e))) ∧
      (1 / 2 < t.val → q e t ∈ faceRegion D (positiveChartFace D e (charts e))))
    (hout : ∀ e F, q e ⟨1 / 2, by norm_num⟩ ∉ faceRegion D F)
    (F : Face D) (hcard : (Finset.univ.filter
      (fun i : E × Bool => dualSideFace D charts i = F)).card ≤ 3) :
    ∃ r ∈ faceRegion D F, ∃ arm : ∀ i : E × Bool,
      Path r (q i.1 ⟨1 / 2, by norm_num⟩),
      (∀ i, dualSideFace D charts i = F → Function.Injective (arm i)) ∧
      (∀ i, dualSideFace D charts i = F →
        range (arm i) ∩ (faceRegion D F)ᶜ = {q i.1 ⟨1 / 2, by norm_num⟩}) ∧
      (∀ i j, dualSideFace D charts i = F → dualSideFace D charts j = F → i ≠ j →
        ∀ z ∈ range (arm i) ∩ range (arm j), z = r ∨
          z = q i.1 ⟨1 / 2, by norm_num⟩ ∧
          q i.1 ⟨1 / 2, by norm_num⟩ = q j.1 ⟨1 / 2, by norm_num⟩) ∧
      (∀ i, dualSideFace D charts i = F → ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          arm i t = midpointStub (q i.1) (hq i.1).1 i.2 ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  classical
  let s : Finset (E × Bool) := Finset.univ.filter (fun i => dualSideFace D charts i = F)
  let stub : ∀ i : E × Bool, Path (q i.1 (crossingStubParameter i.2 0))
      (q i.1 ⟨1 / 2, by norm_num⟩) :=
    fun i => midpointStub (q i.1) (hq i.1).1 i.2
  have hmem : ∀ i, i ∈ s ↔ dualSideFace D charts i = F := by simp [s]
  have hstub : ∀ i ∈ s, Function.Injective (stub i) := fun i _ =>
    crossingStub_injective (q i.1) (hq i.1).1 (hq i.1).2 i.2
  have hstubface : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → stub i t ∈ faceRegion D F := by
    intro ⟨e, b⟩ hi t ht
    have hF := (hmem (e, b)).mp hi
    have hs := crossingStubParameter_side b t ht
    cases b with
    | false =>
        rw [← hF]
        exact (hface e _).1 (hs.1 rfl)
    | true =>
        rw [← hF]
        exact (hface e _).2 (hs.2 rfl)
  have hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (stub i) ∩ faceRegion D F) (range (stub j)) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro z hz hz'
    have hmid := midpointStub_inter_subset q (fun e => (hq e).1) (fun e => (hq e).2) hd hij
      (show z ∈ range (stub i) ∩ range (stub j) from ⟨hz.1, hz'⟩)
    have hzmid : z = q i.1 ⟨1 / 2, by norm_num⟩ := mem_singleton_iff.mp hmid.1
    exact hout i.1 F (hzmid ▸ hz.2)
  obtain ⟨r, hr, arm, ha, _, hb, hc, ht⟩ :=
    exists_boundary_arm_family_of_card_le_three (punctured_faceRegion_isOpen D F)
      (faceRegion_isConnected D F).isPreconnected (faceRegion_isConnected D F).nonempty
      s hcard stub hstub hdisj hstubface (fun i _ => hout i.1 F)
      (Set.finite_empty) (by simp)
      (fun i _ j _ k _ hij hik hjk =>
        not_three_crossing_sides_same_midpoint q hd hij hik hjk)
  exact ⟨r, hr, arm, fun i hi => ha i ((hmem i).mpr hi),
    fun i hi => hb i ((hmem i).mpr hi),
    fun i j hi hj hij => hc i ((hmem i).mpr hi) j ((hmem j).mpr hj) hij,
    fun i hi => ht i ((hmem i).mpr hi)⟩

end FiniteAvalanches.Electrical.StatementGeometry
