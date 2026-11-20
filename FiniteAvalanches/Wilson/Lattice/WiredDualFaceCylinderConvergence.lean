import FiniteAvalanches.Wilson.Lattice.WiredDualFaceBoundaryRowLimit
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceFiniteLaw
import FiniteAvalanches.Wilson.Lattice.FiniteUstCylinderConvergence

/-! Shifted face-square spanning-tree cylinders converge to the wired limit. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal symmDiff

noncomputable section

local instance decEqWiredEdgeDualFaceCylinderConvergence (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- The face-square tree cylinder tends to the origin-rooted Wilson exploration probability. -/
theorem wiredDualFaceLaw_cylinder_tendsto_originSampler (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1)))
    (hk : ∀ B v, v ∈ wiredDualFaceOuterBoundary B → kc B v = 0) (n : ℕ)
    (E : Finset LatticeEdge) (p : E → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) :
    Tendsto (fun B => wiredDualFaceLaw (B + 1) (cylinder E p)) atTop
      (nhds (wilsonRows (originSamplerEvent ((List.range n).map x) E
        (fun e => if h : e ∈ E then p ⟨e, h⟩ else false)))) := by
  let q : LatticeEdge → Bool := fun e => if h : e ∈ E then p ⟨e, h⟩ else false
  let μ := fun B => variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
  let A := fun B => wiredDualFaceIncidentStackEdgeEvent B {wiredDualFaceOrigin (B + 1)} (kc B) E q
  let C := fun B => wiredDualFaceIncidentStackEdgeEvent B (wiredDualFaceOriginAndBoundary B) (kc B) E q
  let a := wilsonRows (originSamplerEvent ((List.range n).map x) E q)
  have hC : Tendsto (fun B => μ B (C B)) atTop (nhds a) := by
    have h := wiredDualFaceBoundaryRowEdgeEvent_tendsto x ka kb kc n E q
    apply h.congr'
    filter_upwards [eventually_all.mpr (fun i : Fin n => eventually_finiteWired_inBox (x i.val))] with B hbox
    have hebox : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox (B + 1) z := by
      intro e he z hz d
      obtain ⟨i, hi, hix⟩ := hE e he z hz
      have hb := hbox ⟨i, hi⟩ d
      rw [hix] at hb
      constructor <;> omega
    have hrep : ∀ e ∈ E, ∃ i : FiniteWired.Edge (B + 1), wiredCopyDualEdge i = e := by
      intro e he
      apply (dualFaceEdge_iff_wiredCopy (B + 1) e).mp
      intro z hz
      exact inDualFaceBox_of_inBox (B + 1) z (hebox e he z hz)
    exact (variableStackLaw_wiredDualFaceBoundaryEdgeEvent_eq_wilsonRows B x (kc B) (hk B)
      n E q hE hebox hrep).symm
  have hdiff : Tendsto (fun B => μ B (A B ∆ C B)) atTop (nhds 0) :=
    wiredDualFaceIncidentStackEdgeEvent_symmDiff_tendsto_zero x ka kb kc hk n E q hE
  have hCReal : Tendsto (fun B => (μ B (C B)).toReal) atTop (nhds a.toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hC
  have hdiffReal : Tendsto (fun B => (μ B (A B ∆ C B)).toReal) atTop (nhds 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdiff
  have hdist : Tendsto (fun B => dist (μ B (C B)).toReal (μ B (A B)).toReal) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) ?_ hdiffReal
    intro B
    have h := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ B)
      (measurableSet_wiredDualFaceIncidentStackEdgeEvent B (wiredDualFaceOriginAndBoundary B) (kc B) E q).nullMeasurableSet
      (measurableSet_wiredDualFaceIncidentStackEdgeEvent B {wiredDualFaceOrigin (B + 1)} (kc B) E q).nullMeasurableSet
    change |(μ B (C B)).toReal - (μ B (A B)).toReal| ≤ (μ B (C B ∆ A B)).toReal at h
    rw [symmDiff_comm] at h
    rw [Real.dist_eq]
    exact h
  have hAReal := hCReal.congr_dist hdist
  have hA : Tendsto (fun B => μ B (A B)) atTop (nhds a) :=
    (ENNReal.tendsto_toReal_iff (fun B => measure_ne_top (μ B) (A B))
      (measure_ne_top _ _)).mp hAReal
  have he : (fun B => μ B (A B)) = fun B => wiredDualFaceLaw (B + 1) (cylinder E p) := by
    funext B
    exact variableStackLaw_wiredDualFaceOriginEdgeEvent_eq_law B (kc B) E p
  rwa [he] at hA

/-- Every shifted face-square tree cylinder converges to any weak wired UST limit. -/
theorem wiredDualFaceLaw_cylinder_tendsto_wiredLimit (ν : ProbabilityMeasure EdgeField)
    (hν : Tendsto finiteProbability atTop (nhds ν)) (E : Finset LatticeEdge) (p : E → Bool) :
    Tendsto (fun B => wiredDualFaceLaw (B + 1) (cylinder E p)) atTop
      (nhds ((ν : Measure EdgeField) (cylinder E p))) := by
  obtain ⟨x, n, hE, _⟩ := exists_finite_queries E ∅
  have hf := wiredDualFaceLaw_cylinder_tendsto_originSampler x (fun _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ _ => rfl) n E p hE
  have hw := finiteLaw_cylinder_tendsto_originSampler x (fun _ => 0) (fun _ _ => 0)
    (fun _ => rfl) n E p hE
  have hνc := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hν
    (E := cylinder E p) (by rw [(isClopen_cylinder E p).frontier_eq]; exact measure_empty)
  rw [tendsto_nhds_unique hw hνc] at hf
  exact hf

end
end FiniteAvalanches.Wilson.Lattice
