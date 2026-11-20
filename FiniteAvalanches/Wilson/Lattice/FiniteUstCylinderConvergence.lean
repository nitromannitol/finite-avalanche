import FiniteAvalanches.Wilson.Lattice.DistantOriginWiredConvergence
import FiniteAvalanches.Wilson.Lattice.OriginWiredFiniteLaw

/-! Convergence of finite wired spanning tree edge cylinders. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal symmDiff

noncomputable section

/-- The finite wired UST cylinder probability tends to the probability of the
corresponding finite origin-rooted Wilson exploration. -/
theorem finiteLaw_cylinder_tendsto_originSampler (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B))
    (hk : ∀ B, kb B none = 0) (n : ℕ) (E : Finset LatticeEdge) (p : E → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) :
    Tendsto (fun B => finiteLaw B (cylinder E p)) atTop
      (nhds (wilsonRows (originSamplerEvent ((List.range n).map x) E
        (fun e => if h : e ∈ E then p ⟨e, h⟩ else false)))) := by
  let q : LatticeEdge → Bool := fun e => if h : e ∈ E then p ⟨e, h⟩ else false
  let μ := fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
  let A := fun B => incidentStackEdgeEvent B (wiredOriginRoot B) (kb B) E q
  let C := fun B => incidentStackEdgeEvent B (wiredOriginAndSink B) (kb B) E q
  let a := wilsonRows (originSamplerEvent ((List.range n).map x) E q)
  have hC : Tendsto (fun B => μ B (C B)) atTop (nhds a) := by
    have h := distantOrigin_finiteForestLaw_edge_tendsto x ka kb n E q hE
    have he : (fun B => μ B (C B)) = fun B => finiteForestLaw (distantOriginRootPair B) B
        (jointEvent E ∅ q (fun _ => false)) := by
      funext B
      exact variableStackLaw_originSinkEdgeEvent_eq_finiteForestLaw B (kb B) E p
    rwa [he]
  have hdiff : Tendsto (fun B => μ B (A B ∆ C B)) atTop (nhds 0) :=
    incidentStackEdgeEvent_symmDiff_tendsto_zero x ka kb hk n E q hE
  have hCReal : Tendsto (fun B => (μ B (C B)).toReal) atTop (nhds a.toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hC
  have hdiffReal : Tendsto (fun B => (μ B (A B ∆ C B)).toReal) atTop (nhds 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdiff
  have hdist : Tendsto (fun B => dist (μ B (C B)).toReal (μ B (A B)).toReal) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) ?_ hdiffReal
    intro B
    have h := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ B)
      (measurableSet_incidentStackEdgeEvent B (wiredOriginAndSink B) (kb B) E q).nullMeasurableSet
      (measurableSet_incidentStackEdgeEvent B (wiredOriginRoot B) (kb B) E q).nullMeasurableSet
    change |(μ B (C B)).toReal - (μ B (A B)).toReal| ≤ (μ B (C B ∆ A B)).toReal at h
    rw [symmDiff_comm] at h
    rw [Real.dist_eq]
    exact h
  have hAReal := hCReal.congr_dist hdist
  have hA : Tendsto (fun B => μ B (A B)) atTop (nhds a) :=
    (ENNReal.tendsto_toReal_iff (fun B => measure_ne_top (μ B) (A B))
      (measure_ne_top _ _)).mp hAReal
  have he : (fun B => μ B (A B)) = fun B => finiteLaw B (cylinder E p) := by
    funext B
    exact variableStackLaw_originEdgeEvent_eq_finiteLaw B (kb B) E p
  rwa [he] at hA

/-- Every finite wired UST cylinder has a limiting probability. -/
theorem finiteLaw_cylinder_converges (E : Finset LatticeEdge) (p : E → Bool) :
    ∃ a : ℝ≥0∞, Tendsto (fun B => finiteLaw B (cylinder E p)) atTop (nhds a) := by
  obtain ⟨x, n, hE, _⟩ := exists_finite_queries E ∅
  exact ⟨_, finiteLaw_cylinder_tendsto_originSampler x (fun _ => 0) (fun _ _ => 0)
    (fun _ => rfl) n E p hE⟩

end
end FiniteAvalanches.Wilson.Lattice
