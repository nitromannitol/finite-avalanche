import FiniteAvalanches.Wilson.Lattice.OriginWiredObservationEvent

/-! Probability bounds for coupled wired edge observations. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal symmDiff

noncomputable section

/-- Projecting incident stacks to active lattice directions is measurable. -/
theorem measurable_wiredActiveDirectionStacks (B : ℕ) :
    Measurable (wiredActiveDirectionStacks B) := by
  apply measurable_pi_iff.mpr
  intro q
  exact (measurable_of_finite (wiredActiveCopyEquiv q.1).symm).comp
    (measurable_pi_apply (some q.1, q.2))

/-- The incident-stack safe history is measurable. -/
theorem measurableSet_originSafeIncidentStackEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    MeasurableSet (originSafeIncidentStackEvent B x k n) :=
  (measurableSet_originSafeStackHistoryEvent B x k n).preimage
    ((measurable_padActiveDirectionStacks B).comp (measurable_wiredActiveDirectionStacks B))

/-- Terminal incident-stack configurations form a measurable event. -/
theorem measurableSet_incidentTerminalEvent (B : ℕ) (R : Set (FiniteWired.Vertex B))
    (k : Cursor (FiniteWired.Vertex B)) :
    MeasurableSet (terminalEvent R (incidentCopyHead (WiredTrees.graph B)) k
      (fun v i (σ : (q : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) q.1) =>
        σ (v, i))) := by
  rw [terminalEvent_eq_iUnion]
  apply MeasurableSet.iUnion
  intro a
  apply measurableSet_terminalOutputEvent
  intro v i
  exact measurable_pi_apply (v, i)

/-- The safe event with both terminal continuations is measurable. -/
theorem measurableSet_originWiredCouplingEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    MeasurableSet (originWiredCouplingEvent B x k n) := by
  change MeasurableSet (originSafeIncidentStackEvent B x k n ∩
    terminalEvent (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B)) k
      (fun v i σ => σ (v, i)) ∩
    terminalEvent (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B)) k
      (fun v i σ => σ (v, i)))
  exact ((measurableSet_originSafeIncidentStackEvent B x k n).inter
    (measurableSet_incidentTerminalEvent B (wiredOriginRoot B) k)).inter
      (measurableSet_incidentTerminalEvent B (wiredOriginAndSink B) k)

/-- The discrepancy between the coupled edge events is contained in the
complement of the safe coupling event. -/
theorem incidentStackEdgeEvent_symmDiff_le (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (incidentStackEdgeEvent B (wiredOriginRoot B) k E p ∆
        incidentStackEdgeEvent B (wiredOriginAndSink B) k E p) ≤
    variableStackLaw (IncidentCopy (WiredTrees.graph B)) (originWiredCouplingEvent B x k n)ᶜ := by
  apply measure_mono
  intro σ hσ hgood
  have he := originWiredCouplingEvent_edgeEvent_iff B x k n E p hE σ hgood
  rcases hσ with h | h
  · exact h.2 (he.mp h.1)
  · exact h.2 (he.mpr h.1)

/-- The two finite edge observations disagree with probability tending to zero. -/
theorem incidentStackEdgeEvent_symmDiff_tendsto_zero (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B))
    (hk : ∀ B, kb B none = 0) (n : ℕ) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (incidentStackEdgeEvent B (wiredOriginRoot B) (kb B) E p ∆
        incidentStackEdgeEvent B (wiredOriginAndSink B) (kb B) E p)) atTop (nhds 0) := by
  have hgood := originWiredCouplingEvent_tendsto_one x ka kb hk n
  have hbad : Tendsto (fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (originWiredCouplingEvent B x (kb B) n)ᶜ) atTop (nhds 0) := by
    have h := ENNReal.Tendsto.sub tendsto_const_nhds hgood (Or.inl (by simp : (1 : ℝ≥0∞) ≠ ⊤))
    simp only [tsub_self] at h
    convert h using 1
    funext B
    rw [measure_compl (measurableSet_originWiredCouplingEvent B x (kb B) n)
      (measure_ne_top _ _), measure_univ]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad
    (fun _ => bot_le) (fun B => incidentStackEdgeEvent_symmDiff_le B x (kb B) n E p hE)

end
end FiniteAvalanches.Wilson.Lattice
