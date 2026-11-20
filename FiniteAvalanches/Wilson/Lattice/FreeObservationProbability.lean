import FiniteAvalanches.Wilson.Lattice.FreeObservationEvent

/-! Probability bounds for coupled free-box edge observations. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal symmDiff

noncomputable section

local instance decEqInteriorEdgeFreeObservationProbability (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- Projecting incident stacks to inner-box lattice directions is measurable. -/
theorem measurable_freeInteriorDirectionStacks (B : ℕ) :
    Measurable (freeInteriorDirectionStacks B) := by
  apply measurable_pi_iff.mpr
  intro q
  exact (measurable_of_finite (freeInteriorDirectionEquiv B q.1.val q.1.property).symm).comp
    (measurable_pi_apply (q.1.val, q.2))

/-- The incident-stack safe history is measurable. -/
theorem measurableSet_freeSafeIncidentStackEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    MeasurableSet (freeSafeIncidentStackEvent B x k n) :=
  (measurableSet_freeSafeStackHistoryEvent B x k n).preimage
    ((measurable_padFreeInteriorStacks B).comp (measurable_freeInteriorDirectionStacks B))

/-- Terminal incident-stack configurations form a measurable event. -/
theorem measurableSet_freeIncidentTerminalEvent (B : ℕ) (R : Set (FiniteWired.Active (B + 1)))
    (k : Cursor (FiniteWired.Active (B + 1))) :
    MeasurableSet (terminalEvent R (incidentCopyHead (freeBoxGraph (B + 1))) k
      (fun v i (σ : (q : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) q.1) =>
        σ (v, i))) := by
  rw [terminalEvent_eq_iUnion]
  apply MeasurableSet.iUnion
  intro a
  apply measurableSet_terminalOutputEvent
  intro v i
  exact measurable_pi_apply (v, i)

/-- The safe event with both terminal continuations is measurable. -/
theorem measurableSet_freeCouplingEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    MeasurableSet (freeCouplingEvent B x k n) := by
  change MeasurableSet (freeSafeIncidentStackEvent B x k n ∩
    (terminalEvent (freeOriginRoot B) (incidentCopyHead (freeBoxGraph (B + 1))) k
      (fun v i σ => σ (v, i)) ∩
    terminalEvent (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1))) k
      (fun v i σ => σ (v, i))))
  exact (measurableSet_freeSafeIncidentStackEvent B x k n).inter
    ((measurableSet_freeIncidentTerminalEvent B (freeOriginRoot B) k).inter
      (measurableSet_freeIncidentTerminalEvent B (freeOriginAndBoundary B) k))

/-- The discrepancy between the coupled edge events is contained in the
complement of the safe coupling event. -/
theorem freeIncidentStackEdgeEvent_symmDiff_le (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hbox : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox B z) :
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeIncidentStackEdgeEvent B (freeOriginRoot B) k E p ∆
        freeIncidentStackEdgeEvent B (freeOriginAndBoundary B) k E p) ≤
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1))) (freeCouplingEvent B x k n)ᶜ := by
  apply measure_mono
  intro σ hσ hgood
  have he := freeCouplingEvent_edgeEvent_iff B x k n E p hE hbox σ hgood
  rcases hσ with h | h
  · exact h.2 (he.mp h.1)
  · exact h.2 (he.mpr h.1)

/-- The two finite edge observations disagree with probability tending to zero. -/
theorem freeIncidentStackEdgeEvent_symmDiff_tendsto_zero (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ B v, v ∈ freeOuterBoundary B → kb B v = 0) (n : ℕ) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeIncidentStackEdgeEvent B (freeOriginRoot B) (kb B) E p ∆
        freeIncidentStackEdgeEvent B (freeOriginAndBoundary B) (kb B) E p)) atTop (nhds 0) := by
  have hgood := freeCouplingEvent_tendsto_one x ka kb hk n
  have hbad : Tendsto (fun B => variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeCouplingEvent B x (kb B) n)ᶜ) atTop (nhds 0) := by
    have h := ENNReal.Tendsto.sub tendsto_const_nhds hgood (Or.inl (by simp : (1 : ℝ≥0∞) ≠ ⊤))
    simp only [tsub_self] at h
    convert h using 1
    funext B
    rw [measure_compl (measurableSet_freeCouplingEvent B x (kb B) n)
      (measure_ne_top _ _), measure_univ]
  have hbox : ∀ᶠ B : ℕ in atTop, ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox B z := by
    filter_upwards [eventually_all.mpr (fun i : Fin n => eventually_finiteWired_inBox (x i.val))] with B hB
    intro e he z hz
    obtain ⟨i, hi, hix⟩ := hE e he z hz
    rw [← hix]
    exact hB ⟨i, hi⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [hbox] with B hB
  exact freeIncidentStackEdgeEvent_symmDiff_le B x (kb B) n E p hE hB

end
end FiniteAvalanches.Wilson.Lattice
