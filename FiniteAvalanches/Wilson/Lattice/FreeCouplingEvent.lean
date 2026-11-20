import FiniteAvalanches.Wilson.Lattice.FreeBoxLaw

/-! High-probability couplings of free-box terminal forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeCouplingEvent (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- Safe origin and origin-plus-boundary explorations with terminal continuations. -/
def freeCouplingEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    Set ((p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1) :=
  {σ | σ ∈ freeSafeIncidentStackEvent B x k n ∧
    (∃ t, Relation.ReflTransGen (pop_step (freeOriginRoot B)
        (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t ∧
      terminal (freeOriginRoot B) (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i)) t) ∧
    ∃ u, Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
        (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k u ∧
      terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i)) u}

/-- Adding almost-sure terminal continuations preserves the safe-event probability. -/
theorem freeCouplingEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1))) (freeCouplingEvent B x k n) =
      variableStackLaw (IncidentCopy (freeBoxGraph (B + 1))) (freeSafeIncidentStackEvent B x k n) := by
  apply measure_congr
  filter_upwards [variableStackLaw_ae_freeOrigin_terminates B k,
    variableStackLaw_ae_freeOriginAndBoundary_terminal B k] with σ hσ hτ
  exact propext ⟨fun h => h.1, fun h => ⟨h, hσ, hτ⟩⟩

/-- The free terminal forests couple on a fixed prefix with probability tending to one. -/
theorem freeCouplingEvent_tendsto_one (x : ℕ → Site 2) (ka : Cursor (Site 2))
    (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ B v, v ∈ freeOuterBoundary B → kb B v = 0) (n : ℕ) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeCouplingEvent B x (kb B) n)) atTop (nhds 1) := by
  have he : (fun B => variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeCouplingEvent B x (kb B) n)) =
      fun B => variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
        (freeSafeIncidentStackEvent B x (kb B) n) := by
    funext B
    exact freeCouplingEvent_measure B x (kb B) n
  rw [he]
  exact freeSafeIncidentStackEvent_tendsto_one x ka kb hk n

/-- On the coupling event the terminal forests agree on attached inner copies. -/
theorem freeCouplingEvent_agreement (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (hσ : σ ∈ freeCouplingEvent B x k n) :
    ∃ T : Set (FiniteWired.Active (B + 1)), ∃ t u,
      ∃ ht : terminal (freeOriginRoot B) (incidentCopyHead (freeBoxGraph (B + 1)))
        (fun v i => σ (v, i)) t,
      ∃ hu : terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1)))
        (fun v i => σ (v, i)) u,
      Relation.ReflTransGen (pop_step (freeOriginRoot B)
        (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t ∧
      Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
        (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k u ∧
      (∀ i < n, freeSite (B + 1) (x i) ∈ T) ∧
      ∀ e : FiniteWired.InteriorEdge (B + 1), (freeBoxGraph (B + 1)).left e ∈ T →
        (freeBoxGraph (B + 1)).right e ∈ T →
        (freeBoxGraph (B + 1)).left e ∉ freeOuterBoundary B →
        (freeBoxGraph (B + 1)).right e ∉ freeOuterBoundary B →
        (e ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ↔
          e ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginAndBoundary B)
            ⟨fun v => σ (v, u v), hu⟩) := by
  obtain ⟨hsafe, ⟨t, htRun, ht⟩, u, huRun, hu⟩ := hσ
  obtain ⟨T, hcover, hagree⟩ := freeSafe_terminalCopies_agree B x k t u n σ
    hsafe htRun ht huRun hu
  exact ⟨T, t, u, ht, hu, htRun, huRun, hcover, hagree⟩

end
end FiniteAvalanches.Wilson.Lattice
