import FiniteAvalanches.Wilson.Lattice.WiredDualFaceSafeTerminal

/-! High-probability couplings of face-square terminal forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Safe face exploration with origin and origin-plus-boundary terminal continuations. -/
def wiredDualFaceCouplingEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    Set ((p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1) :=
  {σ | σ ∈ wiredDualFaceSafeIncidentStackEvent B x k n ∧
    (∃ t, Relation.ReflTransGen (pop_step {wiredDualFaceOrigin (B + 1)}
        (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k t ∧
      terminal {wiredDualFaceOrigin (B + 1)} (incidentCopyHead (wiredDualFaceGraph (B + 1)))
        (fun v i => σ (v, i)) t) ∧
    ∃ u, Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B)
        (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k u ∧
      terminal (wiredDualFaceOriginAndBoundary B) (incidentCopyHead (wiredDualFaceGraph (B + 1)))
        (fun v i => σ (v, i)) u}

/-- Almost-sure terminal continuations preserve the safe-event probability. -/
theorem wiredDualFaceCouplingEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1))) (wiredDualFaceCouplingEvent B x k n) =
      variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
        (wiredDualFaceSafeIncidentStackEvent B x k n) := by
  apply measure_congr
  filter_upwards [variableStackLaw_ae_wiredDualFaceOrigin_terminates (B + 1) k,
    variableStackLaw_ae_wiredDualFaceOriginAndBoundary_terminates B k] with σ hσ hτ
  exact propext ⟨fun h => h.1, fun h => ⟨h, hσ, hτ⟩⟩

/-- The face terminal forests couple on a fixed prefix with probability tending to one. -/
theorem wiredDualFaceCouplingEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1)))
    (hk : ∀ B v, v ∈ wiredDualFaceOuterBoundary B → kc B v = 0) (n : ℕ) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      (wiredDualFaceCouplingEvent B x (kc B) n)) atTop (nhds 1) := by
  have he : (fun B => variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      (wiredDualFaceCouplingEvent B x (kc B) n)) =
      fun B => variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
        (wiredDualFaceSafeIncidentStackEvent B x (kc B) n) := by
    funext B
    exact wiredDualFaceCouplingEvent_measure B x (kc B) n
  rw [he]
  exact wiredDualFaceSafeIncidentStackEvent_tendsto_one x ka kb kc hk n

/-- On the coupling event, terminal forests agree on attached interior copies. -/
theorem wiredDualFaceCouplingEvent_agreement (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (hσ : σ ∈ wiredDualFaceCouplingEvent B x k n) :
    ∃ T : Set (WiredDualFace (B + 1)), ∃ t u,
      ∃ ht : terminal {wiredDualFaceOrigin (B + 1)} (incidentCopyHead (wiredDualFaceGraph (B + 1)))
        (fun v i => σ (v, i)) t,
      ∃ hu : terminal (wiredDualFaceOriginAndBoundary B) (incidentCopyHead (wiredDualFaceGraph (B + 1)))
        (fun v i => σ (v, i)) u,
      Relation.ReflTransGen (pop_step {wiredDualFaceOrigin (B + 1)}
        (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k t ∧
      Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B)
        (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k u ∧
      (∀ i < n, wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)) ∈ T) ∧
      ∀ e : FiniteWired.Edge (B + 1), (wiredDualFaceGraph (B + 1)).left e ∈ T →
        (wiredDualFaceGraph (B + 1)).right e ∈ T →
        (wiredDualFaceGraph (B + 1)).left e ∉ wiredDualFaceOuterBoundary B →
        (wiredDualFaceGraph (B + 1)).right e ∉ wiredDualFaceOuterBoundary B →
        (e ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) {wiredDualFaceOrigin (B + 1)}
            ⟨fun v => σ (v, t v), ht⟩ ↔
          e ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) (wiredDualFaceOriginAndBoundary B)
            ⟨fun v => σ (v, u v), hu⟩) := by
  obtain ⟨hsafe, ⟨t, htRun, ht⟩, u, huRun, hu⟩ := hσ
  obtain ⟨T, hcover, hagree⟩ := wiredDualFaceSafe_terminalCopies_agree B x k t u n σ
    hsafe htRun ht huRun hu
  exact ⟨T, t, u, ht, hu, htRun, huRun, hcover, hagree⟩

end
end FiniteAvalanches.Wilson.Lattice
