import FiniteAvalanches.Wilson.Lattice.OriginWiredTerminalCoupling

/-! High-probability coupling events for finite wired forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Safe origin and origin-plus-sink explorations with terminal continuations. -/
def originWiredCouplingEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    Set ((p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1) :=
  {σ | σ ∈ originSafeTerminalEvent B x k n ∧
    ∃ u, Relation.ReflTransGen (pop_step (wiredOriginAndSink B)
        (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k u ∧
      terminal (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i)) u}

/-- Adding the second terminal continuation does not change the event's probability. -/
theorem originWiredCouplingEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B)) (originWiredCouplingEvent B x k n) =
      variableStackLaw (IncidentCopy (WiredTrees.graph B)) (originSafeTerminalEvent B x k n) := by
  apply measure_congr
  filter_upwards [variableStackLaw_ae_wiredOriginAndSink_terminal B k] with σ hσ
  exact propext ⟨fun h => h.1, fun h => ⟨h, hσ⟩⟩

/-- The two finite terminal forests can be coupled on an arbitrary fixed
finite exploration with probability tending to one as the wired box grows. -/
theorem originWiredCouplingEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B))
    (hk : ∀ B, kb B none = 0) (n : ℕ) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (originWiredCouplingEvent B x (kb B) n)) atTop (nhds 1) := by
  have he : (fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (originWiredCouplingEvent B x (kb B) n)) =
      fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
        (originSafeTerminalEvent B x (kb B) n) := by
    funext B
    exact originWiredCouplingEvent_measure B x (kb B) n
  rw [he]
  exact originSafeTerminalEvent_tendsto_one x ka kb hk n

/-- On the coupling event the two terminal forests agree on every active copied
edge whose endpoints belong to the explored prefix. -/
theorem originWiredCouplingEvent_agreement (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originWiredCouplingEvent B x k n) :
    ∃ T : Set (FiniteWired.Vertex B), ∃ t u,
      ∃ ht : terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
        (fun v i => σ (v, i)) t,
      ∃ hu : terminal (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B))
        (fun v i => σ (v, i)) u,
      Relation.ReflTransGen (pop_step (wiredOriginRoot B)
        (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t ∧
      Relation.ReflTransGen (pop_step (wiredOriginAndSink B)
        (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k u ∧
      (∀ i < n, wiredSite B (x i) ∈ T) ∧
      ∀ e : FiniteWired.Edge B, (WiredTrees.graph B).left e ∈ T →
        (WiredTrees.graph B).right e ∈ T →
        (WiredTrees.graph B).left e ≠ none → (WiredTrees.graph B).right e ≠ none →
        (e ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ↔
          e ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginAndSink B)
            ⟨fun v => σ (v, u v), hu⟩) := by
  obtain ⟨⟨hsafe, t, htRun, ht⟩, u, huRun, hu⟩ := hσ
  obtain ⟨T, hcover, hagree⟩ := originSafe_terminalCopies_agree B x k t u n σ
    hsafe htRun ht huRun hu
  exact ⟨T, t, u, ht, hu, htRun, huRun, hcover, hagree⟩

end
end FiniteAvalanches.Wilson.Lattice
