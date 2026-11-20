import FiniteAvalanches.Wilson.Lattice.OriginTerminalGoodEvent
import FiniteAvalanches.Wilson.CyclePopping.NestedRootTerminalCopies

/-! Coupling origin-rooted and wired-rooted finite forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The origin is one of the two wired roots. -/
theorem wiredOriginRoot_subset (B : ℕ) : wiredOriginRoot B ⊆ wiredOriginAndSink B := by
  intro v hv
  simp only [wiredOriginRoot, Set.mem_singleton_iff] at hv
  subst v
  simp [wiredOriginAndSink]

/-- A safe exploration couples terminal forests rooted at the origin and at
both the origin and sink on attached edges with active endpoints. -/
theorem originSafe_terminalCopies_agree (B : ℕ) (x : ℕ → Site 2)
    (k t u : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originSafeIncidentStackEvent B x k n)
    (hrun : Relation.ReflTransGen (pop_step (wiredOriginRoot B)
      (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t)
    (ht : terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i)) t)
    (hsrun : Relation.ReflTransGen (pop_step (wiredOriginAndSink B)
      (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k u)
    (hu : terminal (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i)) u) :
    ∃ T : Set (FiniteWired.Vertex B), (∀ i < n, wiredSite B (x i) ∈ T) ∧
      ∀ e : FiniteWired.Edge B, (WiredTrees.graph B).left e ∈ T →
        (WiredTrees.graph B).right e ∈ T →
        (WiredTrees.graph B).left e ≠ none → (WiredTrees.graph B).right e ≠ none →
        (e ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ↔
          e ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginAndSink B)
            ⟨fun v => σ (v, u v), hu⟩) := by
  obtain ⟨T, j, hsmall, hlarge, _⟩ := originSafeIncidentStackEvent_explorations B x k n σ hσ
  have hcover := (stackExplore_of_some (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
    (fun v i => σ (v, i)) k ((List.range n).map fun i => wiredSite B (x i)) T j hsmall).2.1
  refine ⟨T, ?_, ?_⟩
  · intro i hi
    exact hcover _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · intro e he1 he2 hne1 hne2
    apply terminal_incidentCopy_mem_iff_of_nested_prefix (WiredTrees.graph B)
      (wiredOriginRoot B) (wiredOriginAndSink B) (wiredOriginRoot_subset B)
      (fun v i => σ (v, i)) k t u _ T j hrun ht hsrun hu hsmall hlarge e he1 he2
    all_goals
      intro hv
      simp only [wiredOriginAndSink, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with h | h
      · contradiction
      · simpa [wiredOriginRoot] using h

/-- The origin-and-sink incident-stack sampler terminates almost surely. -/
theorem variableStackLaw_ae_wiredOriginAndSink_terminal (B : ℕ)
    (k : Cursor (FiniteWired.Vertex B)) :
    ∀ᵐ σ ∂variableStackLaw (IncidentCopy (WiredTrees.graph B)),
      ∃ t, Relation.ReflTransGen (pop_step (wiredOriginAndSink B)
          (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t ∧
        terminal (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B))
          (fun v i => σ (v, i)) t := by
  obtain ⟨a⟩ := wiredOrigin_goodIncidentArrows_nonempty B
  have ha : GoodIncidentArrows (WiredTrees.graph B) (wiredOriginAndSink B) :=
    ⟨a.val, terminal_mono_roots (wiredOriginRoot B) (wiredOriginAndSink B)
      (incidentCopyHead (WiredTrees.graph B)) (fun v _ => a.val v) 0
      (wiredOriginRoot_subset B) a.property⟩
  exact variableStackLaw_ae_terminates (IncidentCopy (WiredTrees.graph B))
    (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B)) k ha

end
end FiniteAvalanches.Wilson.Lattice
