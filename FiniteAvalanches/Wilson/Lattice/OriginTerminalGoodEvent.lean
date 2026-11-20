import FiniteAvalanches.Wilson.Lattice.OriginSafeTerminalPrefix

/-! Safe origin-rooted prefixes with terminal spanning-tree continuations. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Every wired box has a cycle-free incident assignment rooted at its origin. -/
theorem wiredOrigin_goodIncidentArrows_nonempty (B : ℕ) :
    Nonempty (GoodIncidentArrows (WiredTrees.graph B) (wiredOriginRoot B)) := by
  let F := (singletonRootedForestEquiv (WiredTrees.graph B) (some (wiredOrigin B))).symm
    (WiredTrees.rowTree B)
  exact ⟨forestIncidentArrows (WiredTrees.graph B) (wiredOriginRoot B) F⟩

/-- Origin-rooted incident cycle popping terminates almost surely in each box. -/
theorem variableStackLaw_ae_wiredOrigin_terminal (B : ℕ) (k : Cursor (FiniteWired.Vertex B)) :
    ∀ᵐ σ ∂variableStackLaw (IncidentCopy (WiredTrees.graph B)),
      ∃ t, Relation.ReflTransGen (pop_step (wiredOriginRoot B)
          (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t ∧
        terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
          (fun v i => σ (v, i)) t := by
  obtain ⟨a⟩ := wiredOrigin_goodIncidentArrows_nonempty B
  exact variableStackLaw_ae_terminates (IncidentCopy (WiredTrees.graph B))
    (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B)) k a

/-- Safe finite incident-stack exploration with an actual terminal continuation. -/
def originSafeTerminalEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    Set ((p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1) :=
  {σ | σ ∈ originSafeIncidentStackEvent B x k n ∧
    ∃ t, Relation.ReflTransGen (pop_step (wiredOriginRoot B)
        (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t ∧
      terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i)) t}

/-- Requiring the terminal continuation does not change the safe-event probability. -/
theorem originSafeTerminalEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B)) (originSafeTerminalEvent B x k n) =
      variableStackLaw (IncidentCopy (WiredTrees.graph B)) (originSafeIncidentStackEvent B x k n) := by
  apply measure_congr
  filter_upwards [variableStackLaw_ae_wiredOrigin_terminal B k] with σ hσ
  exact propext ⟨fun h => h.1, fun h => ⟨h, hσ⟩⟩

/-- Safe finite prefixes with terminal continuations have probability tending to one. -/
theorem originSafeTerminalEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B))
    (hk : ∀ B, kb B none = 0) (n : ℕ) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (originSafeTerminalEvent B x (kb B) n)) atTop (nhds 1) := by
  have he : (fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (originSafeTerminalEvent B x (kb B) n)) =
      fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
        (originSafeIncidentStackEvent B x (kb B) n) := by
    funext B
    exact originSafeTerminalEvent_measure B x (kb B) n
  rw [he]
  exact originSafeIncidentStackEvent_tendsto_one x ka kb hk n

/-- Every queried vertex is attached in a safe origin-rooted prefix, and
terminal copied edges between attached vertices are determined by that prefix. -/
theorem originSafeTerminalEvent_prefix (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originSafeTerminalEvent B x k n) :
    ∃ T j t, ∃ ht : terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
        (fun v i => σ (v, i)) t,
      stackExplore (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))
        (wiredOriginAndSink B) k ((List.range n).map fun i => wiredSite B (x i)) =
          some (wiredOriginAndSink B ∪ T, j) ∧
      (∀ i < n, wiredSite B (x i) ∈ T) ∧
      ∀ e : FiniteWired.Edge B, (WiredTrees.graph B).left e ∈ T →
        (WiredTrees.graph B).right e ∈ T →
        (e ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ↔
          ∃ v ∈ T, v ∉ wiredOriginRoot B ∧ (σ (v, j v)).val = e) := by
  obtain ⟨hsafe, t, hrun, ht⟩ := hσ
  obtain ⟨T, j, hsmall, hlarge, _⟩ := originSafeIncidentStackEvent_explorations B x k n σ hsafe
  have hcover := (stackExplore_of_some (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
    (fun v i => σ (v, i)) k ((List.range n).map fun i => wiredSite B (x i)) T j hsmall).2.1
  refine ⟨T, j, t, ht, hlarge, ?_, ?_⟩
  · intro i hi
    exact hcover _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · intro e he1 he2
    exact terminal_incidentCopy_mem_iff_prefix (WiredTrees.graph B) (wiredOriginRoot B)
      (fun v i => σ (v, i)) k t ((List.range n).map fun i => wiredSite B (x i)) T j
      hrun ht hsmall e he1 he2

end
end FiniteAvalanches.Wilson.Lattice
