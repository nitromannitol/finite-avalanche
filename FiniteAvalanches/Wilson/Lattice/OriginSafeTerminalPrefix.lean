import FiniteAvalanches.Wilson.Lattice.OriginSafeIncidentLaw
import FiniteAvalanches.Wilson.CyclePopping.TerminalPrefixCopies

/-! Origin-rooted wired spanning trees and safe finite prefixes. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The singleton original root at the lattice origin in a wired box. -/
def wiredOriginRoot (B : ℕ) : Set (FiniteWired.Vertex B) := {some (wiredOrigin B)}

/-- A safe incident-stack prefix has the same output whether it is stopped at
the origin alone or at the origin together with the sink. -/
theorem originSafeIncidentStackEvent_explorations (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originSafeIncidentStackEvent B x k n) :
    ∃ T j, stackExplore (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))
        (wiredOriginRoot B) k ((List.range n).map fun i => wiredSite B (x i)) = some (T, j) ∧
      stackExplore (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))
        (wiredOriginAndSink B) k ((List.range n).map fun i => wiredSite B (x i)) =
          some (wiredOriginAndSink B ∪ T, j) ∧ wiredOriginRoot B ⊆ T := by
  have hRS : wiredOriginRoot B ⊆ wiredOriginAndSink B := by
    intro v hv
    simp only [wiredOriginRoot, Set.mem_singleton_iff] at hv
    subst v
    simp only [wiredOriginAndSink, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  have hSD : wiredOriginAndSink B ⊆ wiredOriginRoot B ∪ {none} := by
    intro v hv
    simp only [wiredOriginAndSink, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  exact stackExplore_eq_of_avoidsExtraRoots (incidentCopyHead (WiredTrees.graph B))
    (fun v i => σ (v, i)) (wiredOriginRoot B) (wiredOriginAndSink B) {none} k _ hRS hSD
    (originSafeIncidentStackEvent_avoids_sink B x k n σ hσ)

/-- On a safe prefix, any original copied edge whose endpoints were attached has
terminal-tree membership determined by the prefix's visible outgoing copies. -/
theorem originSafe_terminalCopy_mem_iff_prefix (B : ℕ) (x : ℕ → Site 2)
    (k t : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originSafeIncidentStackEvent B x k n)
    (hrun : Relation.ReflTransGen (pop_step (wiredOriginRoot B)
      (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t)
    (ht : terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i)) t) :
    ∃ T j, stackExplore (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))
        (wiredOriginAndSink B) k ((List.range n).map fun i => wiredSite B (x i)) =
          some (wiredOriginAndSink B ∪ T, j) ∧
      ∀ e : FiniteWired.Edge B, (WiredTrees.graph B).left e ∈ T →
        (WiredTrees.graph B).right e ∈ T →
        (e ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ↔
          ∃ v ∈ T, v ∉ wiredOriginRoot B ∧ (σ (v, j v)).val = e) := by
  obtain ⟨T, j, hsmall, hlarge, _⟩ := originSafeIncidentStackEvent_explorations B x k n σ hσ
  refine ⟨T, j, hlarge, ?_⟩
  intro e he1 he2
  exact terminal_incidentCopy_mem_iff_prefix (WiredTrees.graph B) (wiredOriginRoot B)
    (fun v i => σ (v, i)) k t ((List.range n).map fun i => wiredSite B (x i)) T j
    hrun ht hsmall e he1 he2

end
end FiniteAvalanches.Wilson.Lattice
