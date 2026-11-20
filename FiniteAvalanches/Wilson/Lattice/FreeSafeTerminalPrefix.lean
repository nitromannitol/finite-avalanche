import FiniteAvalanches.Wilson.Lattice.FreeSafeIncidentLaw
import FiniteAvalanches.Wilson.CyclePopping.TerminalPrefixCopies

/-! Safe finite free-box prefixes determine origin-rooted terminal copies. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance (N : ℕ) : DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- The singleton origin root of the free box. -/
def freeOriginRoot (B : ℕ) : Set (FiniteWired.Active (B + 1)) := {wiredOrigin (B + 1)}

/-- The origin-and-boundary root set is the union of its two parts. -/
theorem freeOriginAndBoundary_eq_union (B : ℕ) :
    freeOriginAndBoundary B = freeOriginRoot B ∪ freeOuterBoundary B := by
  ext x
  simp only [freeOriginAndBoundary, freeOriginRoot, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
  have h : FiniteWired.site (wiredOrigin (B + 1)) = (0 : Site 2) := rfl
  constructor
  · rintro (hx | hx)
    · left
      apply FiniteWired.site_injective (B + 1)
      exact hx.trans h.symm
    · exact Or.inr hx
  · rintro (rfl | hx)
    · exact Or.inl h
    · exact Or.inr hx

/-- A safe prefix agrees for the origin root and for the origin plus boundary. -/
theorem freeSafeIncidentStackEvent_explorations (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (hσ : σ ∈ freeSafeIncidentStackEvent B x k n) :
    ∃ T j, stackExplore (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))
        (freeOriginRoot B) k ((List.range n).map fun i => freeSite (B + 1) (x i)) = some (T, j) ∧
      stackExplore (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))
        (freeOriginAndBoundary B) k ((List.range n).map fun i => freeSite (B + 1) (x i)) =
          some (freeOriginAndBoundary B ∪ T, j) ∧ freeOriginRoot B ⊆ T := by
  have hRS : freeOriginRoot B ⊆ freeOriginAndBoundary B := by
    rw [freeOriginAndBoundary_eq_union]
    exact Set.subset_union_left
  have hSD : freeOriginAndBoundary B ⊆ freeOriginRoot B ∪ freeOuterBoundary B := by
    rw [freeOriginAndBoundary_eq_union]
  exact stackExplore_eq_of_avoidsExtraRoots (incidentCopyHead (freeBoxGraph (B + 1)))
    (fun v i => σ (v, i)) (freeOriginRoot B) (freeOriginAndBoundary B) (freeOuterBoundary B) k _
    hRS hSD (freeSafeIncidentStackEvent_avoids_boundary B x k n σ hσ)

/-- Every terminal copy with both endpoints attached by a safe prefix is
determined by the prefix's visible outgoing copies. -/
theorem freeSafe_terminalCopy_mem_iff_prefix (B : ℕ) (x : ℕ → Site 2)
    (k t : Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (hσ : σ ∈ freeSafeIncidentStackEvent B x k n)
    (hrun : Relation.ReflTransGen (pop_step (freeOriginRoot B)
      (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal (freeOriginRoot B) (incidentCopyHead (freeBoxGraph (B + 1)))
      (fun v i => σ (v, i)) t) :
    ∃ T j, stackExplore (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))
        (freeOriginAndBoundary B) k ((List.range n).map fun i => freeSite (B + 1) (x i)) =
          some (freeOriginAndBoundary B ∪ T, j) ∧
      ∀ e : FiniteWired.InteriorEdge (B + 1), (freeBoxGraph (B + 1)).left e ∈ T →
        (freeBoxGraph (B + 1)).right e ∈ T →
        (e ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ↔
          ∃ v ∈ T, v ∉ freeOriginRoot B ∧ (σ (v, j v)).val = e) := by
  obtain ⟨T, j, hsmall, hlarge, _⟩ := freeSafeIncidentStackEvent_explorations B x k n σ hσ
  refine ⟨T, j, hlarge, ?_⟩
  intro e he1 he2
  exact terminal_incidentCopy_mem_iff_prefix (freeBoxGraph (B + 1)) (freeOriginRoot B)
    (fun v i => σ (v, i)) k t ((List.range n).map fun i => freeSite (B + 1) (x i)) T j
    hrun ht hsmall e he1 he2

end
end FiniteAvalanches.Wilson.Lattice
