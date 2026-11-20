import FiniteAvalanches.Wilson.Lattice.FreeSafeTerminalPrefix
import FiniteAvalanches.Wilson.Lattice.FreeOriginTermination
import FiniteAvalanches.Wilson.CyclePopping.NestedRootTerminalCopies

/-! Coupling free-box terminal forests rooted at the origin and the boundary. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeTerminalCoupling (N : ℕ) : DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- The origin is among the origin-and-boundary roots. -/
theorem freeOriginRoot_subset (B : ℕ) : freeOriginRoot B ⊆ freeOriginAndBoundary B := by
  rw [freeOriginAndBoundary_eq_union]
  exact Set.subset_union_left

/-- Safe explorations couple the two terminal forests on inner attached edges. -/
theorem freeSafe_terminalCopies_agree (B : ℕ) (x : ℕ → Site 2)
    (k t u : Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (hσ : σ ∈ freeSafeIncidentStackEvent B x k n)
    (hrun : Relation.ReflTransGen (pop_step (freeOriginRoot B)
      (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal (freeOriginRoot B) (incidentCopyHead (freeBoxGraph (B + 1)))
      (fun v i => σ (v, i)) t)
    (hsrun : Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
      (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k u)
    (hu : terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1)))
      (fun v i => σ (v, i)) u) :
    ∃ T : Set (FiniteWired.Active (B + 1)), (∀ i < n, freeSite (B + 1) (x i) ∈ T) ∧
      ∀ e : FiniteWired.InteriorEdge (B + 1), (freeBoxGraph (B + 1)).left e ∈ T →
        (freeBoxGraph (B + 1)).right e ∈ T →
        (freeBoxGraph (B + 1)).left e ∉ freeOuterBoundary B →
        (freeBoxGraph (B + 1)).right e ∉ freeOuterBoundary B →
        (e ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ↔
          e ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginAndBoundary B)
            ⟨fun v => σ (v, u v), hu⟩) := by
  obtain ⟨T, j, hsmall, hlarge, _⟩ := freeSafeIncidentStackEvent_explorations B x k n σ hσ
  have hcover := (stackExplore_of_some (freeOriginRoot B) (incidentCopyHead (freeBoxGraph (B + 1)))
    (fun v i => σ (v, i)) k ((List.range n).map fun i => freeSite (B + 1) (x i)) T j hsmall).2.1
  refine ⟨T, ?_, ?_⟩
  · intro i hi
    exact hcover _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · intro e he1 he2 hne1 hne2
    apply terminal_incidentCopy_mem_iff_of_nested_prefix (freeBoxGraph (B + 1))
      (freeOriginRoot B) (freeOriginAndBoundary B) (freeOriginRoot_subset B)
      (fun v i => σ (v, i)) k t u _ T j hrun ht hsrun hu hsmall hlarge e he1 he2
    all_goals
      intro hv
      rw [freeOriginAndBoundary_eq_union] at hv
      exact hv.resolve_right (by assumption)

/-- Origin-and-boundary free-box cycle popping terminates almost surely. -/
theorem variableStackLaw_ae_freeOriginAndBoundary_terminal (B : ℕ)
    (k : Cursor (FiniteWired.Active (B + 1))) :
    ∀ᵐ σ ∂variableStackLaw (IncidentCopy (freeBoxGraph (B + 1))),
      ∃ t, Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
          (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t ∧
        terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1)))
          (fun v i => σ (v, i)) t := by
  obtain ⟨a⟩ := freeBox_goodOriginArrows_nonempty B
  have ha : GoodIncidentArrows (freeBoxGraph (B + 1)) (freeOriginAndBoundary B) :=
    ⟨a.val, terminal_mono_roots (freeOriginRoot B) (freeOriginAndBoundary B)
      (incidentCopyHead (freeBoxGraph (B + 1))) (fun v _ => a.val v) 0
      (freeOriginRoot_subset B) a.property⟩
  exact variableStackLaw_ae_terminates (IncidentCopy (freeBoxGraph (B + 1)))
    (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1))) k ha

end
end FiniteAvalanches.Wilson.Lattice
