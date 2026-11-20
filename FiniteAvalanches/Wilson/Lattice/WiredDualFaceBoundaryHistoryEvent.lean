import FiniteAvalanches.Wilson.Lattice.WiredDualFaceTerminalHistoryEdges
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceCompletedHistoryLaw

/-! Origin-and-boundary terminal observations as completed Wilson row histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceBoundaryHistoryEvent (N : ℕ) :
    DecidableEq (FiniteWired.Edge N) := Classical.decEq _

/-- The terminal origin-and-boundary edge event has the independent-row
probability of the corresponding completed finite-history edge pattern. -/
theorem variableStackLaw_wiredDualFaceBoundaryEdgeEvent_eq_wilsonRows (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1)))
    (hk : ∀ v ∈ wiredDualFaceOuterBoundary B, k v = 0) (n : ℕ) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hbox : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox (B + 1) z)
    (hrep : ∀ e ∈ E, ∃ i : FiniteWired.Edge (B + 1), wiredCopyDualEdge i = e) :
    variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      (wiredDualFaceIncidentStackEdgeEvent B (wiredDualFaceOriginAndBoundary B) k E p) =
    wilsonRows {rows | ∃ N, BranchHistory.HitsBefore N n
        (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
          (wiredDualFaceOriginAndBoundary B) k N rows n) ∧
      ∀ e ∈ E, wiredDualFaceHistoryEdgeField B (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) n
        (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
          (wiredDualFaceOriginAndBoundary B) k N rows n) e = p e} := by
  let bx := fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))
  let P : BranchHistory n → Prop := fun h => ∀ e ∈ E, wiredDualFaceHistoryEdgeField B bx n h e = p e
  let H := wiredDualFaceCompletedStackHistoryEvent B x k n P
  have he := variableStackLaw_wiredDualFaceCompletedHistory_eq_wilsonRows B x k hk n P
  have hae : ∀ᵐ σ ∂variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1))),
      σ ∈ wiredDualFaceIncidentStackEdgeEvent B (wiredDualFaceOriginAndBoundary B) k E p ↔
        padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) ∈ H := by
    filter_upwards [variableStackLaw_ae_wiredDualFaceOriginAndBoundary_terminates B k] with σ hterm
    obtain ⟨t, hrun, ht⟩ := hterm
    rw [wiredDualFaceIncidentStackEdgeEvent_iff_terminal B _ k t E p σ hrun ht]
    let τ := padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)
    have hfield (N : ℕ)
        (hhit : ∀ i < n, (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) bx
          (wiredDualFaceOriginAndBoundary B) k N τ (i + 1)).2.1 < N) :
        ∀ e ∈ E, wiredDualFaceIncidentArrowEdgeField B (wiredDualFaceOriginAndBoundary B)
            ⟨fun v => σ (v, t v), ht⟩ e =
          wiredDualFaceHistoryEdgeField B bx n
            (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) bx (wiredDualFaceOriginAndBoundary B) k N τ n) e := by
      intro e heE
      exact wiredDualFaceTerminal_edgeField_eq_history B x k t N n σ hrun ht hhit e (hE e heE) (hbox e heE) (hrep e heE)
    constructor
    · intro hpat
      have hmatch := wiredDualFaceIncident_paddedDirections_terminal B σ k t
      obtain ⟨U, j, hexplore, _⟩ := stackExplore_of_terminal (wiredDualFaceOriginAndBoundary B)
        (wiredDualFaceDirectionHead (B + 1)) (fun v i => τ (v, i)) k t (hmatch.1.mp hrun) (hmatch.2.mp ht)
        ((List.range n).map bx)
      obtain ⟨N, hh⟩ := exists_horizon_of_stackExplore (wiredDualFaceDirectionHead (B + 1)) bx
        (wiredDualFaceOriginAndBoundary B) k n τ U j hexplore
      refine ⟨N, (boundedBranchHistory_hitsBefore_iff (wiredDualFaceDirectionHead (B + 1)) bx
        (wiredDualFaceOriginAndBoundary B) k N n τ).mpr hh, ?_⟩
      intro e heE
      rw [← hfield N hh e heE]
      exact hpat e heE
    · rintro ⟨N, hN, hpat⟩
      have hh := (boundedBranchHistory_hitsBefore_iff (wiredDualFaceDirectionHead (B + 1)) bx
        (wiredDualFaceOriginAndBoundary B) k N n τ).mp hN
      intro e heE
      rw [hfield N hh e heE]
      exact hpat e heE
  calc
    variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
        (wiredDualFaceIncidentStackEdgeEvent B (wiredDualFaceOriginAndBoundary B) k E p) =
      variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
        {σ | padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) ∈ H} :=
          measure_congr (hae.mono fun _ h => propext h)
    _ = _ := he

end
end FiniteAvalanches.Wilson.Lattice
