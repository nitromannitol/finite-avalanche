import FiniteAvalanches.Wilson.Lattice.FreeTerminalHistoryEdges
import FiniteAvalanches.Wilson.Lattice.FreeCompletedHistoryLaw

/-! Origin-and-boundary terminal observations as completed Wilson row histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeBoundaryHistoryEvent (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- The terminal origin-and-boundary edge event has the independent-row
probability of the corresponding completed finite-history edge pattern. -/
theorem variableStackLaw_freeBoundaryEdgeEvent_eq_wilsonRows (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ v ∈ freeOuterBoundary B, k v = 0) (n : ℕ) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hrep : ∀ e ∈ E, ∃ i : FiniteWired.InteriorEdge (B + 1), interiorEdge i = e) :
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeIncidentStackEdgeEvent B (freeOriginAndBoundary B) k E p) =
    wilsonRows {rows | ∃ N, BranchHistory.HitsBefore N n
        (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
          (freeOriginAndBoundary B) k N rows n) ∧
      ∀ e ∈ E, freeHistoryEdgeField B (fun i => freeSite (B + 1) (x i)) n
        (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
          (freeOriginAndBoundary B) k N rows n) e = p e} := by
  let bx := fun i => freeSite (B + 1) (x i)
  let P : BranchHistory n → Prop := fun h => ∀ e ∈ E, freeHistoryEdgeField B bx n h e = p e
  let H := freeCompletedStackHistoryEvent B x k n P
  have he := variableStackLaw_freeCompletedHistory_eq_wilsonRows B x k hk n P
  have hae : ∀ᵐ σ ∂variableStackLaw (IncidentCopy (freeBoxGraph (B + 1))),
      σ ∈ freeIncidentStackEdgeEvent B (freeOriginAndBoundary B) k E p ↔
        padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) ∈ H := by
    filter_upwards [variableStackLaw_ae_freeOriginAndBoundary_terminal B k] with σ hterm
    obtain ⟨t, hrun, ht⟩ := hterm
    rw [freeIncidentStackEdgeEvent_iff_terminal B _ k t E p σ hrun ht]
    let τ := padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)
    have hfield (N : ℕ)
        (hhit : ∀ i < n, (boundedBranchHistory (freeDirectionHead (B + 1)) bx
          (freeOriginAndBoundary B) k N τ (i + 1)).2.1 < N) :
        ∀ e ∈ E, freeIncidentArrowEdgeField B (freeOriginAndBoundary B)
            ⟨fun v => σ (v, t v), ht⟩ e =
          freeHistoryEdgeField B bx n
            (boundedBranchHistory (freeDirectionHead (B + 1)) bx (freeOriginAndBoundary B) k N τ n) e := by
      intro e heE
      exact freeTerminal_edgeField_eq_history B x k t N n σ hrun ht hhit e (hE e heE) (hrep e heE)
    constructor
    · intro hpat
      have hmatch := freeIncident_paddedDirections_terminal B σ k t
      obtain ⟨U, j, hexplore, _⟩ := stackExplore_of_terminal (freeOriginAndBoundary B)
        (freeDirectionHead (B + 1)) (fun v i => τ (v, i)) k t (hmatch.1.mp hrun) (hmatch.2.mp ht)
        ((List.range n).map bx)
      obtain ⟨N, hh⟩ := exists_horizon_of_stackExplore (freeDirectionHead (B + 1)) bx
        (freeOriginAndBoundary B) k n τ U j hexplore
      refine ⟨N, (boundedBranchHistory_hitsBefore_iff (freeDirectionHead (B + 1)) bx
        (freeOriginAndBoundary B) k N n τ).mpr hh, ?_⟩
      intro e heE
      rw [← hfield N hh e heE]
      exact hpat e heE
    · rintro ⟨N, hN, hpat⟩
      have hh := (boundedBranchHistory_hitsBefore_iff (freeDirectionHead (B + 1)) bx
        (freeOriginAndBoundary B) k N n τ).mp hN
      intro e heE
      rw [hfield N hh e heE]
      exact hpat e heE
  calc
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
        (freeIncidentStackEdgeEvent B (freeOriginAndBoundary B) k E p) =
      variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
        {σ | padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) ∈ H} :=
          measure_congr (hae.mono fun _ h => propext h)
    _ = _ := he

end
end FiniteAvalanches.Wilson.Lattice
