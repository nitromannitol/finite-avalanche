import FiniteAvalanches.Wilson.Lattice.WiredDualFaceHistoryEdges
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceObservationEvent

/-! Face terminal edge observations are determined by branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceTerminalHistoryEdges (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- Lattice edge indicators encoded by the erased branches of a face history. -/
def wiredDualFaceHistoryEdgeField (B : ℕ) (x : ℕ → WiredDualFace (B + 1))
    (n : ℕ) (h : BranchHistory n) : EdgeField :=
  fun e => decide (e.val ∈ (branchHistoryEdgeSet (wiredDualFaceDirectionHead (B + 1)) x n h).image
    (Sym2.map wiredDualFaceSite))

/-- A terminal face forest and its successful history agree on an edge with
queried endpoints inside the centered box and a represented face copy. -/
theorem wiredDualFaceTerminal_edgeField_eq_history (B : ℕ) (x : ℕ → Site 2)
    (k t : Cursor (WiredDualFace (B + 1))) (N n : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (hrun : Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B)
      (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal (wiredDualFaceOriginAndBoundary B) (incidentCopyHead (wiredDualFaceGraph (B + 1)))
      (fun v i => σ (v, i)) t)
    (hhit : ∀ i < n, (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1))
      (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
      (wiredDualFaceOriginAndBoundary B) k N
      (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) (i + 1)).2.1 < N)
    (e : LatticeEdge) (hE : ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hbox : ∀ z ∈ e.val, FiniteWired.inBox (B + 1) z)
    (hcopy : ∃ q : FiniteWired.Edge (B + 1), wiredCopyDualEdge q = e) :
    wiredDualFaceIncidentArrowEdgeField B (wiredDualFaceOriginAndBoundary B) ⟨fun v => σ (v, t v), ht⟩ e =
      wiredDualFaceHistoryEdgeField B
        (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) n
        (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1))
          (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
          (wiredDualFaceOriginAndBoundary B) k N
          (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) n) e := by
  let bx := fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))
  let h := boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) bx (wiredDualFaceOriginAndBoundary B) k N
    (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)) n
  obtain ⟨q, hq⟩ := hcopy
  have hpair := wiredDualFaceGraph_edge (B + 1) q
  have hlmem : wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).left q) ∈ e.val := by
    rw [← hq, ← hpair]
    exact Sym2.mem_iff.mpr (Or.inl rfl)
  have hrmem : wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).right q) ∈ e.val := by
    rw [← hq, ← hpair]
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  obtain ⟨l, hl, hlx⟩ := hE _ hlmem
  obtain ⟨r, hr, hrx⟩ := hE _ hrmem
  have hleft : (wiredDualFaceGraph (B + 1)).left q ∈
      branchHistoryRoots (wiredDualFaceDirectionHead (B + 1)) bx (wiredDualFaceOriginAndBoundary B) n h := by
    have hv := mem_branchHistoryRoots_of_query (wiredDualFaceDirectionHead (B + 1)) bx
      (wiredDualFaceOriginAndBoundary B) n h hl
    change wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x l)) ∈ _ at hv
    rw [hlx, wiredDualFaceInnerVertex_freeSite B _ (hbox _ hlmem)] at hv
    exact hv
  have hright : (wiredDualFaceGraph (B + 1)).right q ∈
      branchHistoryRoots (wiredDualFaceDirectionHead (B + 1)) bx (wiredDualFaceOriginAndBoundary B) n h := by
    have hv := mem_branchHistoryRoots_of_query (wiredDualFaceDirectionHead (B + 1)) bx
      (wiredDualFaceOriginAndBoundary B) n h hr
    change wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x r)) ∈ _ at hv
    rw [hrx, wiredDualFaceInnerVertex_freeSite B _ (hbox _ hrmem)] at hv
    exact hv
  have hselected := wiredDualFaceTerminalCopy_mem_iff_branchHistoryEdgeSet B bx k t N n σ
    hrun ht hhit q hleft hright
  have hmap : e.val ∈ (branchHistoryEdgeSet (wiredDualFaceDirectionHead (B + 1)) bx n h).image
      (Sym2.map wiredDualFaceSite) ↔
      s((wiredDualFaceGraph (B + 1)).left q, (wiredDualFaceGraph (B + 1)).right q) ∈
        branchHistoryEdgeSet (wiredDualFaceDirectionHead (B + 1)) bx n h := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, haeq⟩
      have hqpair : Sym2.map wiredDualFaceSite
          s((wiredDualFaceGraph (B + 1)).left q, (wiredDualFaceGraph (B + 1)).right q) = e.val := by
        rw [Sym2.map_mk, wiredDualFaceGraph_edge, hq]
      have ha' := (Sym2.map.injective (wiredDualFaceSite_injective (B + 1))) (haeq.trans hqpair.symm)
      exact ha' ▸ ha
    · intro ha
      refine ⟨s((wiredDualFaceGraph (B + 1)).left q, (wiredDualFaceGraph (B + 1)).right q), ha, ?_⟩
      rw [Sym2.map_mk, wiredDualFaceGraph_edge, hq]
  unfold wiredDualFaceIncidentArrowEdgeField wiredDualFaceHistoryEdgeField
  apply Bool.decide_congr
  constructor
  · rintro ⟨i, hi, hie⟩
    have hiq : i = q := wiredCopyDualEdge_injective (B + 1) (hie.trans hq.symm)
    subst i
    exact hmap.mpr (hselected.mp hi)
  · intro hm
    exact ⟨q, hselected.mpr (hmap.mp hm), hq⟩

end
end FiniteAvalanches.Wilson.Lattice
