import FiniteAvalanches.Wilson.Lattice.FreeHistoryEdges
import FiniteAvalanches.Wilson.Lattice.FreeObservedEdges

/-! Finite free terminal edge observations are determined by branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeTerminalHistoryEdges (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- Edge indicators encoded by the erased branches of a free-box history. -/
def freeHistoryEdgeField (B : ℕ) (x : ℕ → FiniteWired.Active (B + 1))
    (n : ℕ) (h : BranchHistory n) : EdgeField :=
  fun e => decide (e.val ∈ (branchHistoryEdgeSet (freeDirectionHead (B + 1)) x n h).image
    (Sym2.map FiniteWired.site))

/-- A terminal origin-and-boundary forest and its successful history agree on
an edge whose endpoints have been queried and whose original copy lies in the box. -/
theorem freeTerminal_edgeField_eq_history (B : ℕ) (x : ℕ → Site 2)
    (k t : Cursor (FiniteWired.Active (B + 1))) (N n : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (hrun : Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
      (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1)))
      (fun v i => σ (v, i)) t)
    (hhit : ∀ i < n, (boundedBranchHistory (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N
        (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) (i + 1)).2.1 < N)
    (e : LatticeEdge) (hE : ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hcopy : ∃ i : FiniteWired.InteriorEdge (B + 1), interiorEdge i = e) :
    freeIncidentArrowEdgeField B (freeOriginAndBoundary B) ⟨fun v => σ (v, t v), ht⟩ e =
      freeHistoryEdgeField B (fun i => freeSite (B + 1) (x i)) n
        (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
          (freeOriginAndBoundary B) k N (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) n) e := by
  let bx := fun i => freeSite (B + 1) (x i)
  let h := boundedBranchHistory (freeDirectionHead (B + 1)) bx (freeOriginAndBoundary B) k N
    (padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)) n
  obtain ⟨j, hj⟩ := hcopy
  have hlmem : FiniteWired.site j.val.1 ∈ e.val := hj ▸ (interiorEdge_endpoint_mem j).1
  have hrmem : FiniteWired.site j.val.2 ∈ e.val := hj ▸ (interiorEdge_endpoint_mem j).2
  obtain ⟨l, hl, hlx⟩ := hE _ hlmem
  obtain ⟨r, hr, hrx⟩ := hE _ hrmem
  have hleft : (freeBoxGraph (B + 1)).left j ∈
      branchHistoryRoots (freeDirectionHead (B + 1)) bx (freeOriginAndBoundary B) n h := by
    have hv := mem_branchHistoryRoots_of_query (freeDirectionHead (B + 1)) bx
      (freeOriginAndBoundary B) n h hl
    change freeSite (B + 1) (x l) ∈ _ at hv
    rw [hlx, freeSite_site] at hv
    exact hv
  have hright : (freeBoxGraph (B + 1)).right j ∈
      branchHistoryRoots (freeDirectionHead (B + 1)) bx (freeOriginAndBoundary B) n h := by
    have hv := mem_branchHistoryRoots_of_query (freeDirectionHead (B + 1)) bx
      (freeOriginAndBoundary B) n h hr
    change freeSite (B + 1) (x r) ∈ _ at hv
    rw [hrx, freeSite_site] at hv
    exact hv
  have hselected := freeTerminalCopy_mem_iff_branchHistoryEdgeSet B bx k t N n σ
    hrun ht hhit j hleft hright
  have hmap : e.val ∈ (branchHistoryEdgeSet (freeDirectionHead (B + 1)) bx n h).image
      (Sym2.map FiniteWired.site) ↔
      s((freeBoxGraph (B + 1)).left j, (freeBoxGraph (B + 1)).right j) ∈
        branchHistoryEdgeSet (freeDirectionHead (B + 1)) bx n h := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, hqeq⟩
      have hjpair : Sym2.map FiniteWired.site
          s((freeBoxGraph (B + 1)).left j, (freeBoxGraph (B + 1)).right j) = e.val := by
        change (interiorEdge j).val = e.val
        exact congrArg Subtype.val hj
      have hq' := (Sym2.map.injective (FiniteWired.site_injective (B + 1))) (hqeq.trans hjpair.symm)
      exact hq' ▸ hq
    · intro hq
      refine ⟨s((freeBoxGraph (B + 1)).left j, (freeBoxGraph (B + 1)).right j), hq, ?_⟩
      change (interiorEdge j).val = e.val
      exact congrArg Subtype.val hj
  unfold freeIncidentArrowEdgeField freeHistoryEdgeField
  apply Bool.decide_congr
  constructor
  · rintro ⟨i, hi, hie⟩
    have hij : i = j := interiorEdge_injective (B + 1) (hie.trans hj.symm)
    subst i
    exact hmap.mpr (hselected.mp hi)
  · intro hm
    exact ⟨j, hselected.mpr (hmap.mp hm), hj⟩

end
end FiniteAvalanches.Wilson.Lattice
