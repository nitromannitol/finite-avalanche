import FiniteAvalanches.Wilson.Lattice.HistoryRootwardEdges
import FiniteAvalanches.Wilson.CyclePopping.IncidentArrows

/-! Copied forest edges determined by realized finite direction histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

/-- In a copied graph with unique endpoint pairs, a realized first-hit history
determines each selected copy whose endpoints are both in the attached set. -/
theorem incidentCopy_mem_iff_branchHistoryEdgeSet (G : Multigraph V E) (R : Set V)
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (n : ℕ) (h : BranchHistory n)
    (a : (v : V) → IncidentCopy G v) (dirs : V → FiniteWired.Direction) (e : E)
    (huniq : Function.Injective (fun q : E => s(G.left q, G.right q)))
    (hmatch : ∀ v ∉ R, head v (dirs v) = incidentCopyHead G v (a v))
    (hfirst : BranchHistory.FirstHits head x R n h) (ha : BranchHistory.Realizes head x dirs n h)
    (hleft : G.left e ∈ branchHistoryRoots head x R n h)
    (hright : G.right e ∈ branchHistoryRoots head x R n h) :
    e ∈ rootwardCopies R (fun v => (a v).val) ↔
      s(G.left e, G.right e) ∈ branchHistoryEdgeSet head x n h := by
  rw [mem_branchHistoryEdgeSet_iff head x R n h dirs hfirst ha]
  constructor
  · intro he
    obtain ⟨v, hv, hcopy⟩ := Finset.mem_image.mp he
    have hvR : v ∉ R := (Finset.mem_filter.mp hv).2
    have hend := incidentCopy_endpoints G v (a v)
    rw [hcopy] at hend
    have hvU : v ∈ branchHistoryRoots head x R n h := by
      rcases hend with hends | hends
      · exact hends.1 ▸ hleft
      · exact hends.1 ▸ hright
    refine ⟨v, hvU, hvR, ?_⟩
    rw [hmatch v hvR]
    rcases hend with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
    · rw [hl, hr, Sym2.eq_swap]
  · rintro ⟨v, _, hvR, he⟩
    have hend := incidentCopy_endpoints G v (a v)
    have hpair : s(G.left e, G.right e) = s(G.left (a v).val, G.right (a v).val) := by
      rw [he, hmatch v hvR]
      rcases hend with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hl, hr]
      · rw [hl, hr, Sym2.eq_swap]
    have heq : e = (a v).val := huniq hpair
    change e ∈ rootwardCopies R (fun v => (a v).val)
    apply Finset.mem_image.mpr
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvR⟩, heq.symm⟩

end
end FiniteAvalanches.Wilson.Lattice
