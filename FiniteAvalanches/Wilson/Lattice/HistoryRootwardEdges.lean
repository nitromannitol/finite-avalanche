import FiniteAvalanches.Wilson.Lattice.HistoryFirstHit
import FiniteAvalanches.Wilson.Lattice.LatticeBranchHorizon

/-! Rootward edge sets determined by finite first-hit Wilson histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Unoriented edges traversed by an arrow-labeled path. -/
def pathUndirectedEdges [Quiver V] {a : V} : {b : V} → Path a b → Finset (Sym2 V)
  | _, .nil => ∅
  | c, @Path.cons _ _ _ b _ p _ => pathUndirectedEdges p ∪ {s(b, c)}

/-- For a path following an arrow map, its unoriented edges are exactly the
edges from each departure to its successor. -/
theorem mem_pathUndirectedEdges_iff [Quiver V] (f : V → V) {a b : V}
    (p : Path a b) (hp : follows f p) (e : Sym2 V) :
    e ∈ pathUndirectedEdges p ↔ ∃ v ∈ departures p, e = s(v, f v) := by
  induction p with
  | nil => simp only [pathUndirectedEdges, Finset.notMem_empty, departures,
      Path.vertices_nil, List.dropLast_singleton, List.not_mem_nil, false_and,
      exists_false]
  | @cons b c p arrow ih =>
    rw [pathUndirectedEdges, Finset.mem_union, Finset.mem_singleton, departures_cons]
    constructor
    · rintro (he | he)
      · obtain ⟨v, hv, hv'⟩ := (ih hp.1).mp he
        exact ⟨v, List.mem_append_left _ hv, hv'⟩
      · refine ⟨b, List.mem_append_right _ (List.mem_singleton_self b), ?_⟩
        simpa only [hp.2] using he
    · rintro ⟨v, hv, he⟩
      rcases List.mem_append.mp hv with hv | hv
      · exact Or.inl ((ih hp.1).mpr ⟨v, hv, he⟩)
      · have h := List.mem_singleton.mp hv
        subst v
        exact Or.inr (by simpa only [hp.2] using he)

/-- The union of all unoriented edges in the loop-erased branches. -/
def branchHistoryEdgeSet (head : V → FiniteWired.Direction → V) (x : ℕ → V) :
    (n : ℕ) → BranchHistory n → Finset (Sym2 V)
  | 0, _ => ∅
  | n + 1, h => by
    letI : Quiver V := instructionQuiver head
    exact branchHistoryEdgeSet head x n h.1 ∪
      pathUndirectedEdges (loopErase (historyTrace head (x n) h.2).2)

/-- A first-hit history contains exactly the selected outgoing edge of each
attached nonroot vertex. -/
theorem mem_branchHistoryEdgeSet_iff (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (n : ℕ) (h : BranchHistory n)
    (a : V → FiniteWired.Direction)
    (hfirst : BranchHistory.FirstHits head x R n h)
    (ha : BranchHistory.Realizes head x a n h) (e : Sym2 V) :
    e ∈ branchHistoryEdgeSet head x n h ↔
      ∃ v ∈ branchHistoryRoots head x R n h, v ∉ R ∧ e = s(v, head v (a v)) := by
  letI : Quiver V := instructionQuiver head
  induction n with
  | zero =>
    simp only [branchHistoryEdgeSet, Finset.notMem_empty, branchHistoryRoots]
    exact ⟨False.elim, fun ⟨v, hv, hnot, _⟩ => (hnot hv).elim⟩
  | succ n ih =>
    change BranchHistory.FirstHits head x R n h.1 ∧ _ at hfirst
    change BranchHistory.Realizes head x a n h.1 ∧ _ at ha
    let S := branchHistoryRoots head x R n h.1
    let q := loopErase (historyTrace head (x n) h.2).2
    have hend : (historyTrace head (x n) h.2).1 ∈ S := hfirst.2.1
    have hfollow := selected_follows (instructionArrowStacks head (fun v _ => a v)) (fun _ => 0) q ha.2
    change follows (fun v => head v (a v)) q at hfollow
    change e ∈ branchHistoryEdgeSet head x n h.1 ∪ pathUndirectedEdges q ↔
      ∃ v ∈ S ∪ {v | v ∈ q.vertices}, v ∉ R ∧ e = s(v, head v (a v))
    rw [Finset.mem_union, mem_pathUndirectedEdges_iff _ q hfollow]
    constructor
    · rintro (he | ⟨v, hv, he⟩)
      · obtain ⟨v, hv, hR, he⟩ := (ih h.1 hfirst.1 ha.1).mp he
        exact ⟨v, Or.inl hv, hR, he⟩
      · have hR : v ∉ R := fun hvR => hfirst.2.2 v hv
          (branchHistoryRoots_initial_subset head x R n h.1 hvR)
        exact ⟨v, Or.inr (List.mem_of_mem_dropLast hv), hR, he⟩
    · rintro ⟨v, hv, hvR, he⟩
      rcases hv with hv | hv
      · exact Or.inl ((ih h.1 hfirst.1 ha.1).mpr ⟨v, hv, hvR, he⟩)
      · change v ∈ q.vertices at hv
        by_cases hvS : v ∈ S
        · exact Or.inl ((ih h.1 hfirst.1 ha.1).mpr ⟨v, hvS, hvR, he⟩)
        · right
          have hdep : v ∈ departures q := by
            have hm : v ∈ departures q ++ [(historyTrace head (x n) h.2).1] := by
              simpa only [departures, Path.dropLast_append_end_eq, q] using hv
            rcases List.mem_append.mp hm with hm | hm
            · exact hm
            · exact (hvS ((List.mem_singleton.mp hm) ▸ hend)).elim
          exact ⟨v, hdep, he⟩

end
end FiniteAvalanches.Wilson.Lattice
