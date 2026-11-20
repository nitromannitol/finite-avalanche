import FiniteAvalanches.Wilson.Lattice.WiredHistoryEdges
import FiniteAvalanches.Wilson.Lattice.HistoryEdgeRelabel

/-! Interior wired edges in first-hit Wilson branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Between two active endpoints there is exactly one original interior copy. -/
theorem wiredInterior_adjacent_iff (B : ℕ) (F : Finset (FiniteWired.Edge B))
    (e : FiniteWired.InteriorEdge B) :
    (WiredTrees.graph B).adjacent F (some e.val.1) (some e.val.2) ↔ Sum.inl e ∈ F := by
  constructor
  · rintro ⟨q, hq, hends⟩
    cases q with
    | inr q =>
      change ((some q.val.1 = some e.val.1 ∧ none = some e.val.2) ∨
        (none = some e.val.1 ∧ some q.val.1 = some e.val.2)) at hends
      simp only [reduceCtorEq, and_false, false_and, or_self] at hends
    | inl q =>
      change ((some q.val.1 = some e.val.1 ∧ some q.val.2 = some e.val.2) ∨
        (some q.val.2 = some e.val.1 ∧ some q.val.1 = some e.val.2)) at hends
      have hpair : s(FiniteWired.site q.val.1, FiniteWired.site q.val.2) =
          s(FiniteWired.site e.val.1, FiniteWired.site e.val.2) := by
        apply Sym2.eq_iff.mpr
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨congrArg FiniteWired.site (Option.some.inj h1),
            congrArg FiniteWired.site (Option.some.inj h2)⟩
        · exact Or.inr ⟨congrArg FiniteWired.site (Option.some.inj h2),
            congrArg FiniteWired.site (Option.some.inj h1)⟩
      have he : q = e := interiorEdge_injective B (Subtype.ext hpair)
      exact he ▸ hq
  · intro he
    exact ⟨Sum.inl e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- An interior edge with attached endpoints is in the compatible wired
forest exactly when it appears in the recorded erased branches. -/
theorem wiredInterior_mem_iff_branchHistoryEdgeSet (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (n : ℕ) (h : BranchHistory n)
    (a : GoodArrows (wiredRoots R B).val (wiredHead B)) (e : FiniteWired.InteriorEdge B)
    (hfirst : BranchHistory.FirstHits (wiredHead B) x (wiredRoots R B).val n h)
    (ha : BranchHistory.Realizes (wiredHead B) x a.val n h)
    (hleft : some e.val.1 ∈ branchHistoryRoots (wiredHead B) x (wiredRoots R B).val n h)
    (hright : some e.val.2 ∈ branchHistoryRoots (wiredHead B) x (wiredRoots R B).val n h) :
    Sum.inl e ∈ (wiredArrowForest R B a).val ↔
      s(some e.val.1, some e.val.2) ∈ branchHistoryEdgeSet (wiredHead B) x n h := by
  let U := branchHistoryRoots (wiredHead B) x (wiredRoots R B).val n h
  let f := fun v => wiredHead B v (a.val v)
  change Sum.inl e ∈ wiredArrowCopies R B a ↔ _
  rw [← wiredInterior_adjacent_iff B (wiredArrowCopies R B a) e,
    mem_branchHistoryEdgeSet_iff (wiredHead B) x (wiredRoots R B).val n h a.val hfirst ha]
  constructor
  · intro hadj
    have hr := wiredArrowCopies_adj R B a (some e.val.1) (some e.val.2) hadj
    rcases hr with ⟨hv, he⟩ | ⟨hv, he⟩
    · refine ⟨some e.val.1, hleft, hv, ?_⟩
      change wiredHead B (some e.val.1) (a.val (some e.val.1)) = some e.val.2 at he
      exact congrArg (fun q => s(some e.val.1, q)) he.symm
    · refine ⟨some e.val.2, hright, hv, ?_⟩
      change wiredHead B (some e.val.2) (a.val (some e.val.2)) = some e.val.1 at he
      calc
        s(some e.val.1, some e.val.2) = s(some e.val.2, some e.val.1) := Sym2.eq_swap
        _ = s(some e.val.2, wiredHead B (some e.val.2) (a.val (some e.val.2))) :=
          congrArg (fun q => s(some e.val.2, q)) he.symm
  · rintro ⟨v, hvU, hvR, he⟩
    have hp := Sym2.eq_iff.mp he
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hstep := wiredArrowCopies_step R B a v hvR
      rw [← h2, ← h1] at hstep
      exact hstep
    · have hstep := wiredArrowCopies_step R B a v hvR
      rw [← h1, ← h2] at hstep
      obtain ⟨q, hq, hends⟩ := hstep
      exact ⟨q, hq, hends.elim (fun h => Or.inr ⟨h.2, h.1⟩)
        (fun h => Or.inl ⟨h.2, h.1⟩)⟩

end
end FiniteAvalanches.Wilson.Lattice
