import FiniteAvalanches.Wilson.Lattice.HistoryArrows
import FiniteAvalanches.Wilson.Lattice.RowBranchHorizon
import FiniteAvalanches.Wilson.Lattice.WiredStackExplorationLaw
import FiniteAvalanches.Wilson.Lattice.WiredArrowUniqueness

/-! The uniform wired forest law from independently driven branch histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A finite history describes a wired forest if its retained branch arrows are
realized by a cycle-free direction assignment for that forest. -/
def BranchHistory.WiredForestEvent (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (n : ℕ) (S : Set (FiniteForest R B))
    (h : BranchHistory n) : Prop :=
  ∃ a : GoodArrows (wiredRoots R B).val (wiredHead B),
    BranchHistory.Realizes (wiredHead B) x a.val n h ∧ wiredArrowForest R B a ∈ S

/-- In a full wired exploration, independently driven branch histories select a
uniform rooted forest of original edge copies. -/
theorem wilsonRows_completed_wiredForest_eq (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (hcover : ∀ v, v ∈ (List.range n).map x) (S : Set (FiniteForest R B)) :
    wilsonRows {rows | ∃ N,
      BranchHistory.HitsBefore N n
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n) ∧
      BranchHistory.WiredForestEvent R B x n S
        (rowBranchHistory (wiredHead B) x (wiredRoots R B).val k N rows n)} =
      finiteUniformLaw R B S := by
  let V := FiniteWired.Vertex B
  let roots := (wiredRoots R B).val
  let head := wiredHead B
  let L := (List.range n).map x
  let P := BranchHistory.WiredForestEvent R B x n S
  let E : Set (V × ℕ → FiniteWired.Direction) := {σ | ∃ N,
    BranchHistory.HitsBefore N n (boundedBranchHistory head x roots k N σ n) ∧
      P (boundedBranchHistory head x roots k N σ n)}
  let F : Set (V × ℕ → FiniteWired.Direction) := {σ | ∃ (t : Cursor V)
      (ht : terminal roots head (fun v i => σ (v, i)) t),
      stackExplore head (fun v i => σ (v, i)) roots k L = some (Set.univ, t) ∧
      wiredArrowForest R B ⟨fun v => σ (v, t v), ht⟩ ∈ S}
  have hae : ∀ᵐ σ ∂directionStackLaw V, σ ∈ E ↔ σ ∈ F := by
    filter_upwards [wiredStack_ae_terminates R B k] with σ hterm
    obtain ⟨t, hrun, ht⟩ := hterm
    have hexplore : stackExplore head (fun v i => σ (v, i)) roots k L = some (Set.univ, t) :=
      stackExplore_all_of_terminal roots head (fun v i => σ (v, i)) k t hrun ht L hcover
    constructor
    · rintro ⟨N, hN, a, ha, hS⟩
      have hh := (boundedBranchHistory_hitsBefore_iff head x roots k N n σ).mp hN
      let b := boundedBranchHistory head x roots k N σ n
      let j := branchHistoryErasedCursor head x k n b
      have he := (stackExplore_eq_historyErasedCursor head x roots k N n σ hh).1
      rw [hexplore, Option.some.injEq, Prod.mk.injEq] at he
      have hroot : branchHistoryRoots head x roots n b = Set.univ := he.1.symm
      have hj : j = t := he.2.symm
      let z : GoodArrows roots head := ⟨fun v => σ (v, t v), ht⟩
      have hz : BranchHistory.Realizes head x z.val n b := by
        have hz' := branchHistory_top_realizes_of_hits head x roots k N n σ hh
        simpa only [b, j, hj, z] using hz'
      have hend := branchHistory_endsInRoots_of_hits head x roots k N n σ hh
      have heq : wiredArrowForest R B a = wiredArrowForest R B z := by
        apply wiredArrowForest_eq_of_nonroot_eq R B
        intro v hv
        exact BranchHistory.Realizes.eq_of_mem_roots head x roots n b a.val z.val hend ha hz
          (hroot.symm ▸ Set.mem_univ v) hv
      refine ⟨t, ht, hexplore, ?_⟩
      rwa [← heq]
    · rintro ⟨u, hu, huExplore, huS⟩
      obtain ⟨N, hh⟩ := exists_horizon_of_stackExplore head x roots k n σ Set.univ u huExplore
      let b := boundedBranchHistory head x roots k N σ n
      let j := branchHistoryErasedCursor head x k n b
      have he := (stackExplore_eq_historyErasedCursor head x roots k N n σ hh).1
      rw [huExplore, Option.some.injEq, Prod.mk.injEq] at he
      have hj : j = u := he.2.symm
      refine ⟨N, (boundedBranchHistory_hitsBefore_iff head x roots k N n σ).mpr hh, ?_⟩
      refine ⟨⟨fun v => σ (v, u v), hu⟩, ?_, huS⟩
      have hz := branchHistory_top_realizes_of_hits head x roots k N n σ hh
      simpa only [b, j, hj] using hz
  calc
    wilsonRows {rows | ∃ N,
        BranchHistory.HitsBefore N n
          (rowBranchHistory head x roots k N rows n) ∧
        P (rowBranchHistory head x roots k N rows n)} = directionStackLaw V E :=
      (directionStackLaw_completedBranchHistory_eq_wilsonRows head x roots k n P).symm
    _ = directionStackLaw V F := measure_congr (hae.mono fun _ h => propext h)
    _ = finiteUniformLaw R B S := directionStackLaw_stackExplore_eq R B k L hcover S

end
end FiniteAvalanches.Wilson.Lattice
