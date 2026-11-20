import FiniteAvalanches.Wilson.Lattice.WiredDualFaceWordCoupling
import FiniteAvalanches.Wilson.Lattice.FreeBranchCoupling

/-! First-hit branches in the centered box and the dual face square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A confined direction word has the same first hit in corresponding root sets. -/
theorem wiredDualFace_boundedWordHit_eq_of_confined (B N : ℕ)
    (x : FiniteWired.Active (B + 1)) (w : WalkDriver)
    (S : Set (FiniteWired.Active (B + 1))) (R : Set (WiredDualFace (B + 1)))
    (k : Cursor (FiniteWired.Active (B + 1))) (l : Cursor (WiredDualFace (B + 1)))
    (hroots : ∀ z, wiredDualFaceInnerVertex (B + 1) z ∈ R ↔ z ∈ S)
    (ht : boundedWordHit (freeDirectionHead (B + 1)) S x k N w < N)
    (hconf : ∀ i < boundedWordHit (freeDirectionHead (B + 1)) S x k N w,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) x k w i).1)) :
    boundedWordHit (wiredDualFaceDirectionHead (B + 1)) R
        (wiredDualFaceInnerVertex (B + 1) x) l N w =
      boundedWordHit (freeDirectionHead (B + 1)) S x k N w := by
  let t := boundedWordHit (freeDirectionHead (B + 1)) S x k N w
  let u := boundedWordHit (wiredDualFaceDirectionHead (B + 1)) R
    (wiredDualFaceInnerVertex (B + 1) x) l N w
  have hstate := wiredDualFace_wordState_of_confined B x k l w t hconf
  have hu_le : u ≤ t := by
    apply Nat.le_of_not_gt
    intro hlt
    have hav := boundedWordHit_avoids (wiredDualFaceDirectionHead (B + 1)) R
      (wiredDualFaceInnerVertex (B + 1) x) l N w t hlt
    apply hav
    rw [← hstate t le_rfl]
    exact (hroots _).mpr (boundedWordHit_mem_of_lt (freeDirectionHead (B + 1)) S x k N w ht)
  have ht_le : t ≤ u := by
    apply Nat.le_of_not_gt
    intro hlt
    have huS := boundedWordHit_mem_of_lt (wiredDualFaceDirectionHead (B + 1)) R
      (wiredDualFaceInnerVertex (B + 1) x) l N w (lt_trans hlt ht)
    rw [← hstate u (Nat.le_of_lt hlt)] at huS
    exact boundedWordHit_avoids (freeDirectionHead (B + 1)) S x k N w u hlt ((hroots _).mp huS)
  exact Nat.le_antisymm hu_le ht_le

/-- Attaching a confined stopped branch preserves the correspondence of roots. -/
theorem wiredDualFace_historyRoots_iff_of_confined (B : ℕ)
    (x : FiniteWired.Active (B + 1)) (w : WalkDriver)
    (S : Set (FiniteWired.Active (B + 1))) (R : Set (WiredDualFace (B + 1)))
    (k : Cursor (FiniteWired.Active (B + 1))) (l : Cursor (WiredDualFace (B + 1))) (t : ℕ)
    (hroots : ∀ z, wiredDualFaceInnerVertex (B + 1) z ∈ R ↔ z ∈ S)
    (hconf : ∀ i < t, FiniteWired.inBox B
      (FiniteWired.site (wordState (freeDirectionHead (B + 1)) x k w i).1)) :
    ∀ z, wiredDualFaceInnerVertex (B + 1) z ∈
        historyRoots (wiredDualFaceDirectionHead (B + 1)) (wiredDualFaceInnerVertex (B + 1) x) R
          (stoppedDirectionHistory (fun _ => t) w) ↔
      z ∈ historyRoots (freeDirectionHead (B + 1)) x S
          (stoppedDirectionHistory (fun _ => t) w) := by
  letI : Quiver (FiniteWired.Active (B + 1)) := instructionQuiver (freeDirectionHead (B + 1))
  letI : Quiver (WiredDualFace (B + 1)) := instructionQuiver (wiredDualFaceDirectionHead (B + 1))
  let p := stoppedDirectionHistory (fun _ => t) w
  have hp : ∀ i < t, p.extend i = w i := by
    intro i hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
  have hf := wordTrace_eq_of_prefix (freeDirectionHead (B + 1)) x w p.extend t hp
  have hd := wordTrace_eq_of_prefix (wiredDualFaceDirectionHead (B + 1))
    (wiredDualFaceInnerVertex (B + 1) x) w p.extend t hp
  have he := wiredDualFace_wordTrace_loopErase_of_confined B x k l w t hconf
  have hm : (loopErase (historyTrace (freeDirectionHead (B + 1)) x p).2).vertices.map
        (wiredDualFaceInnerVertex (B + 1)) =
      (loopErase (historyTrace (wiredDualFaceDirectionHead (B + 1))
        (wiredDualFaceInnerVertex (B + 1) x) p).2).vertices := by
    change (loopErase (wordTrace (freeDirectionHead (B + 1)) x p.extend t).2).vertices.map _ =
      (loopErase (wordTrace (wiredDualFaceDirectionHead (B + 1))
        (wiredDualFaceInnerVertex (B + 1) x) p.extend t).2).vertices
    rw [hf, hd]
    exact he
  intro z
  change (wiredDualFaceInnerVertex (B + 1) z ∈ R ∨
    wiredDualFaceInnerVertex (B + 1) z ∈ (loopErase (historyTrace
      (wiredDualFaceDirectionHead (B + 1)) (wiredDualFaceInnerVertex (B + 1) x) p).2).vertices) ↔
    (z ∈ S ∨ z ∈ (loopErase (historyTrace (freeDirectionHead (B + 1)) x p).2).vertices)
  rw [hroots, ← hm, List.mem_map]
  constructor
  · rintro (h | ⟨v, hv, heq⟩)
    · exact Or.inl h
    · exact Or.inr ((wiredDualFaceInnerVertex_injective (B + 1) heq) ▸ hv)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨z, h, rfl⟩

/-- Confined first-hit branch histories agree and preserve the attached roots. -/
theorem rowBranchHistory_wiredDualFace_eq_of_confined (B N : ℕ)
    (x : ℕ → FiniteWired.Active (B + 1))
    (S : Set (FiniteWired.Active (B + 1))) (R : Set (WiredDualFace (B + 1)))
    (k : Cursor (FiniteWired.Active (B + 1))) (l : Cursor (WiredDualFace (B + 1)))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hroots : ∀ z, wiredDualFaceInnerVertex (B + 1) z ∈ R ↔ z ∈ S)
    (hhit : ∀ i < n,
      (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1 < N)
    (hconf : ∀ i < n, ∀ j <
      (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x i)
        (branchHistoryCursor (freeDirectionHead (B + 1)) x k i
          (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows i)) (rows i) j).1)) :
    rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (x i)) R l N rows n =
      rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n ∧
    ∀ z, wiredDualFaceInnerVertex (B + 1) z ∈
      branchHistoryRoots (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (x i)) R n
        (rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
          (fun i => wiredDualFaceInnerVertex (B + 1) (x i)) R l N rows n) ↔
      z ∈ branchHistoryRoots (freeDirectionHead (B + 1)) x S n
        (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n) := by
  induction n with
  | zero => exact ⟨rfl, hroots⟩
  | succ n ih =>
    have hpast : ∀ i < n,
        (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1 < N :=
      fun i hi => hhit i (Nat.lt_succ_of_lt hi)
    have hconfpast : ∀ i < n, ∀ j <
        (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (i + 1)).2.1,
        FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x i)
          (branchHistoryCursor (freeDirectionHead (B + 1)) x k i
            (rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows i)) (rows i) j).1) :=
      fun i hi => hconf i (Nat.lt_succ_of_lt hi)
    obtain ⟨hprev, hr⟩ := ih hpast hconfpast
    let y := fun i => wiredDualFaceInnerVertex (B + 1) (x i)
    let a := rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows n
    let T := branchHistoryRoots (freeDirectionHead (B + 1)) x S n a
    let U := branchHistoryRoots (wiredDualFaceDirectionHead (B + 1)) y R n a
    let ca := branchHistoryCursor (freeDirectionHead (B + 1)) x k n a
    let cb := branchHistoryCursor (wiredDualFaceDirectionHead (B + 1)) y l n a
    let t := boundedWordHit (freeDirectionHead (B + 1)) T (x n) ca N (rows n)
    have ht : t < N := hhit n (Nat.lt_succ_self n)
    have hc : ∀ j < t, FiniteWired.inBox B
        (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (x n) ca (rows n) j).1) :=
      hconf n (Nat.lt_succ_self n)
    have hr' : ∀ z, wiredDualFaceInnerVertex (B + 1) z ∈ U ↔ z ∈ T := by
      simpa only [hprev, a, T, U, y] using hr
    have htb := wiredDualFace_boundedWordHit_eq_of_confined B N (x n) (rows n) T U ca cb hr' ht hc
    have he : rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y R l N rows (n + 1) =
        rowBranchHistory (freeDirectionHead (B + 1)) x S k N rows (n + 1) := by
      change (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y R l N rows n,
        stoppedDirectionHistory (boundedWordHit (wiredDualFaceDirectionHead (B + 1))
          (branchHistoryRoots (wiredDualFaceDirectionHead (B + 1)) y R n
            (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y R l N rows n))
          (y n) (branchHistoryCursor (wiredDualFaceDirectionHead (B + 1)) y l n
            (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y R l N rows n)) N) (rows n)) =
        (a, stoppedDirectionHistory (boundedWordHit (freeDirectionHead (B + 1)) T (x n) ca N) (rows n))
      rw [hprev]
      change (a, stoppedDirectionHistory (boundedWordHit (wiredDualFaceDirectionHead (B + 1)) U
        (y n) cb N) (rows n)) = (a, stoppedDirectionHistory (fun _ => t) (rows n))
      simp only [stoppedDirectionHistory]
      rw [htb]
    refine ⟨he, ?_⟩
    rw [he]
    change ∀ z, wiredDualFaceInnerVertex (B + 1) z ∈
      historyRoots (wiredDualFaceDirectionHead (B + 1)) (y n) U
          (stoppedDirectionHistory (fun _ => t) (rows n)) ↔
        z ∈ historyRoots (freeDirectionHead (B + 1)) (x n) T
          (stoppedDirectionHistory (fun _ => t) (rows n))
    exact wiredDualFace_historyRoots_iff_of_confined B (x n) (rows n) T U ca cb t hr' hc

end
end FiniteAvalanches.Wilson.Lattice
