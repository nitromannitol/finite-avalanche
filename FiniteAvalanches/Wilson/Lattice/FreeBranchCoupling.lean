import FiniteAvalanches.Wilson.Lattice.FreeWordCoupling
import FiniteAvalanches.Wilson.Lattice.RowBranchHistory

/-! First-hit branches coupled between a free box and the lattice. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Confined walks with matching root sets have the same first-hit time. -/
theorem free_boundedWordHit_eq_of_confined (B N : ℕ) (x : Site 2) (w : WalkDriver)
    (S : Set (FiniteWired.Active B)) (R : Set (Site 2))
    (k : Cursor (FiniteWired.Active B)) (t : ℕ)
    (hroots : ∀ z, FiniteWired.inBox B z → (freeSite B z ∈ S ↔ z ∈ R))
    (hhit : hitTime R x w = some t) (ht : t < N)
    (hbox : ∀ i ≤ t, FiniteWired.inBox B (position x w i)) :
    boundedWordHit (freeDirectionHead B) S (freeSite B x) k N w = t := by
  let u := boundedWordHit (freeDirectionHead B) S (freeSite B x) k N w
  obtain ⟨htR, hfirst⟩ := (hitTime_eq_some_iff R x w t).mp hhit
  have hstate := freeWordState_eq_of_confined B x w k t hbox
  have hu_le : u ≤ t := by
    apply Nat.le_of_not_gt
    intro hlt
    have ha := boundedWordHit_avoids (freeDirectionHead B) S (freeSite B x) k N w t hlt
    apply ha
    rw [hstate t le_rfl]
    exact (hroots _ (hbox t le_rfl)).mpr htR
  have ht_le : t ≤ u := by
    apply Nat.le_of_not_gt
    intro hlt
    have huS := boundedWordHit_mem_of_lt (freeDirectionHead B) S (freeSite B x) k N w
      (lt_trans hlt ht)
    rw [hstate u (Nat.le_of_lt hlt)] at huS
    exact hfirst u hlt ((hroots _ (hbox u (Nat.le_of_lt hlt))).mp huS)
  exact Nat.le_antisymm hu_le ht_le

/-- A stopped confined branch has the same loop-erased vertices in the free
box and in the lattice. -/
theorem free_historyTrace_loopErase_of_confined (B : ℕ) (x : Site 2)
    (w : WalkDriver) (k : Cursor (FiniteWired.Active B)) (t : ℕ)
    (hbox : ∀ i ≤ t, FiniteWired.inBox B (position x w i)) :
    letI : Quiver (FiniteWired.Active B) := instructionQuiver (freeDirectionHead B)
    ((loopErase (historyTrace (freeDirectionHead B) (freeSite B x)
      (stoppedDirectionHistory (fun _ => t) w)).2).vertices.map (FiniteWired.site : FiniteWired.Active B → Site 2)) =
        walkErase x w t := by
  letI : Quiver (FiniteWired.Active B) := instructionQuiver (freeDirectionHead B)
  let p := stoppedDirectionHistory (fun _ => t) w
  have hp : ∀ i < t, p.extend i = w i := by
    intro i hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
  have he := wordTrace_eq_of_prefix (freeDirectionHead B) (freeSite B x) w p.extend t hp
  change (loopErase (wordTrace (freeDirectionHead B) (freeSite B x) p.extend t).2).vertices.map
    (FiniteWired.site : FiniteWired.Active B → Site 2) = walkErase x w t
  rw [he]
  exact freeWordTrace_loopErase_of_confined B x w k t hbox

/-- Attaching a confined branch preserves agreement of the two root sets at
all sites of the free box. -/
theorem free_historyRoots_iff_of_confined (B : ℕ) (x : Site 2) (w : WalkDriver)
    (S : Set (FiniteWired.Active B)) (R : Set (Site 2))
    (k : Cursor (FiniteWired.Active B)) (t : ℕ)
    (hroots : ∀ z, FiniteWired.inBox B z → (freeSite B z ∈ S ↔ z ∈ R))
    (hbox : ∀ i ≤ t, FiniteWired.inBox B (position x w i)) :
    ∀ z, FiniteWired.inBox B z →
      (freeSite B z ∈ historyRoots (freeDirectionHead B) (freeSite B x) S
          (stoppedDirectionHistory (fun _ => t) w) ↔
       z ∈ historyRoots latticeDirectionHead x R (stoppedDirectionHistory (fun _ => t) w)) := by
  letI : Quiver (FiniteWired.Active B) := instructionQuiver (freeDirectionHead B)
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  let p := stoppedDirectionHistory (fun _ => t) w
  have hw := free_historyTrace_loopErase_of_confined B x w k t hbox
  have hl := historyTrace_stopped_loopErase_vertices x w t
  change (loopErase (historyTrace (freeDirectionHead B) (freeSite B x) p).2).vertices.map
    (FiniteWired.site : FiniteWired.Active B → Site 2) = walkErase x w t at hw
  change (loopErase (historyTrace latticeDirectionHead x p).2).vertices = walkErase x w t at hl
  intro z hz
  change (freeSite B z ∈ S ∨
    freeSite B z ∈ (loopErase (historyTrace (freeDirectionHead B) (freeSite B x) p).2).vertices) ↔
    (z ∈ R ∨ z ∈ (loopErase (historyTrace latticeDirectionHead x p).2).vertices)
  rw [hroots z hz, hl, ← hw, List.mem_map]
  constructor
  · rintro (hzR | hzpath)
    · exact Or.inl hzR
    · exact Or.inr ⟨freeSite B z, hzpath, site_freeSite_of_inBox B z hz⟩
  · rintro (hzR | ⟨v, hv, he⟩)
    · exact Or.inl hzR
    · have hv' : v = freeSite B z := FiniteWired.site_injective B
        (he.trans (site_freeSite_of_inBox B z hz).symm)
      exact Or.inr (hv' ▸ hv)

/-- Confined lattice branch histories agree exactly with their free-box
counterparts and preserve the correspondence of the attached root sets. -/
theorem rowBranchHistory_free_eq_of_confined (B N : ℕ) (x : ℕ → Site 2)
    (S : Set (FiniteWired.Active B)) (R : Set (Site 2))
    (kb : Cursor (FiniteWired.Active B)) (ka : Cursor (Site 2))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hroots : ∀ z, FiniteWired.inBox B z → (freeSite B z ∈ S ↔ z ∈ R))
    (hhit : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1 < N)
    (hbox : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j)) :
    rowBranchHistory (freeDirectionHead B) (fun i => freeSite B (x i)) S kb N rows n =
      rowBranchHistory latticeDirectionHead x R ka N rows n ∧
    ∀ z, FiniteWired.inBox B z →
      (freeSite B z ∈ branchHistoryRoots (freeDirectionHead B) (fun i => freeSite B (x i)) S n
          (rowBranchHistory (freeDirectionHead B) (fun i => freeSite B (x i)) S kb N rows n) ↔
       z ∈ branchHistoryRoots latticeDirectionHead x R n
          (rowBranchHistory latticeDirectionHead x R ka N rows n)) := by
  induction n with
  | zero => exact ⟨rfl, hroots⟩
  | succ n ih =>
    have hpast : ∀ i < n,
        (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1 < N :=
      fun i hi => hhit i (Nat.lt_succ_of_lt hi)
    have hboxpast : ∀ i < n, ∀ j ≤
        (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1,
        FiniteWired.inBox B (position (x i) (rows i) j) :=
      fun i hi => hbox i (Nat.lt_succ_of_lt hi)
    obtain ⟨hprev, hr⟩ := ih hpast hboxpast
    let a := rowBranchHistory latticeDirectionHead x R ka N rows n
    let T := branchHistoryRoots latticeDirectionHead x R n a
    let U := branchHistoryRoots (freeDirectionHead B) (fun i => freeSite B (x i)) S n a
    let ca := branchHistoryCursor latticeDirectionHead x ka n a
    let cb := branchHistoryCursor (freeDirectionHead B) (fun i => freeSite B (x i)) kb n a
    let t := boundedWordHit latticeDirectionHead T (x n) ca N (rows n)
    have ht : t < N := hhit n (Nat.lt_succ_self n)
    have hconf : ∀ j ≤ t, FiniteWired.inBox B (position (x n) (rows n) j) :=
      hbox n (Nat.lt_succ_self n)
    have hr' : ∀ z, FiniteWired.inBox B z → (freeSite B z ∈ U ↔ z ∈ T) := by
      simpa only [hprev, a, T, U] using hr
    have htime := hitTime_eq_boundedWordHit T (x n) ca N (rows n) ht
    have htb := free_boundedWordHit_eq_of_confined B N (x n) (rows n) U T cb t
      hr' htime ht hconf
    have he : rowBranchHistory (freeDirectionHead B) (fun i => freeSite B (x i)) S kb N rows (n + 1) =
        rowBranchHistory latticeDirectionHead x R ka N rows (n + 1) := by
      change (rowBranchHistory (freeDirectionHead B) (fun i => freeSite B (x i)) S kb N rows n,
        stoppedDirectionHistory (boundedWordHit (freeDirectionHead B)
          (branchHistoryRoots (freeDirectionHead B) (fun i => freeSite B (x i)) S n
            (rowBranchHistory (freeDirectionHead B) (fun i => freeSite B (x i)) S kb N rows n))
          (freeSite B (x n)) (branchHistoryCursor (freeDirectionHead B) (fun i => freeSite B (x i)) kb n
            (rowBranchHistory (freeDirectionHead B) (fun i => freeSite B (x i)) S kb N rows n)) N) (rows n)) =
        (a, stoppedDirectionHistory (boundedWordHit latticeDirectionHead T (x n) ca N) (rows n))
      rw [hprev]
      change (a, stoppedDirectionHistory (boundedWordHit (freeDirectionHead B) U (freeSite B (x n)) cb N) (rows n)) =
        (a, stoppedDirectionHistory (boundedWordHit latticeDirectionHead T (x n) ca N) (rows n))
      change (a, stoppedDirectionHistory (boundedWordHit (freeDirectionHead B) U (freeSite B (x n)) cb N) (rows n)) =
        (a, stoppedDirectionHistory (fun _ => t) (rows n))
      simp only [stoppedDirectionHistory]
      rw [htb]
    refine ⟨he, ?_⟩
    rw [he]
    change ∀ z, FiniteWired.inBox B z →
      (freeSite B z ∈ historyRoots (freeDirectionHead B) (freeSite B (x n)) U
          (stoppedDirectionHistory (fun _ => t) (rows n)) ↔
       z ∈ historyRoots latticeDirectionHead (x n) T
          (stoppedDirectionHistory (fun _ => t) (rows n)))
    exact free_historyRoots_iff_of_confined B (x n) (rows n) U T cb t hr' hconf

end
end FiniteAvalanches.Wilson.Lattice
