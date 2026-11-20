import FiniteAvalanches.Wilson.Lattice.WiredWordCoupling
import FiniteAvalanches.Wilson.Lattice.RowBranchHistory

/-! First-hit branches coupled between a wired box and the lattice. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb Quiver FiniteAvalanches.Wilson FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Confined walks with matching root sets have the same first-hit time. -/
theorem wired_boundedWordHit_eq_of_confined (B N : ℕ) (x : Site 2) (w : WalkDriver)
    (S : Set (FiniteWired.Vertex B)) (R : Set (Site 2))
    (k : Cursor (FiniteWired.Vertex B)) (t : ℕ)
    (hroots : ∀ z, FiniteWired.inBox B z → (wiredSite B z ∈ S ↔ z ∈ R))
    (hhit : hitTime R x w = some t) (ht : t < N)
    (hbox : ∀ i ≤ t, FiniteWired.inBox B (position x w i)) :
    boundedWordHit (wiredHead B) S (wiredSite B x) k N w = t := by
  let u := boundedWordHit (wiredHead B) S (wiredSite B x) k N w
  obtain ⟨htR, hfirst⟩ := (hitTime_eq_some_iff R x w t).mp hhit
  have hstate := wiredWordState_eq_of_confined B x w k t hbox
  have hu_le : u ≤ t := by
    apply Nat.le_of_not_gt
    intro hlt
    have ha := boundedWordHit_avoids (wiredHead B) S (wiredSite B x) k N w t hlt
    apply ha
    rw [hstate t le_rfl]
    exact (hroots _ (hbox t le_rfl)).mpr htR
  have ht_le : t ≤ u := by
    apply Nat.le_of_not_gt
    intro hlt
    have huS := boundedWordHit_mem_of_lt (wiredHead B) S (wiredSite B x) k N w
      (lt_trans hlt ht)
    rw [hstate u (Nat.le_of_lt hlt)] at huS
    exact hfirst u hlt ((hroots _ (hbox u (Nat.le_of_lt hlt))).mp huS)
  exact Nat.le_antisymm hu_le ht_le

/-- A stopped confined branch has the same loop-erased vertices in the wired
box and in the lattice. -/
theorem wired_historyTrace_loopErase_of_confined (B : ℕ) (x : Site 2)
    (w : WalkDriver) (k : Cursor (FiniteWired.Vertex B)) (t : ℕ)
    (hbox : ∀ i ≤ t, FiniteWired.inBox B (position x w i)) :
    letI : Quiver (FiniteWired.Vertex B) := instructionQuiver (wiredHead B)
    ((loopErase (historyTrace (wiredHead B) (wiredSite B x)
      (stoppedDirectionHistory (fun _ => t) w)).2).vertices.map (wiredVertexSite B)) =
        walkErase x w t := by
  letI : Quiver (FiniteWired.Vertex B) := instructionQuiver (wiredHead B)
  let p := stoppedDirectionHistory (fun _ => t) w
  have hp : ∀ i < t, p.extend i = w i := by
    intro i hi
    simp only [p, stoppedDirectionHistory, DirectionHistory.extend, dif_pos hi]
  have he := wordTrace_eq_of_prefix (wiredHead B) (wiredSite B x) w p.extend t hp
  change (loopErase (wordTrace (wiredHead B) (wiredSite B x) p.extend t).2).vertices.map
    (wiredVertexSite B) = walkErase x w t
  rw [he]
  exact wiredWordTrace_loopErase_of_confined B x w k t hbox

/-- Attaching a confined branch preserves agreement of the two root sets at
all sites of the wired box. -/
theorem wired_historyRoots_iff_of_confined (B : ℕ) (x : Site 2) (w : WalkDriver)
    (S : Set (FiniteWired.Vertex B)) (R : Set (Site 2))
    (k : Cursor (FiniteWired.Vertex B)) (t : ℕ)
    (hroots : ∀ z, FiniteWired.inBox B z → (wiredSite B z ∈ S ↔ z ∈ R))
    (hbox : ∀ i ≤ t, FiniteWired.inBox B (position x w i)) :
    ∀ z, FiniteWired.inBox B z →
      (wiredSite B z ∈ historyRoots (wiredHead B) (wiredSite B x) S
          (stoppedDirectionHistory (fun _ => t) w) ↔
       z ∈ historyRoots latticeDirectionHead x R (stoppedDirectionHistory (fun _ => t) w)) := by
  letI : Quiver (FiniteWired.Vertex B) := instructionQuiver (wiredHead B)
  letI : Quiver (Site 2) := instructionQuiver latticeDirectionHead
  let p := stoppedDirectionHistory (fun _ => t) w
  have hw := wired_historyTrace_loopErase_of_confined B x w k t hbox
  have hl := historyTrace_stopped_loopErase_vertices x w t
  change (loopErase (historyTrace (wiredHead B) (wiredSite B x) p).2).vertices.map
    (wiredVertexSite B) = walkErase x w t at hw
  change (loopErase (historyTrace latticeDirectionHead x p).2).vertices = walkErase x w t at hl
  intro z hz
  change (wiredSite B z ∈ S ∨
    wiredSite B z ∈ (loopErase (historyTrace (wiredHead B) (wiredSite B x) p).2).vertices) ↔
    (z ∈ R ∨ z ∈ (loopErase (historyTrace latticeDirectionHead x p).2).vertices)
  rw [hroots z hz, hl, ← hw, List.mem_map]
  constructor
  · rintro (hzR | hzpath)
    · exact Or.inl hzR
    · exact Or.inr ⟨wiredSite B z, hzpath, wiredVertexSite_wiredSite B z hz⟩
  · rintro (hzR | ⟨v, hv, he⟩)
    · exact Or.inl hzR
    · have hv' : v = wiredSite B z := wiredVertexSite_injective B
        (he.trans (wiredVertexSite_wiredSite B z hz).symm)
      exact Or.inr (hv' ▸ hv)

/-- Confined lattice branch histories agree exactly with their wired-box
counterparts and preserve the correspondence of the attached root sets. -/
theorem rowBranchHistory_wired_eq_of_confined (B N : ℕ) (x : ℕ → Site 2)
    (S : Set (FiniteWired.Vertex B)) (R : Set (Site 2))
    (kb : Cursor (FiniteWired.Vertex B)) (ka : Cursor (Site 2))
    (rows : ℕ → WalkDriver) (n : ℕ)
    (hroots : ∀ z, FiniteWired.inBox B z → (wiredSite B z ∈ S ↔ z ∈ R))
    (hhit : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1 < N)
    (hbox : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x R ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j)) :
    rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) S kb N rows n =
      rowBranchHistory latticeDirectionHead x R ka N rows n ∧
    ∀ z, FiniteWired.inBox B z →
      (wiredSite B z ∈ branchHistoryRoots (wiredHead B) (fun i => wiredSite B (x i)) S n
          (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) S kb N rows n) ↔
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
    let U := branchHistoryRoots (wiredHead B) (fun i => wiredSite B (x i)) S n a
    let ca := branchHistoryCursor latticeDirectionHead x ka n a
    let cb := branchHistoryCursor (wiredHead B) (fun i => wiredSite B (x i)) kb n a
    let t := boundedWordHit latticeDirectionHead T (x n) ca N (rows n)
    have ht : t < N := hhit n (Nat.lt_succ_self n)
    have hconf : ∀ j ≤ t, FiniteWired.inBox B (position (x n) (rows n) j) :=
      hbox n (Nat.lt_succ_self n)
    have hr' : ∀ z, FiniteWired.inBox B z → (wiredSite B z ∈ U ↔ z ∈ T) := by
      simpa only [hprev, a, T, U] using hr
    have htime := hitTime_eq_boundedWordHit T (x n) ca N (rows n) ht
    have htb := wired_boundedWordHit_eq_of_confined B N (x n) (rows n) U T cb t
      hr' htime ht hconf
    have he : rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) S kb N rows (n + 1) =
        rowBranchHistory latticeDirectionHead x R ka N rows (n + 1) := by
      change (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) S kb N rows n,
        stoppedDirectionHistory (boundedWordHit (wiredHead B)
          (branchHistoryRoots (wiredHead B) (fun i => wiredSite B (x i)) S n
            (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) S kb N rows n))
          (wiredSite B (x n)) (branchHistoryCursor (wiredHead B) (fun i => wiredSite B (x i)) kb n
            (rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) S kb N rows n)) N) (rows n)) =
        (a, stoppedDirectionHistory (boundedWordHit latticeDirectionHead T (x n) ca N) (rows n))
      rw [hprev]
      change (a, stoppedDirectionHistory (boundedWordHit (wiredHead B) U (wiredSite B (x n)) cb N) (rows n)) =
        (a, stoppedDirectionHistory (boundedWordHit latticeDirectionHead T (x n) ca N) (rows n))
      change (a, stoppedDirectionHistory (boundedWordHit (wiredHead B) U (wiredSite B (x n)) cb N) (rows n)) =
        (a, stoppedDirectionHistory (fun _ => t) (rows n))
      simp only [stoppedDirectionHistory]
      rw [htb]
    refine ⟨he, ?_⟩
    rw [he]
    change ∀ z, FiniteWired.inBox B z →
      (wiredSite B z ∈ historyRoots (wiredHead B) (wiredSite B (x n)) U
          (stoppedDirectionHistory (fun _ => t) (rows n)) ↔
       z ∈ historyRoots latticeDirectionHead (x n) T
          (stoppedDirectionHistory (fun _ => t) (rows n)))
    exact wired_historyRoots_iff_of_confined B (x n) (rows n) U T cb t hr' hconf

end
end FiniteAvalanches.Wilson.Lattice
