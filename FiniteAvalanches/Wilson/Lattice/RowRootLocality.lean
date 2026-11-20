import FiniteAvalanches.Wilson.Lattice.OriginSamplerLimit

/-! Local dependence of finite Wilson row histories on their initial roots. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- For a fixed sequence of branches, root-set agreement at a vertex is
preserved when the same branches are attached to both root sets. -/
theorem branchHistoryRoots_mem_iff_of_roots_mem_iff {V : Type*} [DecidableEq V]
    (head : V → FiniteWired.Direction → V) (x : ℕ → V) (R S : Set V)
    (n : ℕ) (h : BranchHistory n) (z : V) (hz : z ∈ S ↔ z ∈ R) :
    z ∈ branchHistoryRoots head x S n h ↔ z ∈ branchHistoryRoots head x R n h := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    simp only [branchHistoryRoots, historyRoots, Set.mem_union, Set.mem_setOf_eq]
    exact or_congr (ih h.1) Iff.rfl

/-- The first bounded lattice hit is unchanged if root membership agrees on
the stopped walk segment. -/
theorem lattice_boundedWordHit_eq_of_confined (B N : ℕ) (x : Site 2)
    (w : WalkDriver) (R S : Set (Site 2)) (k : Cursor (Site 2))
    (hroots : ∀ z, FiniteWired.inBox B z → (z ∈ S ↔ z ∈ R))
    (ht : boundedWordHit latticeDirectionHead R x k N w < N)
    (hbox : ∀ i ≤ boundedWordHit latticeDirectionHead R x k N w,
      FiniteWired.inBox B (position x w i)) :
    boundedWordHit latticeDirectionHead S x k N w =
      boundedWordHit latticeDirectionHead R x k N w := by
  let t := boundedWordHit latticeDirectionHead R x k N w
  let u := boundedWordHit latticeDirectionHead S x k N w
  have hstate (i : ℕ) : (wordState latticeDirectionHead x k w i).1 = position x w i :=
    wordState_lattice_position x k w i
  have hu_le : u ≤ t := by
    apply Nat.le_of_not_gt
    intro hlt
    have ha := boundedWordHit_avoids latticeDirectionHead S x k N w t hlt
    apply ha
    rw [hstate]
    apply (hroots _ (hbox t le_rfl)).mpr
    have hm := boundedWordHit_mem_of_lt latticeDirectionHead R x k N w ht
    simpa only [hstate] using hm
  have ht_le : t ≤ u := by
    apply Nat.le_of_not_gt
    intro hlt
    have hm := boundedWordHit_mem_of_lt latticeDirectionHead S x k N w (lt_trans hlt ht)
    have ha := boundedWordHit_avoids latticeDirectionHead R x k N w u hlt
    apply ha
    rw [hstate]
    apply (hroots _ (hbox u (Nat.le_of_lt hlt))).mp
    simpa only [hstate] using hm
  exact Nat.le_antisymm hu_le ht_le

/-- A finite lattice row exploration confined to a box is unchanged when the
initial root set is modified only outside that box. -/
theorem rowBranchHistory_eq_of_confined_roots (B N : ℕ) (x : ℕ → Site 2)
    (R S : Set (Site 2)) (k : Cursor (Site 2)) (rows : ℕ → WalkDriver) (n : ℕ)
    (hroots : ∀ z, FiniteWired.inBox B z → (z ∈ S ↔ z ∈ R))
    (hhit : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x R k N rows (i + 1)).2.1 < N)
    (hbox : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x R k N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j)) :
    rowBranchHistory latticeDirectionHead x S k N rows n =
      rowBranchHistory latticeDirectionHead x R k N rows n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := ih (fun i hi => hhit i (Nat.lt_succ_of_lt hi))
      (fun i hi => hbox i (Nat.lt_succ_of_lt hi))
    let h := rowBranchHistory latticeDirectionHead x R k N rows n
    let T := branchHistoryRoots latticeDirectionHead x R n h
    let U := branchHistoryRoots latticeDirectionHead x S n h
    let c := branchHistoryCursor latticeDirectionHead x k n h
    have hr : ∀ z, FiniteWired.inBox B z → (z ∈ U ↔ z ∈ T) := by
      intro z hz
      exact branchHistoryRoots_mem_iff_of_roots_mem_iff latticeDirectionHead x R S n h z (hroots z hz)
    have ht : boundedWordHit latticeDirectionHead T (x n) c N (rows n) < N :=
      hhit n (Nat.lt_succ_self n)
    have hb : ∀ j ≤ boundedWordHit latticeDirectionHead T (x n) c N (rows n),
        FiniteWired.inBox B (position (x n) (rows n) j) := hbox n (Nat.lt_succ_self n)
    have he := lattice_boundedWordHit_eq_of_confined B N (x n) (rows n) T U c hr ht hb
    change (rowBranchHistory latticeDirectionHead x S k N rows n,
      stoppedDirectionHistory (boundedWordHit latticeDirectionHead
        (branchHistoryRoots latticeDirectionHead x S n
          (rowBranchHistory latticeDirectionHead x S k N rows n)) (x n)
        (branchHistoryCursor latticeDirectionHead x k n
          (rowBranchHistory latticeDirectionHead x S k N rows n)) N) (rows n)) = _
    rw [hp]
    change (h, stoppedDirectionHistory (boundedWordHit latticeDirectionHead U (x n) c N) (rows n)) =
      (h, stoppedDirectionHistory (boundedWordHit latticeDirectionHead T (x n) c N) (rows n))
    simp only [stoppedDirectionHistory]
    rw [he]

end
end FiniteAvalanches.Wilson.Lattice
