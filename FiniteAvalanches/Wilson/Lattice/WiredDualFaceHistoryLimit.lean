import FiniteAvalanches.Wilson.Lattice.WiredDualFaceBranchCoupling
import FiniteAvalanches.Wilson.Lattice.FreeOriginHistory

/-! Almost-sure comparison of confined face-square and lattice Wilson histories. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Equal row histories have equal initial segments, even on different vertex types. -/
theorem rowBranchHistory_prefix_eq {V W : Type*} [DecidableEq V] [DecidableEq W]
    (head : V → FiniteWired.Direction → V) (head' : W → FiniteWired.Direction → W)
    (x : ℕ → V) (y : ℕ → W) (S : Set V) (R : Set W)
    (k : Cursor V) (l : Cursor W) (N : ℕ) (rows : ℕ → WalkDriver) (n : ℕ)
    (h : rowBranchHistory head x S k N rows n = rowBranchHistory head' y R l N rows n) :
    ∀ m ≤ n, rowBranchHistory head x S k N rows m = rowBranchHistory head' y R l N rows m := by
  induction n with
  | zero =>
    intro m hm
    have : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    intro m hm
    by_cases hmn : m = n + 1
    · subst m
      exact h
    · have hn : m ≤ n := by omega
      have hp : rowBranchHistory head x S k N rows n =
          rowBranchHistory head' y R l N rows n := congrArg Prod.fst h
      exact ih hp m hn

/-- Origin and exterior roots in the dual face square. -/
def wiredDualFaceOriginAndBoundary (B : ℕ) : Set (WiredDualFace (B + 1)) :=
  {v | wiredDualFaceSite v = 0} ∪ {v | ¬FiniteWired.inBox B (wiredDualFaceSite v)}

/-- Centered and face-square origin-plus-boundary roots agree under inclusion. -/
theorem wiredDualFaceOriginAndBoundary_inner_iff (B : ℕ) (x : FiniteWired.Active (B + 1)) :
    wiredDualFaceInnerVertex (B + 1) x ∈ wiredDualFaceOriginAndBoundary B ↔
      x ∈ freeOriginAndBoundary B := by
  simp only [wiredDualFaceOriginAndBoundary, freeOriginAndBoundary, freeOuterBoundary,
    Set.mem_union, Set.mem_setOf_eq, wiredDualFaceSite_innerVertex]

/-- For every finite query family, the face and lattice origin-rooted histories
coincide almost surely in all sufficiently large squares. -/
theorem wilsonRows_ae_eventually_wiredDualFace_history_eq (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ T,
      (∀ i < n, (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1 < T) ∧
      ∀ᶠ B : ℕ in atTop,
        rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
          (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
          (wiredDualFaceOriginAndBoundary B) (kc B) T rows n =
        rowBranchHistory latticeDirectionHead x {0} ka T rows n := by
  filter_upwards [wilsonRows_ae_eventually_freeOrigin_history_eq x ka kb n] with rows hrows
  obtain ⟨T, hT, heq⟩ := hrows
  refine ⟨T, hT, ?_⟩
  filter_upwards [heq, eventually_walkSegments_inBox x rows n T] with B heq' hbox
  let xf := fun i => freeSite (B + 1) (x i)
  let S := freeOriginAndBoundary B
  have hprefix : ∀ m ≤ n, rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows m =
      rowBranchHistory latticeDirectionHead x {0} ka T rows m :=
    rowBranchHistory_prefix_eq _ _ _ _ _ _ _ _ _ _ _ heq'
  have hfhit : ∀ i < n,
      (rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows (i + 1)).2.1 < T := by
    intro i hi
    rw [hprefix (i + 1) (by omega)]
    exact hT i hi
  have hfconf : ∀ i < n, ∀ j <
      (rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows (i + 1)).2.1,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (xf i)
        (branchHistoryCursor (freeDirectionHead (B + 1)) xf (kb B) i
          (rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows i)) (rows i) j).1) := by
    intro i hi j hj
    have hjT : j < T := lt_trans hj (hfhit i hi)
    have hbox' : ∀ s ≤ j, FiniteWired.inBox (B + 1) (position (x i) (rows i) s) := by
      intro s hs d
      have hh := hbox i hi s (lt_of_le_of_lt hs hjT) d
      constructor <;> omega
    rw [freeWordState_eq_of_confined (B + 1) (x i) (rows i) _ j hbox' j le_rfl,
      site_freeSite_of_inBox _ _ (hbox' j le_rfl)]
    exact hbox i hi j hjT
  have hface := rowBranchHistory_wiredDualFace_eq_of_confined B T xf S
    (wiredDualFaceOriginAndBoundary B) (kb B) (kc B) rows n
    (wiredDualFaceOriginAndBoundary_inner_iff B) hfhit hfconf
  exact hface.1.trans heq'

end
end FiniteAvalanches.Wilson.Lattice
