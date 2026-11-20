import FiniteAvalanches.Wilson.Lattice.WiredDualFaceAvoidBoundary
import FiniteAvalanches.Wilson.Lattice.FreeSafeHistoryLaw

/-! Safe face-square row histories have probabilities tending to one. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Face-square row histories that complete and avoid the outer boundary. -/
def wiredDualFaceSafeRowEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) : Set (ℕ → WalkDriver) :=
  {rows | ∃ N, BranchHistory.HitsBefore N n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
        (wiredDualFaceOriginAndBoundary B) k N rows n) ∧
    BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1))
      (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
      (wiredDualFaceOuterBoundary B) n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
        (wiredDualFaceOriginAndBoundary B) k N rows n)}

/-- Safe face-square row events are measurable. -/
theorem measurableSet_wiredDualFaceSafeRowEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    MeasurableSet (wiredDualFaceSafeRowEvent B x k n) := by
  let y := fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))
  have he : wiredDualFaceSafeRowEvent B x k n = ⋃ N : ℕ,
      {rows | BranchHistory.HitsBefore N n
          (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
            (wiredDualFaceOriginAndBoundary B) k N rows n) ∧
        BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1)) y
          (wiredDualFaceOuterBoundary B) n
          (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
            (wiredDualFaceOriginAndBoundary B) k N rows n)} := by
    ext rows
    simp only [wiredDualFaceSafeRowEvent, Set.mem_setOf_eq, Set.mem_iUnion, y]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun rows => rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
      (wiredDualFaceOriginAndBoundary B) k N rows n)
    (fun a => measurableSet_rowBranchHistory_eq (wiredDualFaceDirectionHead (B + 1)) y
      (wiredDualFaceOriginAndBoundary B) k N n
      (fun i (rows : ℕ → WalkDriver) => rows i) (fun i => measurable_pi_apply i) a)
    (fun a => BranchHistory.HitsBefore N n a ∧
      BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1)) y (wiredDualFaceOuterBoundary B) n a)

/-- Safe finite face-square row histories occur eventually almost surely. -/
theorem wilsonRows_ae_eventually_wiredDualFaceSafeRowEvent (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop, rows ∈ wiredDualFaceSafeRowEvent B x (kc B) n := by
  filter_upwards [wilsonRows_ae_eventually_freeOrigin_history_eq x ka kb n] with rows hrows
  obtain ⟨T, hT, heq⟩ := hrows
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
  have hfconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows (i + 1)).2.1,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (xf i)
        (branchHistoryCursor (freeDirectionHead (B + 1)) xf (kb B) i
          (rowBranchHistory (freeDirectionHead (B + 1)) xf S (kb B) T rows i)) (rows i) j).1) := by
    intro i hi j hj
    have hjT : j < T := lt_of_le_of_lt hj (hfhit i hi)
    have hbox' : ∀ s ≤ j, FiniteWired.inBox (B + 1) (position (x i) (rows i) s) := by
      intro s hs d
      have hh := hbox i hi s (lt_of_le_of_lt hs hjT) d
      constructor <;> omega
    rw [freeWordState_eq_of_confined (B + 1) (x i) (rows i) _ j hbox' j le_rfl,
      site_freeSite_of_inBox _ _ (hbox' j le_rfl)]
    exact hbox i hi j hjT
  have hface := rowBranchHistory_wiredDualFace_eq_of_confined B T xf S
    (wiredDualFaceOriginAndBoundary B) (kb B) (kc B) rows n
    (wiredDualFaceOriginAndBoundary_inner_iff B) hfhit
    (fun i hi j hj => hfconf i hi j (Nat.le_of_lt hj))
  refine ⟨T, ?_, rowBranchHistory_wiredDualFace_endsAvoid_of_confined B T xf S
    (wiredDualFaceOriginAndBoundary B) (kb B) (kc B) rows n hface.1 hfconf⟩
  rw [hface.1, heq']
  exact (rowBranchHistory_hitsBefore_iff latticeDirectionHead x {0} ka T n rows).mpr hT

/-- The probabilities of safe face-square row histories tend to one. -/
theorem wiredDualFaceSafeRowEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    Tendsto (fun B => wilsonRows (wiredDualFaceSafeRowEvent B x (kc B) n)) atTop (nhds 1) := by
  have hpoint : ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop,
      rows ∈ wiredDualFaceSafeRowEvent B x (kc B) n ↔ rows ∈ (Set.univ : Set (ℕ → WalkDriver)) := by
    filter_upwards [wilsonRows_ae_eventually_wiredDualFaceSafeRowEvent x ka kb kc n] with rows hrows
    filter_upwards [hrows] with B hB
    simp only [Set.mem_univ, iff_true]
    exact hB
  have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (μ := wilsonRows) (A := Set.univ) (As := fun B => wiredDualFaceSafeRowEvent B x (kc B) n)
    MeasurableSet.univ (fun B => measurableSet_wiredDualFaceSafeRowEvent B x (kc B) n) hpoint
  simpa only [measure_univ] using ht

end
end FiniteAvalanches.Wilson.Lattice
