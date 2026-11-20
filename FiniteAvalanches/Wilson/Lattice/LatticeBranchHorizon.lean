import FiniteAvalanches.Wilson.Lattice.WiredBranchCoupling
import FiniteAvalanches.Wilson.Lattice.RowBranchHorizon

/-! Finite recurrent lattice branch histories and their eventual confinement. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Attaching recorded branches preserves all initially prescribed roots. -/
theorem branchHistoryRoots_initial_subset (head : V → FiniteWired.Direction → V)
    (x : ℕ → V) (R : Set V) (n : ℕ) (a : BranchHistory n) :
    R ⊆ branchHistoryRoots head x R n a := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact (ih a.1).trans Set.subset_union_left

/-- If every row reaches one initial root from every start, any finite family
of its lattice Wilson branches fits into a common finite horizon. -/
theorem exists_lattice_row_horizon_of_hits (x : ℕ → Site 2) (R : Set (Site 2))
    (k : Cursor (Site 2)) (rows : ℕ → WalkDriver) (r : Site 2) (hr : r ∈ R)
    (hh : ∀ i y, ∃ j, position y (rows i) j = r) (n : ℕ) :
    ∃ N, ∀ i < n,
      (rowBranchHistory latticeDirectionHead x R k N rows (i + 1)).2.1 < N := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨N, hN⟩ := ih
    let a := rowBranchHistory latticeDirectionHead x R k N rows n
    let S := branchHistoryRoots latticeDirectionHead x R n a
    let c := branchHistoryCursor latticeDirectionHead x k n a
    have hrS : r ∈ S := branchHistoryRoots_initial_subset latticeDirectionHead x R n a hr
    have hhit : ∃ j, (wordState latticeDirectionHead (x n) c (rows n) j).1 ∈ S := by
      obtain ⟨j, hj⟩ := hh n (x n)
      exact ⟨j, (wordState_lattice_position (x n) c (rows n) j).trans hj ▸ hrS⟩
    obtain ⟨M, hM⟩ := exists_boundedWordHit_lt latticeDirectionHead S (x n) c (rows n) hhit
    let K := max N M
    have hNK : N ≤ K := le_max_left _ _
    have hMK : M ≤ K := le_max_right _ _
    have hpast (i : ℕ) (hi : i < n) :
        (rowBranchHistory latticeDirectionHead x R k K rows (i + 1)).2.1 < K := by
      have hsmall : ∀ j < i + 1,
          (rowBranchHistory latticeDirectionHead x R k N rows (j + 1)).2.1 < N :=
        fun j hj => hN j (lt_of_lt_of_le hj (Nat.succ_le_of_lt hi))
      rw [rowBranchHistory_eq_of_hits latticeDirectionHead x R k N K (i + 1) rows hNK hsmall]
      exact lt_of_lt_of_le (hN i hi) hNK
    have ha : rowBranchHistory latticeDirectionHead x R k K rows n = a :=
      rowBranchHistory_eq_of_hits latticeDirectionHead x R k N K n rows hNK hN
    have hlast : (rowBranchHistory latticeDirectionHead x R k K rows (n + 1)).2.1 < K := by
      change boundedWordHit latticeDirectionHead
        (branchHistoryRoots latticeDirectionHead x R n
          (rowBranchHistory latticeDirectionHead x R k K rows n)) (x n)
        (branchHistoryCursor latticeDirectionHead x k n
          (rowBranchHistory latticeDirectionHead x R k K rows n)) K (rows n) < K
      rw [ha]
      change boundedWordHit latticeDirectionHead S (x n) c K (rows n) < K
      rw [boundedWordHit_eq_of_hit latticeDirectionHead S (x n) c M K (rows n) hMK hM]
      exact lt_of_lt_of_le hM hMK
    refine ⟨K, ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hpast i hi
    · exact hlast

/-- By planar recurrence every finite lattice branch history has a finite
common horizon almost surely. -/
theorem wilsonRows_lattice_ae_finite_branch_horizon (R : RootPair)
    (x : ℕ → Site 2) (k : Cursor (Site 2)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ N, ∀ i < n,
      (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) k N rows (i + 1)).2.1 < N := by
  obtain ⟨r, hr⟩ := R.zero_nonempty
  have hhit (y : Site 2) : ∀ᵐ w ∂walkLaw, ∃ j, position y w j = r := by
    have hm : MeasurableSet {w : WalkDriver | ∃ j, position y w j = r} := by
      have he : {w : WalkDriver | ∃ j, position y w j = r} =
          ⋃ j : ℕ, {w | position y w j = r} := by ext w; simp
      rw [he]
      exact MeasurableSet.iUnion fun j =>
        (isClosed_eq (continuous_position y j) continuous_const).measurableSet
    exact (mem_ae_iff_prob_eq_one hm).mpr
      (FiniteAvalanches.ProvedStandards.polya_square_lattice_hits_every_site y r)
  have hall : ∀ᵐ rows ∂wilsonRows, ∀ i (y : Site 2), ∃ j, position y (rows i) j = r := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro y
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => walkLaw) i).quasiMeasurePreserving.ae
      (hhit y)
  filter_upwards [hall] with rows hrows
  exact exists_lattice_row_horizon_of_hits x (R.zero ∪ R.one) k rows r (Or.inl hr) hrows n

/-- Every fixed lattice site belongs to all sufficiently large wired boxes. -/
theorem eventually_finiteWired_inBox (z : Site 2) :
    ∀ᶠ B : ℕ in atTop, FiniteWired.inBox B z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|z 0| + |z 1| : ℤ)
  refine eventually_atTop.2 ⟨N, fun B hB => ?_⟩
  have hcast : (N : ℤ) ≤ B := Int.ofNat_le.mpr hB
  have h0 := abs_nonneg (z 0)
  have h1 := abs_nonneg (z 1)
  have hp0 := le_abs_self (z 0)
  have hp1 := le_abs_self (z 1)
  have hn0 := neg_abs_le (z 0)
  have hn1 := neg_abs_le (z 1)
  intro i
  fin_cases i
  · change -(B : ℤ) ≤ z 0 ∧ z 0 ≤ B
    constructor <;> omega
  · change -(B : ℤ) ≤ z 1 ∧ z 1 ≤ B
    constructor <;> omega

/-- A finite family of finite lattice walk segments is eventually contained in
all wired boxes. -/
theorem eventually_walkSegments_inBox (x : ℕ → Site 2) (rows : ℕ → WalkDriver)
    (n N : ℕ) : ∀ᶠ B : ℕ in atTop, ∀ i < n, ∀ j < N,
      FiniteWired.inBox B (position (x i) (rows i) j) := by
  have he : ∀ᶠ B : ℕ in atTop, ∀ i : Fin n, ∀ j : Fin N,
      FiniteWired.inBox B (position (x i.val) (rows i.val) j.val) :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun j =>
      eventually_finiteWired_inBox (position (x i.val) (rows i.val) j.val)))
  filter_upwards [he] with B hB i hi j hj
  exact hB ⟨i, hi⟩ ⟨j, hj⟩

/-- The original roots agree with the wired roots at every active site. -/
theorem wiredRoots_wiredSite_iff (R : RootPair) (B : ℕ) (z : Site 2)
    (hz : FiniteWired.inBox B z) :
    wiredSite B z ∈ (wiredRoots R B).val ↔ z ∈ R.zero ∪ R.one := by
  rw [wiredSite, dif_pos hz]
  change (FiniteWired.site (FiniteWired.activeOfSite B z hz) ∈ R.zero ∨
    FiniteWired.site (FiniteWired.activeOfSite B z hz) ∈ R.one) ↔ z ∈ R.zero ∪ R.one
  rw [FiniteWired.site_activeOfSite]
  rfl

/-- Almost surely, one finite horizon captures a finite lattice exploration,
and every sufficiently large wired box produces exactly the same branch words. -/
theorem wilsonRows_ae_eventually_wiredBranchHistory_eq (R : RootPair)
    (x : ℕ → Site 2) (ka : Cursor (Site 2))
    (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ N,
      (∀ i < n, (rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows (i + 1)).2.1 < N) ∧
      ∀ᶠ B : ℕ in atTop,
        rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredRoots R B).val
            (kb B) N rows n =
          rowBranchHistory latticeDirectionHead x (R.zero ∪ R.one) ka N rows n := by
  filter_upwards [wilsonRows_lattice_ae_finite_branch_horizon R x ka n] with rows hrows
  obtain ⟨N, hN⟩ := hrows
  refine ⟨N, hN, ?_⟩
  filter_upwards [eventually_walkSegments_inBox x rows n N] with B hbox
  apply (rowBranchHistory_wired_eq_of_confined B N x (wiredRoots R B).val
    (R.zero ∪ R.one) (kb B) ka rows n (wiredRoots_wiredSite_iff R B) hN ?_).1
  intro i hi j hj
  exact hbox i hi j (lt_of_le_of_lt hj (hN i hi))

end
end FiniteAvalanches.Wilson.Lattice
