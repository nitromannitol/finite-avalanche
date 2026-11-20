import FiniteAvalanches.Wilson.Lattice.FreeBranchCoupling
import FiniteAvalanches.Wilson.Lattice.OriginRootCoupling
import FiniteAvalanches.Wilson.Lattice.RowRootLocality

/-! Origin-rooted free-box histories agree with lattice histories away from the boundary. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Sites on the outer layer of the next larger free box. -/
def freeOuterBoundary (N : ℕ) : Set (FiniteWired.Active (N + 1)) :=
  {x | ¬FiniteWired.inBox N (FiniteWired.site x)}

/-- The origin and outer boundary are roots for the stopped free exploration. -/
def freeOriginAndBoundary (N : ℕ) : Set (FiniteWired.Active (N + 1)) :=
  {x | FiniteWired.site x = 0} ∪ freeOuterBoundary N

/-- The corresponding origin and exterior roots on the full lattice. -/
def latticeOriginAndExterior (N : ℕ) : Set (Site 2) :=
  {z | z = 0} ∪ {z | ¬FiniteWired.inBox N z}

/-- Lattice and free-box roots agree at every site of the larger box. -/
theorem freeOriginAndBoundary_freeSite_iff (N : ℕ) (z : Site 2)
    (hz : FiniteWired.inBox (N + 1) z) :
    freeSite (N + 1) z ∈ freeOriginAndBoundary N ↔ z ∈ latticeOriginAndExterior N := by
  simp only [freeOriginAndBoundary, freeOuterBoundary, latticeOriginAndExterior,
    Set.mem_union, Set.mem_setOf_eq, site_freeSite_of_inBox (N + 1) z hz]

/-- The additional lattice exterior roots do not change the origin root inside the box. -/
theorem latticeOriginAndExterior_iff_of_inBox (N : ℕ) (z : Site 2)
    (hz : FiniteWired.inBox N z) : z ∈ latticeOriginAndExterior N ↔ z ∈ ({0} : Set (Site 2)) := by
  simp [latticeOriginAndExterior, hz]

/-- For a fixed finite query sequence, free origin-and-boundary row histories
and origin-only lattice histories eventually agree almost surely. -/
theorem wilsonRows_ae_eventually_freeOrigin_history_eq (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (N : ℕ) → Cursor (FiniteWired.Active (N + 1))) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ T,
      (∀ i < n, (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1 < T) ∧
      ∀ᶠ N : ℕ in atTop,
        rowBranchHistory (freeDirectionHead (N + 1)) (fun i => freeSite (N + 1) (x i))
          (freeOriginAndBoundary N) (kb N) T rows n =
          rowBranchHistory latticeDirectionHead x {0} ka T rows n := by
  filter_upwards [wilsonRows_origin_ae_finite_branch_horizon x ka n] with rows hrows
  obtain ⟨T, hT⟩ := hrows
  refine ⟨T, hT, ?_⟩
  filter_upwards [eventually_walkSegments_inBox x rows n T] with N hbox
  have hconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1,
      FiniteWired.inBox N (position (x i) (rows i) j) := by
    intro i hi j hj
    exact hbox i hi j (lt_of_le_of_lt hj (hT i hi))
  have hroot : ∀ z, FiniteWired.inBox N z →
      (z ∈ latticeOriginAndExterior N ↔ z ∈ ({0} : Set (Site 2))) :=
    latticeOriginAndExterior_iff_of_inBox N
  have heq (m : ℕ) (hm : m ≤ n) :
      rowBranchHistory latticeDirectionHead x (latticeOriginAndExterior N) ka T rows m =
        rowBranchHistory latticeDirectionHead x {0} ka T rows m :=
    rowBranchHistory_eq_of_confined_roots N T x {0} (latticeOriginAndExterior N) ka rows m hroot
      (fun i hi => hT i (lt_of_lt_of_le hi hm))
      (fun i hi => hconf i (lt_of_lt_of_le hi hm))
  have hhit' : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x (latticeOriginAndExterior N) ka T rows (i + 1)).2.1 < T := by
    intro i hi
    rw [heq (i + 1) (by omega)]
    exact hT i hi
  have hbox' : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x (latticeOriginAndExterior N) ka T rows (i + 1)).2.1,
      FiniteWired.inBox (N + 1) (position (x i) (rows i) j) := by
    intro i hi j hj
    rw [heq (i + 1) (by omega)] at hj
    have hjbox := hconf i hi j hj
    intro k
    have hcoord := hjbox k
    constructor <;> omega
  have hf := (rowBranchHistory_free_eq_of_confined (N + 1) T x
    (freeOriginAndBoundary N) (latticeOriginAndExterior N) (kb N) ka rows n
    (freeOriginAndBoundary_freeSite_iff N) hhit' hbox').1
  exact hf.trans (heq n le_rfl)

end
end FiniteAvalanches.Wilson.Lattice
