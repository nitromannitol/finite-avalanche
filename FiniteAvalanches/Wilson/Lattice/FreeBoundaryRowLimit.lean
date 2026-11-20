import FiniteAvalanches.Wilson.Lattice.FreeBoundaryHistoryEvent
import FiniteAvalanches.Wilson.Lattice.FreeHistoryRelabel
import FiniteAvalanches.Wilson.Lattice.OriginSamplerRootPath
import FiniteAvalanches.Wilson.Lattice.HistoryListEdges
import FiniteAvalanches.Wilson.Lattice.WiredRowRealization

/-! Boundary-rooted free row observations converge to the origin sampler. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The completed row-history event for a free-box edge observation. -/
def freeBoundaryRowEdgeEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) : Set (ℕ → WalkDriver) :=
  {rows | ∃ N, BranchHistory.HitsBefore N n
      (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
        (freeOriginAndBoundary B) k N rows n) ∧
    ∀ e ∈ E, freeHistoryEdgeField B (fun i => freeSite (B + 1) (x i)) n
      (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
        (freeOriginAndBoundary B) k N rows n) e = p e}

/-- Completed free row-history edge events are measurable. -/
theorem measurableSet_freeBoundaryRowEdgeEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    MeasurableSet (freeBoundaryRowEdgeEvent B x k n E p) := by
  have he : freeBoundaryRowEdgeEvent B x k n E p = ⋃ N : ℕ,
      {rows | BranchHistory.HitsBefore N n
          (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
            (freeOriginAndBoundary B) k N rows n) ∧
        ∀ e ∈ E, freeHistoryEdgeField B (fun i => freeSite (B + 1) (x i)) n
          (rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
            (freeOriginAndBoundary B) k N rows n) e = p e} := by
    ext rows
    simp only [freeBoundaryRowEdgeEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun rows => rowBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
      (freeOriginAndBoundary B) k N rows n)
    (fun a => measurableSet_rowBranchHistory_eq (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n
      (fun i (rows : ℕ → WalkDriver) => rows i) (fun i => measurable_pi_apply i) a)
    (fun h => BranchHistory.HitsBefore N n h ∧
      ∀ e ∈ E, freeHistoryEdgeField B (fun i => freeSite (B + 1) (x i)) n h e = p e)

/-- Common rows eventually give the same free boundary-history and origin-sampler edge event. -/
theorem wilsonRows_ae_eventually_freeBoundaryRowEdgeEvent_iff (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop,
      (rows ∈ freeBoundaryRowEdgeEvent B x (kb B) n E p ↔
        rows ∈ originSamplerEvent ((List.range n).map x) E p) := by
  filter_upwards [wilsonRows_ae_eventually_freeOrigin_history_eq x ka kb n,
    samplerRun_origin_ae_success ((List.range n).map x)] with rows hrows hsuccess
  obtain ⟨T, hT, heq⟩ := hrows
  obtain ⟨out, hout⟩ := hsuccess
  have hhit : ∀ i < n,
      (rowBranchHistory latticeDirectionHead x originInitialSampler.covered ka T rows (i + 1)).2.1 < T := by
    simpa only [originInitialSampler_covered] using hT
  have hsam := samplerRun_edges_eq_branchHistoryEdgeSet originInitialSampler x ka T n rows out hhit hout
  rw [originInitialSampler_covered] at hsam
  have hsam' : out.edges = branchHistoryEdgeSet latticeDirectionHead x n
      (rowBranchHistory latticeDirectionHead x {0} ka T rows n) := by
    simpa only [originInitialSampler, Finset.empty_union] using hsam
  filter_upwards [heq, eventually_walkSegments_inBox x rows n T] with B hEq hbox
  let bx := fun i => freeSite (B + 1) (x i)
  let roots := freeOriginAndBoundary B
  have hconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1,
      FiniteWired.inBox (B + 1) (position (x i) (rows i) j) := by
    intro i hi j hj d
    have hh := hbox i hi j (lt_of_le_of_lt hj (hT i hi)) d
    constructor <;> omega
  have hmap := rowBranchHistory_free_edges_map_of_confined (B + 1) T x {0} ka (kb B) rows n hconf
  have hfree : BranchHistory.HitsBefore T n (rowBranchHistory (freeDirectionHead (B + 1)) bx roots
      (kb B) T rows n) := by
    rw [hEq]
    exact (rowBranchHistory_hitsBefore_iff latticeDirectionHead x {0} ka T n rows).mpr hT
  have hfield (e : LatticeEdge) : freeHistoryEdgeField B bx n
      (rowBranchHistory (freeDirectionHead (B + 1)) bx roots (kb B) T rows n) e =
        decide (e.val ∈ out.edges) := by
    unfold freeHistoryEdgeField
    rw [hEq, hmap, ← hsam']
  constructor
  · rintro ⟨N, hN, hpat⟩
    have hh := (rowBranchHistory_hitsBefore_iff (freeDirectionHead (B + 1)) bx roots (kb B) N n rows).mp hN
    have ht := (rowBranchHistory_hitsBefore_iff (freeDirectionHead (B + 1)) bx roots (kb B) T n rows).mp hfree
    have he := rowBranchHistory_eq_of_two_hits (freeDirectionHead (B + 1)) bx roots (kb B) N T n rows hh ht
    rw [he] at hpat
    refine ⟨out, hout, ?_⟩
    intro e heE
    rw [← hfield e]
    exact hpat e heE
  · rintro ⟨out', hout', hpat⟩
    have heqout : out' = out := Option.some.inj (hout'.symm.trans hout)
    refine ⟨T, hfree, ?_⟩
    intro e heE
    rw [hfield e, ← heqout]
    exact hpat e heE

/-- Free boundary-rooted row edge observations converge to origin sampler probabilities. -/
theorem freeBoundaryRowEdgeEvent_tendsto (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    Tendsto (fun B => wilsonRows (freeBoundaryRowEdgeEvent B x (kb B) n E p)) atTop
      (nhds (wilsonRows (originSamplerEvent ((List.range n).map x) E p))) :=
  tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_originSamplerEvent ((List.range n).map x) E p)
    (fun B => measurableSet_freeBoundaryRowEdgeEvent B x (kb B) n E p)
    (wilsonRows_ae_eventually_freeBoundaryRowEdgeEvent_iff x ka kb n E p)

end
end FiniteAvalanches.Wilson.Lattice
