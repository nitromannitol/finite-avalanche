import FiniteAvalanches.Wilson.Lattice.WiredDualFaceBoundaryHistoryEvent
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceHistoryRelabel
import FiniteAvalanches.Wilson.Lattice.FreeBoundaryRowLimit

/-! Boundary-rooted face-square row observations converge to the origin sampler. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The completed row-history event for a face-square edge observation. -/
def wiredDualFaceBoundaryRowEdgeEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) : Set (ℕ → WalkDriver) :=
  {rows | ∃ N, BranchHistory.HitsBefore N n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
        (wiredDualFaceOriginAndBoundary B) k N rows n) ∧
    ∀ e ∈ E, wiredDualFaceHistoryEdgeField B
      (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
        (wiredDualFaceOriginAndBoundary B) k N rows n) e = p e}

/-- Completed face-square row edge events are measurable. -/
theorem measurableSet_wiredDualFaceBoundaryRowEdgeEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    MeasurableSet (wiredDualFaceBoundaryRowEdgeEvent B x k n E p) := by
  let y := fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))
  have he : wiredDualFaceBoundaryRowEdgeEvent B x k n E p = ⋃ N : ℕ,
      {rows | BranchHistory.HitsBefore N n
          (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
            (wiredDualFaceOriginAndBoundary B) k N rows n) ∧
        ∀ e ∈ E, wiredDualFaceHistoryEdgeField B y n
          (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
            (wiredDualFaceOriginAndBoundary B) k N rows n) e = p e} := by
    ext rows
    simp only [wiredDualFaceBoundaryRowEdgeEvent, Set.mem_setOf_eq, Set.mem_iUnion, y]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun rows => rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
      (wiredDualFaceOriginAndBoundary B) k N rows n)
    (fun a => measurableSet_rowBranchHistory_eq (wiredDualFaceDirectionHead (B + 1)) y
      (wiredDualFaceOriginAndBoundary B) k N n
      (fun i (rows : ℕ → WalkDriver) => rows i) (fun i => measurable_pi_apply i) a)
    (fun h => BranchHistory.HitsBefore N n h ∧ ∀ e ∈ E, wiredDualFaceHistoryEdgeField B y n h e = p e)

/-- Common rows eventually give the same boundary-face and origin-sampler edge event. -/
theorem wilsonRows_ae_eventually_wiredDualFaceBoundaryRowEdgeEvent_iff (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1))) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop,
      (rows ∈ wiredDualFaceBoundaryRowEdgeEvent B x (kc B) n E p ↔
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
  filter_upwards [heq, eventually_walkSegments_inBox x rows n T] with B heq' hbox
  let bx := fun i => freeSite (B + 1) (x i)
  let fx := fun i => wiredDualFaceInnerVertex (B + 1) (bx i)
  let S := freeOriginAndBoundary B
  let R := wiredDualFaceOriginAndBoundary B
  have hprefix : ∀ m ≤ n, rowBranchHistory (freeDirectionHead (B + 1)) bx S (kb B) T rows m =
      rowBranchHistory latticeDirectionHead x {0} ka T rows m :=
    rowBranchHistory_prefix_eq _ _ _ _ _ _ _ _ _ _ _ heq'
  have hfhit : ∀ i < n,
      (rowBranchHistory (freeDirectionHead (B + 1)) bx S (kb B) T rows (i + 1)).2.1 < T := by
    intro i hi
    rw [hprefix (i + 1) (by omega)]
    exact hT i hi
  have hfconf : ∀ i < n, ∀ j <
      (rowBranchHistory (freeDirectionHead (B + 1)) bx S (kb B) T rows (i + 1)).2.1,
      FiniteWired.inBox B (FiniteWired.site (wordState (freeDirectionHead (B + 1)) (bx i)
        (branchHistoryCursor (freeDirectionHead (B + 1)) bx (kb B) i
          (rowBranchHistory (freeDirectionHead (B + 1)) bx S (kb B) T rows i)) (rows i) j).1) := by
    intro i hi j hj
    have hjT : j < T := lt_trans hj (hfhit i hi)
    have hbox' : ∀ s ≤ j, FiniteWired.inBox (B + 1) (position (x i) (rows i) s) := by
      intro s hs d
      have hh := hbox i hi s (lt_of_le_of_lt hs hjT) d
      constructor <;> omega
    rw [freeWordState_eq_of_confined (B + 1) (x i) (rows i) _ j hbox' j le_rfl,
      site_freeSite_of_inBox _ _ (hbox' j le_rfl)]
    exact hbox i hi j hjT
  have hface := rowBranchHistory_wiredDualFace_eq_of_confined B T bx S R (kb B) (kc B) rows n
    (wiredDualFaceOriginAndBoundary_inner_iff B) hfhit hfconf
  have hconf : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x {0} ka T rows (i + 1)).2.1,
      FiniteWired.inBox (B + 1) (position (x i) (rows i) j) := by
    intro i hi j hj d
    have hh := hbox i hi j (lt_of_le_of_lt hj (hT i hi)) d
    constructor <;> omega
  have hfreeMap := rowBranchHistory_free_edges_map_of_confined (B + 1) T x {0} ka (kb B) rows n hconf
  have hfaceMap := rowBranchHistory_wiredDualFace_edges_map_of_confined B T bx S (kb B) (kc B) rows n hfconf
  have hmap : (branchHistoryEdgeSet (wiredDualFaceDirectionHead (B + 1)) fx n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) fx R (kc B) T rows n)).image
        (Sym2.map wiredDualFaceSite) =
      branchHistoryEdgeSet latticeDirectionHead x n (rowBranchHistory latticeDirectionHead x {0} ka T rows n) := by
    rw [hface.1, ← hfaceMap, Finset.image_image]
    have hfun : (Sym2.map wiredDualFaceSite ∘ Sym2.map (wiredDualFaceInnerVertex (B + 1))) =
        Sym2.map (FiniteWired.site : FiniteWired.Active (B + 1) → Site 2) := by
      funext e
      induction e using Sym2.inductionOn with
      | _ v w =>
        simp only [Function.comp_apply, Sym2.map_mk, wiredDualFaceSite_innerVertex]
    rw [hfun, heq']
    exact hfreeMap
  have hfaceHit : BranchHistory.HitsBefore T n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) fx R (kc B) T rows n) := by
    rw [hface.1, heq']
    exact (rowBranchHistory_hitsBefore_iff latticeDirectionHead x {0} ka T n rows).mpr hT
  have hfield (e : LatticeEdge) : wiredDualFaceHistoryEdgeField B fx n
      (rowBranchHistory (wiredDualFaceDirectionHead (B + 1)) fx R (kc B) T rows n) e =
        decide (e.val ∈ out.edges) := by
    unfold wiredDualFaceHistoryEdgeField
    rw [hmap, ← hsam']
  constructor
  · rintro ⟨N, hN, hpat⟩
    have hh := (rowBranchHistory_hitsBefore_iff (wiredDualFaceDirectionHead (B + 1)) fx R (kc B) N n rows).mp hN
    have ht := (rowBranchHistory_hitsBefore_iff (wiredDualFaceDirectionHead (B + 1)) fx R (kc B) T n rows).mp hfaceHit
    have he := rowBranchHistory_eq_of_two_hits (wiredDualFaceDirectionHead (B + 1)) fx R (kc B) N T n rows hh ht
    rw [he] at hpat
    refine ⟨out, hout, ?_⟩
    intro e heE
    rw [← hfield e]
    exact hpat e heE
  · rintro ⟨out', hout', hpat⟩
    have heqout : out' = out := Option.some.inj (hout'.symm.trans hout)
    refine ⟨T, hfaceHit, ?_⟩
    intro e heE
    rw [hfield e, ← heqout]
    exact hpat e heE

/-- Boundary face row edge observations converge to origin-sampler probabilities. -/
theorem wiredDualFaceBoundaryRowEdgeEvent_tendsto (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1))) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    Tendsto (fun B => wilsonRows (wiredDualFaceBoundaryRowEdgeEvent B x (kc B) n E p)) atTop
      (nhds (wilsonRows (originSamplerEvent ((List.range n).map x) E p))) :=
  tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_originSamplerEvent ((List.range n).map x) E p)
    (fun B => measurableSet_wiredDualFaceBoundaryRowEdgeEvent B x (kc B) n E p)
    (wilsonRows_ae_eventually_wiredDualFaceBoundaryRowEdgeEvent_iff x ka kb kc n E p)

end
end FiniteAvalanches.Wilson.Lattice
