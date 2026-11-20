import FiniteAvalanches.Wilson.Lattice.WiredActiveStackLaw
import FiniteAvalanches.Wilson.Lattice.LatticeBranchHorizon

/-! Recurrent lattice exploration rooted at the origin and wired-box coupling. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The origin-rooted lattice exploration has a finite common branch horizon
for every finite query sequence, almost surely. -/
theorem wilsonRows_origin_ae_finite_branch_horizon (x : ℕ → Site 2)
    (k : Cursor (Site 2)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ N, ∀ i < n,
      (rowBranchHistory latticeDirectionHead x {0} k N rows (i + 1)).2.1 < N := by
  have hhit (y : Site 2) : ∀ᵐ w ∂walkLaw, ∃ j, position y w j = 0 := by
    have hm : MeasurableSet {w : WalkDriver | ∃ j, position y w j = 0} := by
      have he : {w : WalkDriver | ∃ j, position y w j = 0} =
          ⋃ j : ℕ, {w | position y w j = 0} := by ext w; simp
      rw [he]
      exact MeasurableSet.iUnion fun j =>
        (isClosed_eq (continuous_position y j) continuous_const).measurableSet
    exact (mem_ae_iff_prob_eq_one hm).mpr
      (FiniteAvalanches.ProvedStandards.polya_square_lattice_hits_every_site y 0)
  have hall : ∀ᵐ rows ∂wilsonRows, ∀ i (y : Site 2), ∃ j, position y (rows i) j = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro y
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => walkLaw) i).quasiMeasurePreserving.ae
      (hhit y)
  filter_upwards [hall] with rows hrows
  exact exists_lattice_row_horizon_of_hits x {0} k rows 0 (Set.mem_singleton 0) hrows n

/-- The origin and the wired sink are the two stopping vertices used when
comparing a confined finite exploration to its lattice counterpart. -/
def wiredOriginAndSink (B : ℕ) : Set (FiniteWired.Vertex B) :=
  {none, some (wiredOrigin B)}

/-- The zero site is represented by the designated wired active origin. -/
theorem wiredSite_zero (B : ℕ) : wiredSite B 0 = some (wiredOrigin B) := by
  have hz : FiniteWired.inBox B 0 := by
    intro i
    simp only [Pi.zero_apply]
    constructor <;> omega
  rw [wiredSite, dif_pos hz]
  congr 1

/-- An in-box site belongs to the origin-and-sink set precisely at the origin. -/
theorem wiredOriginAndSink_wiredSite_iff (B : ℕ) (z : Site 2)
    (hz : FiniteWired.inBox B z) :
    wiredSite B z ∈ wiredOriginAndSink B ↔ z ∈ ({0} : Set (Site 2)) := by
  have hz' : wiredSite B z ≠ none := by simp [wiredSite, hz]
  simp only [wiredOriginAndSink, Set.mem_insert_iff, Set.mem_singleton_iff, hz', false_or]
  rw [← wiredSite_zero B]
  constructor
  · intro h
    have h' := congrArg (wiredVertexSite B) h
    rw [wiredVertexSite_wiredSite B z hz] at h'
    have h0 : FiniteWired.inBox B 0 := by
      intro i
      simp only [Pi.zero_apply]
      constructor <;> omega
    rw [wiredVertexSite_wiredSite B 0 h0] at h'
    exact h'
  · rintro rfl
    rfl

/-- Every fixed finite origin-rooted lattice exploration agrees eventually
with its origin-and-sink stopped wired-box exploration. -/
theorem wilsonRows_ae_eventually_originWiredBranchHistory_eq
    (x : ℕ → Site 2) (ka : Cursor (Site 2))
    (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ N,
      (∀ i < n, (rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1)).2.1 < N) ∧
      ∀ᶠ B : ℕ in atTop,
        rowBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
            (kb B) N rows n =
          rowBranchHistory latticeDirectionHead x {0} ka N rows n := by
  filter_upwards [wilsonRows_origin_ae_finite_branch_horizon x ka n] with rows hrows
  obtain ⟨N, hN⟩ := hrows
  refine ⟨N, hN, ?_⟩
  filter_upwards [eventually_walkSegments_inBox x rows n N] with B hbox
  apply (rowBranchHistory_wired_eq_of_confined B N x (wiredOriginAndSink B) {0}
    (kb B) ka rows n (wiredOriginAndSink_wiredSite_iff B) hN ?_).1
  intro i hi j hj
  exact hbox i hi j (lt_of_le_of_lt hj (hN i hi))

end
end FiniteAvalanches.Wilson.Lattice
