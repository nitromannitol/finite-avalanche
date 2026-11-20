import FiniteAvalanches.Wilson.Lattice.RowRootLocality

/-! Distant-root wired forests converge on finite edge observations. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Inside the box, the distant root pair has the origin as its only root. -/
theorem distantOriginRootPair_mem_iff (B : ℕ) (z : Site 2)
    (hz : FiniteWired.inBox B z) :
    z ∈ (distantOriginRootPair B).zero ∪ (distantOriginRootPair B).one ↔ z ∈ ({0} : Set (Site 2)) := by
  have hne : z ≠ distantOriginRoot B := by
    intro h
    exact distantOriginRoot_not_inBox B (h ▸ hz)
  change (z = 0 ∨ z = distantOriginRoot B) ↔ z = 0
  simp only [hne, or_false]

/-- The moving-root lattice exploration eventually stops within the box,
with a common finite horizon, almost surely. -/
theorem wilsonRows_ae_eventually_distantOrigin_confined (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (n : ℕ) :
    ∀ᵐ rows ∂wilsonRows, ∃ N, ∀ᶠ B : ℕ in atTop,
      (∀ i < n,
        (rowBranchHistory latticeDirectionHead x
          ((distantOriginRootPair B).zero ∪ (distantOriginRootPair B).one)
          ka N rows (i + 1)).2.1 < N) ∧
      ∀ i < n, ∀ j ≤
        (rowBranchHistory latticeDirectionHead x
          ((distantOriginRootPair B).zero ∪ (distantOriginRootPair B).one)
          ka N rows (i + 1)).2.1,
        FiniteWired.inBox B (position (x i) (rows i) j) := by
  filter_upwards [wilsonRows_origin_ae_finite_branch_horizon x ka n] with rows hrows
  obtain ⟨N, hN⟩ := hrows
  refine ⟨N, ?_⟩
  filter_upwards [eventually_walkSegments_inBox x rows n N] with B hbox
  have hb : ∀ i < n, ∀ j ≤
      (rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1)).2.1,
      FiniteWired.inBox B (position (x i) (rows i) j) := by
    intro i hi j hj
    exact hbox i hi j (lt_of_le_of_lt hj (hN i hi))
  have he (i : ℕ) (hi : i < n) :
      rowBranchHistory latticeDirectionHead x
          ((distantOriginRootPair B).zero ∪ (distantOriginRootPair B).one)
          ka N rows (i + 1) =
        rowBranchHistory latticeDirectionHead x {0} ka N rows (i + 1) := by
    apply rowBranchHistory_eq_of_confined_roots B N x {0}
      ((distantOriginRootPair B).zero ∪ (distantOriginRootPair B).one) ka rows (i + 1)
      (distantOriginRootPair_mem_iff B)
    · intro j hj
      exact hN j (lt_of_lt_of_le hj (Nat.succ_le_of_lt hi))
    · intro j hj
      exact hb j (lt_of_lt_of_le hj (Nat.succ_le_of_lt hi))
  constructor
  · intro i hi
    rw [he i hi]
    exact hN i hi
  · intro i hi j hj
    rw [he i hi] at hj
    exact hb i hi j hj

/-- Under common rows, each finite distant-root wired observation eventually
matches the origin-rooted lattice observation. -/
theorem wilsonRows_ae_eventually_distantOrigin_wiredObservation_iff
    (x : ℕ → Site 2) (ka : Cursor (Site 2))
    (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) :
    ∀ᵐ rows ∂wilsonRows, ∀ᶠ B : ℕ in atTop,
      (rows ∈ wiredObservationRowEvent (distantOriginRootPair B) B x (kb B) n E ∅ p (fun _ => false) ↔
        rows ∈ originSamplerEvent ((List.range n).map x) E p) := by
  have hreal : ∀ᵐ rows ∂wilsonRows, ∀ B : ℕ,
      rows ∈ wiredRowRealizationEvent (distantOriginRootPair B) B
        (fun i => wiredSite B (x i)) (kb B) n := by
    apply ae_all_iff.mpr
    intro B
    exact wilsonRows_ae_wiredRowRealization (distantOriginRootPair B) B
      (fun i => wiredSite B (x i)) (kb B) n
  have hsuccess : ∀ᵐ rows ∂wilsonRows, ∀ B : ℕ, ∃ out,
      samplerRun (initialSampler (distantOriginRootPair B)) ((List.range n).map x) rows = some out := by
    apply ae_all_iff.mpr
    intro B
    exact samplerRun_ae_success (distantOriginRootPair B) _
  filter_upwards [wilsonRows_ae_eventually_distantOrigin_confined x ka n,
    wilsonRows_ae_eventually_distantOrigin_samplerEvent_iff ((List.range n).map x) E p,
    hreal, hsuccess] with rows hconf hsam hreal hsuccess
  obtain ⟨N, hN⟩ := hconf
  filter_upwards [hN, hsam] with B hB hsamB
  obtain ⟨out, hout⟩ := hsuccess B
  exact (wiredObservationRowEvent_iff_samplerEvent_of_confined (distantOriginRootPair B) B N x ka
    (kb B) rows n out hB.1 hB.2 hout (hreal B) E ∅ p (fun _ => false) hE
    (by simp)).trans hsamB

/-- Finite distant-root wired edge observations converge to the origin-rooted
lattice sampler's edge probabilities. -/
theorem distantOrigin_finiteForestLaw_edge_tendsto (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (E : Finset LatticeEdge) (p : LatticeEdge → Bool)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) :
    Tendsto (fun B => finiteForestLaw (distantOriginRootPair B) B
      (jointEvent E ∅ p (fun _ => false))) atTop
        (nhds (wilsonRows (originSamplerEvent ((List.range n).map x) E p))) := by
  have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_originSamplerEvent ((List.range n).map x) E p)
    (fun B => measurableSet_wiredObservationRowEvent (distantOriginRootPair B) B x (kb B) n
      E ∅ p (fun _ => false))
    (wilsonRows_ae_eventually_distantOrigin_wiredObservation_iff x ka kb n E p hE)
  have he : (fun B => wilsonRows (wiredObservationRowEvent (distantOriginRootPair B) B x
      (kb B) n E ∅ p (fun _ => false))) =
      fun B => finiteForestLaw (distantOriginRootPair B) B (jointEvent E ∅ p (fun _ => false)) := by
    funext B
    rw [finiteForestLaw_jointEvent]
    exact wilsonRows_wiredObservationRowEvent_eq (distantOriginRootPair B) B x (kb B) n
      E ∅ p (fun _ => false) hE (by simp)
  rwa [he] at ht

end
end FiniteAvalanches.Wilson.Lattice
