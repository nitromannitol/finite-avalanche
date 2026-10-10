import FiniteAvalanches.Wilson.Lattice.DistinctStartContainment
import FiniteAvalanches.Wilson.Lattice.StoppedHistoryLocalization

/-! Full stopped-history escape bounds count distinct queried starts. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.DistinctStartLocalization
open LatticeProb MeasureTheory FiniteAvalanches BeurlingConnected
open DistinctStartContainment StoppedHistoryLocalization
open scoped Classical ENNReal
noncomputable section

/-- One universal bound uses the number of distinct starts, preserving all
original row slots and all recorded terminal vertices. -/
theorem finite_stopped_history_distinct_bound : ∃ D : ℝ, 0 < D ∧
    ∀ K : Set (Site 2), ((lattice 2).induce K).Preconnected → (0 : Site 2) ∈ K →
    ∀ R : RootPair, K ⊆ R.zero →
    ∀ r h : ℕ, 4 * r + 4 ≤ h - 1 →
      (∃ z ∈ K, siteRadius 0 z = h - 1) →
    ∀ L : List (Site 2), (∀ x ∈ L, siteRadius 0 x ≤ r) →
      wilsonRows {ξ : ℕ → WalkDriver | ∃ out,
        samplerRun (initialSampler R) L ξ = some out ∧
        ∃ p ∈ out.history, ∃ j : Fin (p.length + 1), h < siteRadius 0 (p.vertex j)} ≤
        ENNReal.ofReal ((L.toFinset.card : ℝ) * D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) := by
  obtain ⟨D, hD, hbound⟩ := full_stopped_localization_bound
  refine ⟨D, hD, ?_⟩
  intro K hK h0 R hKR r h hscale hboundary L hL
  let E : {x // x ∈ L.toFinset} → Set (ℕ → WalkDriver) := fun x =>
    {ξ | ∃ t : ℕ,
      h < siteRadius 0 (position x.val (ξ (L.idxOf x.val)) t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position x.val (ξ (L.idxOf x.val)))}
  have hrow (x : {x // x ∈ L.toFinset}) : wilsonRows (E x) ≤
      ENNReal.ofReal (D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) := by
    have he : E x = (fun ξ : ℕ → WalkDriver => ξ (L.idxOf x.val)) ⁻¹'
        {w : WalkDriver | ∃ t : ℕ,
          h < siteRadius 0 (position x.val w t) ∧
          (t : WithTop ℕ) ≤ firstHit K (position x.val w)} := rfl
    rw [he, ← Measure.map_apply (measurable_pi_apply (L.idxOf x.val))
      (measurableSet_full_stopped_exit K x.val h)]
    change (Measure.infinitePi (fun _ : ℕ => walkLaw)).map
      (fun ξ : ℕ → WalkDriver => ξ (L.idxOf x.val)) _ ≤ _
    rw [Measure.infinitePi_map_eval]
    exact hbound K hK h0 K Set.Subset.rfl r h hscale hboundary x.val
      (hL x.val (List.mem_toFinset.mp x.property))
  calc
    _ ≤ wilsonRows (⋃ x, E x) :=
      measure_mono (actual_history_exit_subset_distinct K R L h hKR)
    _ ≤ ∑ x : {x // x ∈ L.toFinset}, wilsonRows (E x) :=
      measure_iUnion_fintype_le wilsonRows E
    _ ≤ ∑ _x : {x // x ∈ L.toFinset}, ENNReal.ofReal
        (D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) :=
      Finset.sum_le_sum (fun x _ => hrow x)
    _ = ENNReal.ofReal ((L.toFinset.card : ℝ) * D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end
end FiniteAvalanches.Wilson.Lattice.DistinctStartLocalization
