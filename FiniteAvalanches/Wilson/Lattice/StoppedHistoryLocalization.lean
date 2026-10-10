import FiniteAvalanches.Wilson.Lattice.StoppedHistoryContainment
import FiniteAvalanches.Wilson.Lattice.ConditionalHistory

set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.StoppedHistoryLocalization
open LatticeProb MeasureTheory FiniteAvalanches.BeurlingConnected
open scoped Classical ENNReal
noncomputable section

/-- The fixed-obstacle full stopped-row exit event is measurable, including its
last position and the possibility of an infinite avoiding driver. -/
theorem measurableSet_full_stopped_exit (K : Set (Site 2)) (x : Site 2) (h : ℕ) :
    MeasurableSet {w : WalkDriver | ∃ t : ℕ,
      h < FiniteAvalanches.siteRadius 0 (position x w t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position x w)} := by
  have he : {w : WalkDriver | ∃ t : ℕ,
      h < FiniteAvalanches.siteRadius 0 (position x w t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position x w)} =
      {w : WalkDriver | ∃ t : ℕ,
        h < FiniteAvalanches.siteRadius 0 (position x w t) ∧
        ∀ s < t, position x w s ∉ K} := by
    ext w
    simp only [Set.mem_setOf_eq, prefix_avoidance_iff]
  rw [he]
  have hout (t : ℕ) : MeasurableSet {w : WalkDriver |
      h < FiniteAvalanches.siteRadius 0 (position x w t)} :=
    (measurable_position x t)
      (Set.to_countable {z : Site 2 | h < FiniteAvalanches.siteRadius 0 z}).measurableSet
  have hav (s : ℕ) : MeasurableSet {w : WalkDriver | position x w s ∉ K} :=
    ((measurable_position x s) (Set.to_countable K).measurableSet).compl
  simp only [Set.setOf_exists, Set.setOf_and, Set.setOf_forall]
  exact MeasurableSet.iUnion (fun t => (hout t).inter
    (MeasurableSet.iInter (fun s => MeasurableSet.iInter (fun _ => hav s))))

/-- Literal completed stopped-history escape is observed by the actual full-history
sigma algebra and hence by the ambient iid-driver sigma algebra. -/
theorem measurableSet_actual_history_exit (R : RootPair) (L : List (Site 2)) (h : ℕ) :
    MeasurableSet {ξ : ℕ → WalkDriver | ∃ out,
      samplerRun (initialSampler R) L ξ = some out ∧
      ∃ p ∈ out.history, ∃ j : Fin (p.length + 1),
        h < FiniteAvalanches.siteRadius 0 (p.vertex j)} :=
  ConditionalIteration7.fullHistory_le R L _
    (ConditionalIteration7.measurable_completed_observation R L _)

/-- Finite Wilson localization for the complete actual stopped histories. One
universal constant precedes the obstacle, roots, scales and finite start list. -/
theorem finite_stopped_history_localization_bound : ∃ D : ℝ, 0 < D ∧
    ∀ K : Set (Site 2), ((lattice 2).induce K).Preconnected → (0 : Site 2) ∈ K →
    ∀ R : RootPair, K ⊆ R.zero →
    ∀ r h : ℕ, 4 * r + 4 ≤ h - 1 →
      (∃ z ∈ K, FiniteAvalanches.siteRadius 0 z = h - 1) →
    ∀ L : List (Site 2), (∀ x ∈ L, FiniteAvalanches.siteRadius 0 x ≤ r) →
      wilsonRows {ξ : ℕ → WalkDriver | ∃ out,
        samplerRun (initialSampler R) L ξ = some out ∧
        ∃ p ∈ out.history, ∃ j : Fin (p.length + 1),
          h < FiniteAvalanches.siteRadius 0 (p.vertex j)} ≤
        ENNReal.ofReal ((L.length : ℝ) * D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) := by
  obtain ⟨D, hD, hbound⟩ := full_stopped_localization_bound
  refine ⟨D, hD, ?_⟩
  intro K hK h0 R hKR r h hscale hboundary L hL
  let E : Fin L.length → Set (ℕ → WalkDriver) := fun i =>
    {ξ | ∃ t : ℕ,
      h < FiniteAvalanches.siteRadius 0 (position (L.get i) (ξ i.val) t) ∧
      (t : WithTop ℕ) ≤ firstHit K (position (L.get i) (ξ i.val))}
  have hrow (i : Fin L.length) : wilsonRows (E i) ≤
      ENNReal.ofReal (D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) := by
    have he : E i = (fun ξ : ℕ → WalkDriver => ξ i.val) ⁻¹'
        {w : WalkDriver | ∃ t : ℕ,
          h < FiniteAvalanches.siteRadius 0 (position (L.get i) w t) ∧
          (t : WithTop ℕ) ≤ firstHit K (position (L.get i) w)} := rfl
    rw [he, ← Measure.map_apply (measurable_pi_apply i.val)
      (measurableSet_full_stopped_exit K (L.get i) h)]
    change (Measure.infinitePi (fun _ : ℕ => walkLaw)).map
      (fun ξ : ℕ → WalkDriver => ξ i.val) _ ≤ _
    rw [Measure.infinitePi_map_eval]
    exact hbound K hK h0 K Set.Subset.rfl r h hscale hboundary (L.get i)
      (hL (L.get i) (List.get_mem L i))
  calc
    _ ≤ wilsonRows (⋃ i, E i) := measure_mono (actual_history_exit_subset K R L h hKR)
    _ ≤ ∑ i : Fin L.length, wilsonRows (E i) := measure_iUnion_fintype_le wilsonRows E
    _ ≤ ∑ _i : Fin L.length, ENNReal.ofReal
        (D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = ENNReal.ofReal ((L.length : ℝ) * D * Real.sqrt (((r + 1 : ℕ) : ℝ) / h)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end
end FiniteAvalanches.Wilson.Lattice.StoppedHistoryLocalization
