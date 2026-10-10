import FiniteAvalanches.Trees.Lattice.FiniteObservationContactLaw
import FiniteAvalanches.Wilson.Lattice.ContactWindow
import FiniteAvalanches.Wilson.Lattice.FixedBoxColorLaw

/-! The actual finite conditional contact law, with exact ENNReal event
probabilities. The fixed-box input is the separately checked Wilson dictionary. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile MeasureTheory
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- Ordinary finite-measure conversion of the checked fixed-box window law,
then the literal forest-field pushforward. -/
theorem fixed_box_contact_event_ennreal (R : RootPair) (N : ℕ)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (K : Finset (Site 2)) (D : Set ℕ) :
    finiteUniformLaw R N {F | contacts K (finiteForestField R N F).2 ∈ D} =
      wilsonColorLaw R {σ | contacts K σ ∈ D} := by
  have hreal := WiredBoxCopies.fixed_box_window_real R N houtside
    (contactSites K) (contactWindowEvent K D)
  have he : finiteForestLaw R N (Prod.snd ⁻¹'
      windowColorEvent (contactSites K) (contactWindowEvent K D)) =
      wilsonColorLaw R (windowColorEvent (contactSites K) (contactWindowEvent K D)) :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal
  rw [contactWindowEvent_eq] at he
  have hm : MeasurableSet (Prod.snd ⁻¹' {σ : ColorField | contacts K σ ∈ D} : Set ForestField) :=
    (measurableSet_contact_count_event K D).preimage measurable_snd
  rw [finiteForestLaw, Measure.map_apply (finiteForestField_measurable R N) hm] at he
  exact he

/-- The ENNReal law retains the complete original-copy forest denominator,
including forests having the same colors but different copy subsets. -/
theorem fixed_box_contact_count_ennreal (R : RootPair) (N : ℕ)
    (houtside : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.one)
    (K : Finset (Site 2)) (D : Set ℕ) :
    wilsonColorLaw R {σ | contacts K σ ∈ D} =
      (Nat.card {F : FiniteForest R N | contacts K (finiteForestField R N F).2 ∈ D} : ℝ≥0∞) /
        finiteForestCount R N := by
  exact (fixed_box_contact_event_ennreal R N houtside K D).symm.trans
    (FiniteAvalanches.uniformMeasure_apply (FiniteForest R N) _)

/-- The whole copied K and ordered complete ancestor-to-sink path condition the
actual finite UST count to the lattice Wilson contact law. All exterior sites
are one roots and every ambient copy remains in the statistic. -/
theorem finite_whole_observation_conditional_contact_law (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t₀ : (graph N).SpanningTree)
    (hne₀ : (graph N).ancestorOf t₀ none S hS ≠ none) (D : Set ℕ) :
    let G := graph N
    let Ksites := activeSites N (G.span t₀ S)
    let roots := observationRootPair N S hS t₀ hne₀
    ProbabilityTheory.cond (law N)
      {t | G.copiedConnectorObservation t₀ t none S hS}
      {t | ∃ hne : G.ancestorOf t none S hS ≠ none,
        (G.admissibleEdges (G.past t none (G.ancestorOf t none S hS) hne)
          (G.span t S)).card ∈ D} =
      wilsonColorLaw roots {σ | contacts Ksites σ ∈ D} := by
  exact (finite_whole_observation_contact_forest_law N S hS t₀ hne₀ D).trans
    (fixed_box_contact_event_ennreal _ N
      (fun x hx => observationRootPair_exterior_one N S hS t₀ hne₀ hx) _ D)

end
end FiniteAvalanches.ConditioningConsumer
