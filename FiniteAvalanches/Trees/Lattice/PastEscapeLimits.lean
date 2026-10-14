import FiniteAvalanches.Trees.Lattice.PastCylinderLimit
import FiniteAvalanches.Paper.Revision4498.FiniteApplications

/-! The current finite-past cylinder limit applied to the complementary escape event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Paper.CurrentRadiusReduction

open LatticeProb FiniteAvalanches Sandpile MeasureTheory Filter Trees.Lattice
open Trees.Lattice.CurrentPastCylinder
open scoped Classical ENNReal
noncomputable section

/-- The actual infinite past event is null measurable by its current raw cylinder dictionary. -/
theorem infinitePastEvent_nullMeasurable (x : Site 2) (W : Finset (Site 2)) :
    NullMeasurableSet (infinitePastEvent x W) (squareLatticeUST : Measure EdgeField) := by
  apply (measurable_rawPastEvent x W).nullMeasurableSet.congr
  filter_upwards [infinitePastEvent_ae_raw x W] with ω hω
  exact propext hω.symm

/-- The complementary probabilities converge under the same full volume clock. -/
theorem finite_past_escape_real_tendsto (x : Site 2) (W : Finset (Site 2)) :
    Tendsto (fun N : ℕ => (WiredTrees.law N).real (finitePastEvent x W N)ᶜ) atTop
      (nhds ((squareLatticeUST : Measure EdgeField).real (infinitePastEvent x W)ᶜ)) := by
  rw [probReal_compl_eq_one_sub₀ (infinitePastEvent_nullMeasurable x W)]
  have hgood := (ENNReal.tendsto_toReal
    (measure_ne_top (squareLatticeUST : Measure EdgeField) (infinitePastEvent x W))).comp
      (past_probability_tendsto x W)
  apply ((tendsto_const_nhds (x := (1 : ℝ))).sub hgood).congr
  intro N
  exact (probReal_compl_eq_one_sub
    (finitePastEvent x W N).toFinite.measurableSet).symm

/-- On the actual full-measure tree/end carrier, complementing containment gives
the true past escape event, with the same outgoing past and original window. -/
theorem infinite_past_compl_real_eq_escape (x : Site 2) (W : Finset (Site 2)) :
    (squareLatticeUST : Measure EdgeField).real (infinitePastEvent x W)ᶜ =
      (squareLatticeUST : Measure EdgeField).real
        {ω | ∃ hT : IsTree ω, ∃ hE : OneEnded ω,
          ¬vertexPast ω hT hE x ⊆ (W : Set (Site 2))} := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [squareLatticeUST_ae_tree_oneEnded] with ω hω
  apply propext
  constructor
  · intro h
    exact ⟨hω.1, hω.2, fun hp => h ⟨hω.1, hω.2, hp⟩⟩
  · rintro ⟨hT, hE, hp⟩ ⟨hT', hE', hgood⟩
    exact hp hgood

/-- The same universal true-past tail constant bounds the limiting complements. -/
theorem exists_infinite_past_compl_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r M : ℕ, r + 2 ≤ M → ∀ x : Site 2,
      x ∈ boxSites r →
      (squareLatticeUST : Measure EdgeField).real (infinitePastEvent x (boxSites M))ᶜ ≤
        C * ((M : ℝ) - (r : ℝ)) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ := Revised.past_outside_origin_box_bound
  refine ⟨C, hC, ?_⟩
  intro r M hM x hx
  rw [infinite_past_compl_real_eq_escape]
  exact htail r M hM x hx

end
end FiniteAvalanches.Paper.CurrentRadiusReduction
