import FiniteAvalanches.Trees.Lattice.TightEvents
import FiniteAvalanches.Wilson.Lattice.WiredLimitOneEnd
import FiniteAvalanches.Trees.Lattice.InfiniteLaw

/-! Past events under the wired uniform spanning tree of `ℤ²`.

Almost surely the tree is one-ended with a connected dual. Hence the events that the
past of a nonempty finite set `B` is `S` in all large boxes are almost surely disjoint and
exhaust the space, so their probabilities sum to one; the local past events converge to
them; and the tightness events vanish in the limit. -/

set_option autoImplicit false

namespace FiniteAvalanches.Trees.Lattice

open LatticeProb MeasureTheory Filter Topology FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal

noncomputable section

/-- The past of `B` is `S` in all large boxes. -/
def pastLimitEvent (B S : Finset (Site 2)) : Set EdgeField :=
  {ω | ∀ᶠ m in atTop, ω ∈ pastEvent B S (boxFinset m)}

theorem measurableSet_pastLimitEvent (B S : Finset (Site 2)) :
    MeasurableSet (pastLimitEvent B S) := by
  have h : pastLimitEvent B S = ⋃ N : ℕ, ⋂ m : ℕ, ⋂ (_ : N ≤ m), pastEvent B S (boxFinset m) := by
    ext ω
    simp [pastLimitEvent, eventually_atTop]
  rw [h]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    (isClopen_pastEvent B S _).isClosed.measurableSet

/-- A box containing the lattice neighbours of `B`. -/
def nbrBox (B : Finset (Site 2)) : ℕ := (exists_subset_boxFinset (B.biUnion nbrFinset)).choose

theorem nbr_mem_nbrBox {B : Finset (Site 2)} {b w : Site 2} (hb : b ∈ B)
    (hbw : (lattice 2).Adj b w) : w ∈ boxFinset (nbrBox B) :=
  (exists_subset_boxFinset (B.biUnion nbrFinset)).choose_spec (Finset.mem_biUnion.mpr
    ⟨b, hb, (FiniteAvalanches.Sandpile.FiniteWired.mem_neighbors_iff b w).mpr hbw⟩)

theorem pastEvent_antitone (B S : Finset (Site 2)) :
    Antitone fun m => pastEvent B S (boxFinset (m + nbrBox B)) := by
  intro m m' hmm'
  exact pastEvent_anti (boxFinset_mono (by omega)) fun b hb w hw =>
    boxFinset_mono (by omega) (nbr_mem_nbrBox hb hw)

theorem pastLimitEvent_eq (B S : Finset (Site 2)) :
    pastLimitEvent B S = ⋂ m, pastEvent B S (boxFinset (m + nbrBox B)) := by
  ext ω
  simp only [pastLimitEvent, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro h m
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    have := hN (max m N + nbrBox B) (by omega)
    exact pastEvent_antitone B S (le_max_left m N) this
  · intro h
    filter_upwards [eventually_ge_atTop (nbrBox B)] with m hm
    have := h (m - nbrBox B)
    rwa [Nat.sub_add_cancel hm] at this

/-- The local past events converge to the limiting past event. -/
theorem tendsto_pastEvent (μ : Measure EdgeField) [IsFiniteMeasure μ] (B S : Finset (Site 2)) :
    Tendsto (fun m => μ (pastEvent B S (boxFinset m))) atTop (𝓝 (μ (pastLimitEvent B S))) := by
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun m => (isClopen_pastEvent B S (boxFinset (m + nbrBox B))).isClosed.measurableSet
      |>.nullMeasurableSet) (pastEvent_antitone B S) ⟨0, measure_ne_top _ _⟩
  rw [← pastLimitEvent_eq] at h
  have h' : Tendsto (fun m => μ (pastEvent B S (boxFinset (m + nbrBox B)))) atTop
      (𝓝 (μ (pastLimitEvent B S))) := h
  exact (tendsto_add_atTop_iff_nat (f := fun m => μ (pastEvent B S (boxFinset m)))
    (nbrBox B)).mp h'

/-- The wired uniform spanning tree of `ℤ²` as a measure. -/
abbrev ustMeasure : Measure EdgeField := (squareLatticeUST : Measure EdgeField)

theorem ae_one_ended :
    ∀ᵐ ω ∂ustMeasure, IsTree ω ∧ (∀ K : Finset (Site 2),
      ∃! C : (toGraph ω).ComponentCompl (K : Set (Site 2)), C.supp.Infinite) ∧
      (toGraph (dualField ω)).Connected := by
  filter_upwards [wiredLimit_ae_tree_and_existsUnique_infinite_componentCompl squareLatticeUST
    squareLatticeUST_tendsto, wiredLimit_ae_tree_and_dual_tree squareLatticeUST
      squareLatticeUST_tendsto] with ω h1 h2
  exact ⟨h1.1, h1.2, h2.2.connected⟩

/-- The limiting past events of a nonempty `B` have probabilities summing to one. -/
theorem hasSum_pastLimitEvent {B : Finset (Site 2)} (hB : B.Nonempty) :
    HasSum (fun S : Finset (Site 2) => ustMeasure (pastLimitEvent B S)) 1 := by
  have hgood : ∀ᵐ ω ∂ustMeasure, ∃ S : Finset (Site 2), ω ∈ pastLimitEvent B S ∧
      ∀ S' : Finset (Site 2), ω ∈ pastLimitEvent B S' → S' = S := by
    filter_upwards [ae_one_ended] with ω ⟨hT, hU, _⟩
    obtain hfin := pastSet_finite ω hT hU B
    refine ⟨hfin.toFinset, ?_, fun S' hS' => ?_⟩
    · exact (eventually_pastEvent_iff ω hT hU hB _).mpr (by simp)
    · have h := (eventually_pastEvent_iff ω hT hU hB S').mp hS'
      ext x
      rw [← Finset.mem_coe, h, Set.Finite.mem_toFinset]
  have hdisj : Pairwise (Function.onFun (AEDisjoint ustMeasure) fun S : Finset (Site 2) =>
      pastLimitEvent B S) := by
    intro S S' hne
    apply measure_mono_null (t := {ω | ¬∃ S : Finset (Site 2), ω ∈ pastLimitEvent B S ∧
      ∀ S' : Finset (Site 2), ω ∈ pastLimitEvent B S' → S' = S})
    · rintro ω ⟨h1, h2⟩ ⟨S0, -, hu⟩
      exact hne ((hu S h1).trans (hu S' h2).symm)
    · exact ae_iff.mp hgood
  have hunion : ustMeasure (⋃ S : Finset (Site 2), pastLimitEvent B S) = 1 := by
    rw [← measure_univ (μ := ustMeasure)]
    apply measure_congr
    rw [ae_eq_univ]
    apply measure_mono_null (t := {ω | ¬∃ S : Finset (Site 2), ω ∈ pastLimitEvent B S ∧
      ∀ S' : Finset (Site 2), ω ∈ pastLimitEvent B S' → S' = S})
    · intro ω hω hgoodω
      obtain ⟨S, hS, -⟩ := hgoodω
      exact hω (Set.mem_iUnion.mpr ⟨S, hS⟩)
    · exact ae_iff.mp hgood
  rw [measure_iUnion₀ hdisj fun S => (measurableSet_pastLimitEvent B S).nullMeasurableSet]
    at hunion
  rw [← hunion]
  exact ENNReal.summable.hasSum

/-- The tightness events at a site vanish under the wired uniform spanning tree. -/
theorem tendsto_tightEvent (b : Site 2) :
    Tendsto (fun k => ustMeasure (tightEvent b (boxFinset k))) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := ustMeasure)
    (fun k => (isClopen_tightEvent b (boxFinset k)).isClosed.measurableSet.nullMeasurableSet)
    (fun k k' hkk' => tightEvent_anti b (boxFinset_mono hkk')) ⟨0, measure_ne_top _ _⟩
  have hnull : ustMeasure (⋂ k, tightEvent b (boxFinset k)) = 0 := by
    apply measure_mono_null (t := {ω | ¬(toGraph (dualField ω)).Connected})
    · intro ω hω hconn
      obtain ⟨k, hk⟩ := (eventually_not_mem_tightEvent ω hconn b).exists
      exact hk (Set.mem_iInter.mp hω k)
    · apply ae_iff.mp
      filter_upwards [ae_one_ended] with ω h
      exact h.2.2
  rw [hnull] at h
  exact h

end

end FiniteAvalanches.Trees.Lattice
