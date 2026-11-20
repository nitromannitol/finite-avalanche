import FiniteAvalanches.Wilson.Lattice.SiteRootBox
import FiniteAvalanches.Trees.Lattice.InfiniteLaw
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Wired uniform spanning forests along an arbitrary exhaustion of `ℤ²` converge weakly
to the wired uniform spanning tree `squareLatticeUST`.

For a finite set of edges, the probability that all of them are present is squeezed
between the corresponding probabilities for boxes inside and outside the volume, by the
monotonicity of `forestLaw_allPresent_mono`; the box probabilities converge by the weak
convergence of the box laws. These events form a π-system generating the edge σ-algebra,
so every weak cluster point of the volume laws is `squareLatticeUST`. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.SiteRoots

open LatticeProb MeasureTheory Filter Topology FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open scoped Classical ENNReal

noncomputable section

theorem exists_inBox_finset (S : Finset (Site 2)) : ∃ m : ℕ, ∀ z ∈ S, FiniteWired.inBox m z := by
  refine ⟨∑ z ∈ S, ((z 0).natAbs + (z 1).natAbs), fun z hz i => ?_⟩
  have hle : (z 0).natAbs + (z 1).natAbs ≤ ∑ w ∈ S, ((w 0).natAbs + (w 1).natAbs) :=
    Finset.single_le_sum (f := fun w : Site 2 => (w 0).natAbs + (w 1).natAbs)
      (fun _ _ => Nat.zero_le _) hz
  have hi : (z i).natAbs ≤ (z 0).natAbs + (z 1).natAbs := by
    fin_cases i <;> simp
  have hc : ((z i).natAbs : ℤ) ≤ ((∑ w ∈ S, ((w 0).natAbs + (w 1).natAbs) : ℕ) : ℤ) := by
    exact_mod_cast hi.trans hle
  rw [Int.natCast_natAbs] at hc
  exact abs_le.mp hc

theorem exists_inBox_edges (Fl : Finset LatticeEdge) :
    ∃ m : ℕ, ∀ e ∈ Fl, ∀ z ∈ e.val, FiniteWired.inBox m z := by
  obtain ⟨m, hm⟩ := exists_inBox_finset (Fl.biUnion fun e => e.val.toFinset)
  exact ⟨m, fun e he z hz =>
    hm z (Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hz⟩)⟩

theorem boxSet_mono {m M : ℕ} (h : m ≤ M) : boxSet m ⊆ boxSet M :=
  fun _ hx => inBox_mono h hx

theorem le_of_boxSet_subset {m M : ℕ} {Γ : Set (Site 2)} (h : boxSet m ⊆ Γ)
    (hΓ : ∀ x ∈ Γ, FiniteWired.inBox M x) : m ≤ M := by
  have hc : (fun _ : Fin 2 => (m : ℤ)) ∈ boxSet m := fun _ => ⟨by simp, by simp⟩
  have := (hΓ _ (h hc) 0).2
  exact_mod_cast this

theorem isClopen_allPresent (Fl : Finset LatticeEdge) : IsClopen (allPresent Fl) := by
  have h : allPresent Fl = ⋂ e ∈ Fl, {ω : EdgeField | ω e = true} := by
    ext ω
    simp [allPresent]
  rw [h]
  exact isClopen_biInter_finset fun e _ =>
    (isClopen_discrete {true}).preimage (continuous_apply e)

theorem finiteLaw_allPresent_tendsto (Fl : Finset LatticeEdge) :
    Tendsto (fun N => finiteLaw N (allPresent Fl)) atTop
      (𝓝 ((squareLatticeUST : Measure EdgeField) (allPresent Fl))) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' squareLatticeUST_tendsto
    (by rw [(isClopen_allPresent Fl).frontier_eq]; exact measure_empty)

/-- Along an exhaustion, the probability that a finite set of edges is present converges
to its probability under the wired uniform spanning tree. -/
theorem forestLaw_allPresent_tendsto (Γ : ℕ → Set (Site 2)) (M : ℕ → ℕ)
    (hM : ∀ n, ∀ x ∈ Γ n, FiniteWired.inBox (M n) x)
    (hΓ : ∀ m, ∀ᶠ n in atTop, boxSet m ⊆ Γ n) (Fl : Finset LatticeEdge) :
    Tendsto (fun n => forestLaw (Γ n) (M n) (allPresent Fl)) atTop
      (𝓝 ((squareLatticeUST : Measure EdgeField) (allPresent Fl))) := by
  obtain ⟨m0, hm0⟩ := exists_inBox_edges Fl
  have hbox := finiteLaw_allPresent_tendsto Fl
  have hMtend : Tendsto M atTop atTop := by
    rw [tendsto_atTop]
    intro m
    filter_upwards [hΓ m] with n hn
    exact le_of_boxSet_subset hn (hM n)
  have hupper : ∀ᶠ n in atTop,
      forestLaw (Γ n) (M n) (allPresent Fl) ≤ finiteLaw (M n) (allPresent Fl) := by
    filter_upwards [hΓ m0] with n hn
    rw [← forestLaw_boxSet (M n)]
    exact forestLaw_allPresent_mono (fun x hx => hM n x hx) (M n) Fl
      (fun e he z hz => hn (hm0 e he z hz))
  have hlower : ∀ m, m0 ≤ m → ∀ᶠ n in atTop,
      finiteLaw m (allPresent Fl) ≤ forestLaw (Γ n) (M n) (allPresent Fl) := by
    intro m hm
    filter_upwards [hΓ m] with n hn
    have hmM : m ≤ M n := le_of_boxSet_subset hn (hM n)
    rw [← forestLaw_boxSet m, forestLaw_eq_of_le (boxSet m) hmM (fun x hx => hx)]
    exact forestLaw_allPresent_mono hn (M n) Fl
      (fun e he z hz => boxSet_mono hm (hm0 e he z hz))
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨m, hm⟩ := (((tendsto_order.1 hbox).1 a ha).and (eventually_ge_atTop m0)).exists
    filter_upwards [hlower m hm.2] with n hn
    exact lt_of_lt_of_le hm.1 hn
  · filter_upwards [hupper, hMtend.eventually ((tendsto_order.1 hbox).2 b hb)] with n h1 h2
    exact lt_of_le_of_lt h1 h2

/-- The events that finite sets of edges are present generate the edge σ-algebra. -/
theorem generateFrom_allPresent :
    (inferInstance : MeasurableSpace EdgeField) =
      MeasurableSpace.generateFrom (Set.range allPresent) := by
  apply le_antisymm
  · have hmeas : @Measurable EdgeField EdgeField
        (MeasurableSpace.generateFrom (Set.range allPresent)) inferInstance id := by
      rw [@measurable_pi_iff]
      intro e
      apply @measurable_to_bool
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨{e}, ?_⟩
      ext ω
      simp [allPresent]
    exact fun s hs => hmeas hs
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨Fl, rfl⟩
    exact measurableSet_allPresent Fl

theorem isPiSystem_allPresent : IsPiSystem (Set.range allPresent) := by
  rintro s ⟨Fl, rfl⟩ t ⟨Fl', rfl⟩ _
  refine ⟨Fl ∪ Fl', ?_⟩
  ext ω
  simp only [allPresent, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_union]
  constructor
  · intro h
    exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
  · rintro ⟨h1, h2⟩ e (he | he)
    · exact h1 e he
    · exact h2 e he

/-- Probability measures on edge fields are determined by the presence probabilities of
finite edge sets. -/
theorem probabilityMeasure_eq_of_allPresent (μ ν : ProbabilityMeasure EdgeField)
    (h : ∀ Fl : Finset LatticeEdge,
      (μ : Measure EdgeField) (allPresent Fl) = (ν : Measure EdgeField) (allPresent Fl)) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  refine ext_of_generate_finite (Set.range allPresent) generateFrom_allPresent
    isPiSystem_allPresent ?_ (by simp)
  rintro s ⟨Fl, rfl⟩
  exact h Fl

/-- The rooted forest lattice law as a probability measure. -/
def forestProbability (Γ : Set (Site 2)) (N : ℕ) : ProbabilityMeasure EdgeField :=
  ⟨forestLaw Γ N, inferInstance⟩

@[simp] theorem forestProbability_toMeasure (Γ : Set (Site 2)) (N : ℕ) :
    (forestProbability Γ N : Measure EdgeField) = forestLaw Γ N := rfl

/-- Wired uniform spanning forests along an exhaustion converge weakly to the wired
uniform spanning tree of `ℤ²`. -/
theorem forestProbability_tendsto (Γ : ℕ → Set (Site 2)) (M : ℕ → ℕ)
    (hM : ∀ n, ∀ x ∈ Γ n, FiniteWired.inBox (M n) x)
    (hΓ : ∀ m, ∀ᶠ n in atTop, boxSet m ⊆ Γ n) :
    Tendsto (fun n => forestProbability (Γ n) (M n)) atTop (𝓝 squareLatticeUST) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  apply probabilityMeasure_eq_of_allPresent
  intro Fl
  obtain ⟨U, hU, hweak⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  have h1 := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak
    (E := allPresent Fl) (by rw [(isClopen_allPresent Fl).frontier_eq]; exact measure_empty)
  exact tendsto_nhds_unique h1 ((forestLaw_allPresent_tendsto Γ M hM hΓ Fl).mono_left hU)

end

end FiniteAvalanches.Wilson.Lattice.SiteRoots
