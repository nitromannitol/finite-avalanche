import FiniteAvalanches.Wilson.Lattice.WiredLawReduction

/-! Prescribed root colors under the recurrent Wilson cylinder law. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Every prescribed zero root has color zero almost surely. -/
theorem IsWilsonCylinderLaw.ae_zero_root_color (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (r : Site 2) (hr : r ∈ R.zero) :
    ∀ᵐ ω ∂(ν : Measure ForestField), ω.2 r = false := by
  let x : ℕ → Site 2 := fun _ => r
  let pc : Site 2 → Bool := fun _ => false
  let pe : LatticeEdge → Bool := fun _ => false
  have h := hν x 1 ∅ {r} pe pc (by simp) (by
    intro z hz
    have he : z = r := Finset.mem_singleton.mp hz
    exact ⟨0, by omega, he.symm⟩)
  have hL : (List.range 1).map x = [r] := rfl
  have hroot : r ∈ (initialSampler R).covered := by
    simp [SamplerState.covered, initialSampler, hr]
  have hevent : samplerEvent R [r] ∅ {r} pe pc = Set.univ := by
    ext rows
    simp only [Set.mem_univ, iff_true, samplerEvent, Set.mem_setOf_eq]
    refine ⟨initialSampler R, ?_, ?_, ?_⟩
    · exact samplerRun_of_covered _ _ (by simpa using hroot) rows
    · simp
    · intro z hz
      have he : z = r := Finset.mem_singleton.mp hz
      subst z
      simp [initialSampler, hr, pc]
  have hjoint : jointEvent ∅ {r} pe pc = {ω : ForestField | ω.2 r = false} := by
    ext ω
    simp [jointEvent, pc]
  rw [hL, hevent, measure_univ, hjoint] at h
  have hm : MeasurableSet {ω : ForestField | ω.2 r = false} :=
    ((isClopen_discrete {false}).preimage ((continuous_apply r).comp continuous_snd)).isClosed.measurableSet
  exact (mem_ae_iff_prob_eq_one hm).mpr h

/-- Every prescribed one root has color one almost surely. -/
theorem IsWilsonCylinderLaw.ae_one_root_color (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (r : Site 2) (hr : r ∈ R.one) :
    ∀ᵐ ω ∂(ν : Measure ForestField), ω.2 r = true := by
  let x : ℕ → Site 2 := fun _ => r
  let pc : Site 2 → Bool := fun _ => true
  let pe : LatticeEdge → Bool := fun _ => false
  have h := hν x 1 ∅ {r} pe pc (by simp) (by
    intro z hz
    have he : z = r := Finset.mem_singleton.mp hz
    exact ⟨0, by omega, he.symm⟩)
  have hL : (List.range 1).map x = [r] := rfl
  have hz : r ∉ R.zero := fun hz => Set.disjoint_left.mp R.disjoint hz hr
  have hroot : r ∈ (initialSampler R).covered := by
    simp [SamplerState.covered, initialSampler, hz, hr]
  have hevent : samplerEvent R [r] ∅ {r} pe pc = Set.univ := by
    ext rows
    simp only [Set.mem_univ, iff_true, samplerEvent, Set.mem_setOf_eq]
    refine ⟨initialSampler R, ?_, ?_, ?_⟩
    · exact samplerRun_of_covered _ _ (by simpa using hroot) rows
    · simp
    · intro z hz'
      have he : z = r := Finset.mem_singleton.mp hz'
      subst z
      simp [initialSampler, hz, hr, pc]
  have hjoint : jointEvent ∅ {r} pe pc = {ω : ForestField | ω.2 r = true} := by
    ext ω
    simp [jointEvent, pc]
  rw [hL, hevent, measure_univ, hjoint] at h
  have hm : MeasurableSet {ω : ForestField | ω.2 r = true} :=
    ((isClopen_discrete {true}).preimage ((continuous_apply r).comp continuous_snd)).isClosed.measurableSet
  exact (mem_ae_iff_prob_eq_one hm).mpr h

/-- All prescribed roots have their prescribed colors simultaneously. -/
theorem IsWilsonCylinderLaw.ae_root_colors (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν) :
    ∀ᵐ ω ∂(ν : Measure ForestField),
      (∀ r ∈ R.zero, ω.2 r = false) ∧ ∀ r ∈ R.one, ω.2 r = true := by
  have h0 : ∀ᵐ ω ∂(ν : Measure ForestField), ∀ r, r ∈ R.zero → ω.2 r = false := by
    apply ae_all_iff.mpr
    intro r
    by_cases hr : r ∈ R.zero
    · filter_upwards [hν.ae_zero_root_color R ν r hr] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall (fun _ h => (hr h).elim)
  have h1 : ∀ᵐ ω ∂(ν : Measure ForestField), ∀ r, r ∈ R.one → ω.2 r = true := by
    apply ae_all_iff.mpr
    intro r
    by_cases hr : r ∈ R.one
    · filter_upwards [hν.ae_one_root_color R ν r hr] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall (fun _ h => (hr h).elim)
  filter_upwards [h0, h1] with ω hω0 hω1
  exact ⟨hω0, hω1⟩

end
end FiniteAvalanches.Wilson.Lattice
