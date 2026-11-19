import FiniteAvalanches.Wilson.Lattice.SamplerEvents
import FiniteAvalanches.External.PolyaSquareLatticeProof

/-! Recurrence implies termination of every finite two-color Wilson exploration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory
open scoped Classical

noncomputable section

/-- A successful sampler step keeps every previously covered site covered. -/
theorem SamplerState.covered_subset_of_samplerStep {st out : SamplerState}
    {x : Site 2} {w : WalkDriver} (h : samplerStep st x w = some out) :
    st.covered ⊆ out.covered := by
  by_cases hx : x ∈ st.covered
  · simp only [samplerStep, if_pos hx, Option.some.injEq] at h
    subst out
    exact Set.Subset.rfl
  · cases ht : hitTime st.covered x w with
    | none => simp [samplerStep, hx, ht] at h
    | some T =>
      have hend : st.colors (position x w T) ≠ none :=
        (hitTime_eq_some_iff _ _ _ _).mp ht |>.1
      simp only [samplerStep, hx, if_false, ht, Option.some.injEq] at h
      subst out
      intro y hy
      simp only [SamplerState.covered, Set.mem_setOf_eq] at hy ⊢
      split_ifs <;> assumption

/-- A walk which reaches a covered site produces a successful sampler step. -/
theorem exists_samplerStep_of_hit {st : SamplerState} {x : Site 2} {w : WalkDriver}
    (h : ∃ n, position x w n ∈ st.covered) :
    ∃ out, samplerStep st x w = some out := by
  by_cases hx : x ∈ st.covered
  · exact ⟨st, by simp [samplerStep, hx]⟩
  · have hn : hitTime st.covered x w ≠ none := by
      intro he
      exact (hitTime_eq_none_iff _ _ _).mp he h.choose h.choose_spec
    cases ht : hitTime st.covered x w with
    | none => exact (hn ht).elim
    | some T =>
      simp only [samplerStep, hx, if_false, ht]
      exact ⟨_, rfl⟩

/-- A common covered site hit by each row ensures termination of a finite run. -/
theorem exists_samplerRun_of_hits (st : SamplerState) (L : List (Site 2))
    (ξ : ℕ → WalkDriver) (r : Site 2) (hr : r ∈ st.covered)
    (hh : ∀ i x, ∃ n, position x (ξ i) n = r) :
    ∃ out, samplerRun st L ξ = some out := by
  induction L generalizing st ξ with
  | nil => exact ⟨st, rfl⟩
  | cons x xs ih =>
    obtain ⟨n, hn⟩ := hh 0 x
    obtain ⟨mid, hm⟩ := exists_samplerStep_of_hit ⟨n, hn ▸ hr⟩
    have hr' := SamplerState.covered_subset_of_samplerStep hm hr
    obtain ⟨out, ho⟩ := ih mid (fun i => ξ (i + 1)) hr' (fun i y => hh (i + 1) y)
    exact ⟨out, by simpa only [samplerRun, hm, Option.bind_some] using ho⟩

/-- Every finite exploration terminates almost surely, by planar recurrence. -/
theorem samplerRun_ae_success (R : RootPair) (L : List (Site 2)) :
    ∀ᵐ ξ ∂wilsonRows, ∃ out, samplerRun (initialSampler R) L ξ = some out := by
  obtain ⟨r, hr⟩ := R.zero_nonempty
  have hroot : r ∈ (initialSampler R).covered := by
    simp [SamplerState.covered, initialSampler, hr]
  have hhit (x : Site 2) : ∀ᵐ w ∂walkLaw, ∃ n, position x w n = r := by
    have hm : MeasurableSet {w : WalkDriver | ∃ n, position x w n = r} := by
      have he : {w : WalkDriver | ∃ n, position x w n = r} =
          ⋃ n : ℕ, {w | position x w n = r} := by ext w; simp
      rw [he]
      exact MeasurableSet.iUnion fun n =>
        (isClosed_eq (continuous_position x n) continuous_const).measurableSet
    exact (mem_ae_iff_prob_eq_one hm).mpr
      (FiniteAvalanches.ProvedStandards.polya_square_lattice_hits_every_site x r)
  have hall : ∀ᵐ ξ ∂wilsonRows, ∀ i (x : Site 2), ∃ n, position x (ξ i) n = r := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro x
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => walkLaw) i).quasiMeasurePreserving.ae
      (hhit x)
  filter_upwards [hall] with ξ hξ
  exact exists_samplerRun_of_hits _ _ _ _ hroot hξ

end
end FiniteAvalanches.Wilson.Lattice
