import FiniteAvalanches.Wilson.Lattice.Law

/-! Whole-site translations of the actual finite-query Wilson color sampler.
The query list is arbitrary and every row uses the same infinite iid increments. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.Translation
open LatticeProb MeasureTheory
open scoped Classical
noncomputable section

/-- Translate every original root; membership uses the inverse site translation. -/
def roots (R : RootPair) (z : Site 2) : RootPair where
  zero := {x | x - z ∈ R.zero}
  one := {x | x - z ∈ R.one}
  disjoint := Set.disjoint_left.mpr (fun _ h0 h1 => Set.disjoint_left.mp R.disjoint h0 h1)
  zero_nonempty := by
    obtain ⟨x, hx⟩ := R.zero_nonempty
    exact ⟨x + z, by simpa only [Set.mem_setOf_eq, add_sub_cancel_right] using hx⟩
  one_nonempty := by
    obtain ⟨x, hx⟩ := R.one_nonempty
    exact ⟨x + z, by simpa only [Set.mem_setOf_eq, add_sub_cancel_right] using hx⟩

/-- Translation on the entire Boolean field carrier, with no validity restriction. -/
def colors (z : Site 2) (σ : ColorField) : ColorField := fun x => σ (x - z)

theorem measurable_colors (z : Site 2) : Measurable (colors z) :=
  measurable_pi_lambda _ (fun x => measurable_pi_apply (x - z))

theorem position_add (x z : Site 2) (w : WalkDriver) (n : ℕ) :
    position (x + z) w n = position x w n + z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [position_succ, position_succ, ih]; abel

theorem initial_colors (R : RootPair) (z x : Site 2) :
    (initialSampler (roots R z)).colors (x + z) = (initialSampler R).colors x := by
  simp only [initialSampler, roots, Set.mem_setOf_eq, add_sub_cancel_right]

/-- Equal translated partial colors give exactly equal least hitting times,
including the genuine nonstopping case. -/
theorem hitTime_colors {st st' : SamplerState} (z : Site 2)
    (hc : ∀ v, st'.colors (v + z) = st.colors v) (x : Site 2) (w : WalkDriver) :
    hitTime st'.covered (x + z) w = hitTime st.covered x w := by
  have hm (n : ℕ) : position (x + z) w n ∈ st'.covered ↔
      position x w n ∈ st.covered := by
    simp only [SamplerState.covered, Set.mem_setOf_eq, position_add, hc]
  cases h : hitTime st.covered x w with
  | none =>
    apply (hitTime_eq_none_iff _ _ _).mpr
    intro n hn
    exact (hitTime_eq_none_iff _ _ _).mp h n ((hm n).mp hn)
  | some T =>
    apply (hitTime_eq_some_iff _ _ _ _).mpr
    obtain ⟨ht, hlt⟩ := (hitTime_eq_some_iff _ _ _ _).mp h
    exact ⟨(hm T).mpr ht, fun n hn hm' => hlt n hn ((hm n).mp hm')⟩

theorem eraseStep_map (a : List (Site 2)) (v z : Site 2) :
    eraseStep (a.map (fun x => x + z)) (v + z) =
      (eraseStep a v).map (fun x => x + z) := by
  simp only [eraseStep, List.takeWhile_map, List.map_append, List.map_cons, List.map_nil]
  simp only [Function.comp_def, ne_eq, add_left_inj]

theorem walkErase_map (x z : Site 2) (w : WalkDriver) (T : ℕ) :
    walkErase (x + z) w T = (walkErase x w T).map (fun v => v + z) := by
  unfold walkErase
  exact List.foldl_hom (fun a : List (Site 2) => a.map (fun v => v + z))
    (g₁ := fun acc n => eraseStep acc (position x w n))
    (g₂ := fun acc n => eraseStep acc (position (x + z) w n))
    (init := []) (l := List.range (T + 1))
    (fun a n => by rw [position_add, eraseStep_map])

/-- Successful steps transport every partial site color. Edges and histories are
those produced by the actual translated sampler, rather than a substitute law. -/
theorem step_success {st st' out : SamplerState} (z : Site 2)
    (hc : ∀ v, st'.colors (v + z) = st.colors v) (x : Site 2) (w : WalkDriver)
    (hout : samplerStep st x w = some out) :
    ∃ out', samplerStep st' (x + z) w = some out' ∧
      ∀ v, out'.colors (v + z) = out.colors v := by
  have hx : x + z ∈ st'.covered ↔ x ∈ st.covered := by
    simp only [SamplerState.covered, Set.mem_setOf_eq, hc]
  by_cases hcovered : x ∈ st.covered
  · have he : out = st := by
      simpa only [samplerStep, if_pos hcovered, Option.some.injEq] using hout.symm
    subst out
    exact ⟨st', by rw [samplerStep, if_pos (hx.mpr hcovered)], hc⟩
  · rw [samplerStep, if_neg hcovered] at hout
    rw [samplerStep, if_neg (fun h => hcovered (hx.mp h)), hitTime_colors z hc]
    cases hT : hitTime st.covered x w with
    | none => simp only [hT] at hout; cases hout
    | some T =>
      simp only [hT, Option.some.injEq] at hout
      subst out
      refine ⟨_, rfl, ?_⟩
      intro v
      have hb : v + z ∈ (walkErase (x + z) w T).dropLast ↔
          v ∈ (walkErase x w T).dropLast := by
        rw [walkErase_map, ← List.map_dropLast]
        simp only [List.mem_map, add_left_inj, exists_eq_right]
      simp only [hb, position_add, hc]

/-- Arbitrary finite query lists transport under unchanged iid rows. -/
theorem run_success {st st' out : SamplerState} (z : Site 2)
    (hc : ∀ v, st'.colors (v + z) = st.colors v) (L : List (Site 2))
    (ξ : ℕ → WalkDriver) (hout : samplerRun st L ξ = some out) :
    ∃ out', samplerRun st' (L.map (fun x => x + z)) ξ = some out' ∧
      ∀ v, out'.colors (v + z) = out.colors v := by
  induction L generalizing st st' ξ with
  | nil =>
    have he : st = out := Option.some.inj hout
    subst st
    exact ⟨st', rfl, hc⟩
  | cons x xs ih =>
    cases hs : samplerStep st x (ξ 0) with
    | none => simp only [samplerRun, hs, Option.bind_none] at hout; cases hout
    | some mid =>
      obtain ⟨mid', hs', hm⟩ := step_success z hc x (ξ 0) hs
      have hr : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hs, Option.bind_some] using hout
      obtain ⟨out', ho, hc'⟩ := ih hm _ hr
      exact ⟨out', by simpa only [List.map_cons, samplerRun, hs', Option.bind_some] using ho, hc'⟩

end
end FiniteAvalanches.Wilson.Lattice.Translation
