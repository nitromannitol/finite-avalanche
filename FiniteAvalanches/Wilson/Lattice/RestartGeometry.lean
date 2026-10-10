import FiniteAvalanches.Wilson.Lattice.BatchRestart
import FiniteAvalanches.Wilson.Lattice.PrependRay

/-! Geometry of the actual enlarged roots after a finite Wilson exploration. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.ActualRestartGeometry
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile BatchRestart
open scoped Classical
noncomputable section

theorem samplerStep_history_subset (st out : SamplerState) (x : Site 2)
    (w : WalkDriver) (hs : samplerStep st x w = some out) :
    st.history ⊆ out.history := by
  by_cases hx : x ∈ st.covered
  · have he : st = out := Option.some.inj (by
      simpa only [samplerStep, if_pos hx] using hs)
    subst out
    exact List.Subset.refl _
  · cases hT : hitTime st.covered x w with
    | none => simp only [samplerStep, if_neg hx, hT] at hs; cases hs
    | some T =>
      have he := Option.some.inj (by
        simpa only [samplerStep, if_neg hx, hT] using hs)
      rw [← he]
      exact fun p hp => List.mem_append.mpr (Or.inl hp)

theorem samplerStep_colors_eq_or_visited (st out : SamplerState) (x : Site 2)
    (w : WalkDriver) (hs : samplerStep st x w = some out) (v : Site 2) :
    out.colors v = st.colors v ∨
      ∃ p ∈ out.history, ∃ j : Fin (p.length + 1), p.vertex j = v := by
  by_cases hx : x ∈ st.covered
  · have he : st = out := Option.some.inj (by
      simpa only [samplerStep, if_pos hx] using hs)
    exact Or.inl (he ▸ rfl)
  · cases hT : hitTime st.covered x w with
    | none => simp only [samplerStep, if_neg hx, hT] at hs; cases hs
    | some T =>
      have he := Option.some.inj (by
        simpa only [samplerStep, if_neg hx, hT] using hs)
      rw [← he]
      by_cases hv : v ∈ (walkErase x w T).dropLast
      · obtain ⟨n, hn, hnv⟩ := walkErase_mem_visited x w T v (List.mem_of_mem_dropLast hv)
        refine Or.inr ⟨dirWalkFinite x w T, ?_, ⟨n, by change n < T + 1; omega⟩, hnv⟩
        exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · exact Or.inl (if_neg hv)

theorem samplerRun_history_subset (st out : SamplerState) (L : List (Site 2))
    (ξ : ℕ → WalkDriver) (hs : samplerRun st L ξ = some out) :
    st.history ⊆ out.history := by
  induction L generalizing st ξ with
  | nil =>
    have he : st = out := Option.some.inj hs
    subst out
    exact List.Subset.refl _
  | cons x xs ih =>
    cases hstep : samplerStep st x (ξ 0) with
    | none => simp only [samplerRun, hstep, Option.bind_none] at hs; cases hs
    | some mid =>
      have htail : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hstep, Option.bind_some] using hs
      exact fun p hp => ih mid (fun i => ξ (i + 1)) htail
        (samplerStep_history_subset st mid x (ξ 0) hstep hp)

/-- A changed color was visited by a complete stopped history, including its hit. -/
theorem samplerRun_colors_eq_or_visited (st out : SamplerState) (L : List (Site 2))
    (ξ : ℕ → WalkDriver) (hs : samplerRun st L ξ = some out) (v : Site 2) :
    out.colors v = st.colors v ∨
      ∃ p ∈ out.history, ∃ j : Fin (p.length + 1), p.vertex j = v := by
  induction L generalizing st ξ with
  | nil =>
    exact Or.inl (congrArg (fun q : SamplerState => q.colors v) (Option.some.inj hs).symm)
  | cons x xs ih =>
    cases hstep : samplerStep st x (ξ 0) with
    | none => simp only [samplerRun, hstep, Option.bind_none] at hs; cases hs
    | some mid =>
      have htail : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hstep, Option.bind_some] using hs
      rcases ih mid (fun i => ξ (i + 1)) htail with hc | hv
      · rcases samplerStep_colors_eq_or_visited st mid x (ξ 0) hstep v with hm | hm
        · exact Or.inl (hc.trans hm)
        · obtain ⟨p, hp, j, hj⟩ := hm
          exact Or.inr ⟨p, samplerRun_history_subset mid out xs
            (fun i => ξ (i + 1)) htail hp, j, hj⟩
      · exact Or.inr hv

/-- Original roots retain their colors on the entire root sets. -/
theorem original_roots_subset_restarted (R : RootPair) (L : List (Site 2))
    (ξ : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L ξ = some out) :
    R.zero ⊆ (restartedRoots R L ξ out hs).zero ∧
      R.one ⊆ (restartedRoots R L ξ out hs).one := by
  constructor
  · intro v hv
    have hc : (initialSampler R).colors v = some false := by
      simp only [initialSampler, if_pos hv]
    exact (samplerRun_preserves_covered_colors _ out L ξ hs v (by
      change (initialSampler R).colors v ≠ none
      rw [hc]
      exact Option.some_ne_none _)).trans hc
  · intro v hv
    have hz : v ∉ R.zero := fun h => Set.disjoint_left.mp R.disjoint h hv
    have hc : (initialSampler R).colors v = some true := by
      simp only [initialSampler, if_neg hz, if_pos hv]
    exact (samplerRun_preserves_covered_colors _ out L ξ hs v (by
      change (initialSampler R).colors v ≠ none
      rw [hc]
      exact Option.some_ne_none _)).trans hc

/-- Full-history confinement controls every newly colored zero root. -/
theorem restarted_zero_subset_of_history (R : RootPair) (L : List (Site 2))
    (ξ : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun (initialSampler R) L ξ = some out) (h : ℕ)
    (hstay : ∀ p ∈ out.history, ∀ j : Fin (p.length + 1),
      p.vertex j ∈ (boxSites h : Set (Site 2))) :
    (restartedRoots R L ξ out hs).zero ⊆ R.zero ∪ (boxSites h : Set (Site 2)) := by
  intro v hv
  rcases samplerRun_colors_eq_or_visited (initialSampler R) out L ξ hs v with hc | hc
  · apply Or.inl
    have hv' : out.colors v = some false := hv
    rw [hc] at hv'
    by_contra hz
    by_cases ho : v ∈ R.one
    · simp only [initialSampler, if_neg hz, if_pos ho] at hv'; cases hv'
    · simp only [initialSampler, if_neg hz, if_neg ho] at hv'; cases hv'
  · obtain ⟨p, hp, j, hj⟩ := hc
    exact Or.inr (hj ▸ hstay p hp j)

/-- Actual exploration from `K` and the whole disjoint adjacent ray supplies all
three root hypotheses of the revealed-root estimate. -/
theorem disjoint_ray_restarted_geometry (K : Finset (Site 2)) (γ : SimpleRay)
    (hK : ((lattice 2).induce (K : Set (Site 2))).Connected) (h0 : 0 ∈ K)
    (hd : Disjoint (K : Set (Site 2)) γ.vertices)
    (ha : (lattice 2).Adj 0 (γ.vertex 0))
    (L : List (Site 2)) (ξ : ℕ → WalkDriver) (out : SamplerState)
    (hs : samplerRun (initialSampler
      (prependConnectingPair K hK γ 0 h0 ha
        (fun n hn => Set.disjoint_left.mp hd hn ⟨n, rfl⟩)).roots) L ξ = some out)
    (h : ℕ) (hstay : ∀ p ∈ out.history, ∀ j : Fin (p.length + 1),
      p.vertex j ∈ (boxSites h : Set (Site 2))) :
    let R := (prependConnectingPair K hK γ 0 h0 ha
      (fun n hn => Set.disjoint_left.mp hd hn ⟨n, rfl⟩)).roots
    (K : Set (Site 2)) ⊆ (restartedRoots R L ξ out hs).zero ∧
      (restartedRoots R L ξ out hs).zero ⊆
        (K : Set (Site 2)) ∪ (boxSites h : Set (Site 2)) ∧
      γ.vertices ⊆ (restartedRoots R L ξ out hs).one := by
  dsimp only
  exact ⟨(original_roots_subset_restarted _ L ξ out hs).1,
    restarted_zero_subset_of_history _ L ξ out hs h hstay,
    (original_roots_subset_restarted _ L ξ out hs).2⟩

end
end FiniteAvalanches.Wilson.Lattice.ActualRestartGeometry
