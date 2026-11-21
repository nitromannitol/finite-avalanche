import FiniteAvalanches.Wilson.Lattice.SiteRootTranslation
import FiniteAvalanches.Wilson.Lattice.OriginSamplerMarginals
import FiniteAvalanches.Wilson.Lattice.TranslationSampler

/-! The lattice Wilson sampler rooted at an arbitrary site.

Translating the query list and the root translates the revealed colors and edges of the
sampler under the same rows. Together with the translation invariance of the wired
uniform spanning tree, the finite edge marginals of the tree are those of the sampler
rooted at any site, for every finite query list revealing the observed edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- The initial Wilson state whose only root is the site `z`. -/
def rootSampler (z : Site 2) : SamplerState where
  colors x := if x = z then some false else none
  edges := ∅
  history := []

theorem rootSampler_covered (z : Site 2) : (rootSampler z).covered = {z} := by
  ext x
  by_cases hx : x = z <;> simp [SamplerState.covered, rootSampler, hx]

/-- Finite edge observation of the sampler rooted at `z`. -/
def rootSamplerEvent (z : Site 2) (L : List (Site 2)) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) : Set (ℕ → WalkDriver) :=
  {rows | ∃ out, samplerRun (rootSampler z) L rows = some out ∧
    ∀ e ∈ E, decide (e.val ∈ out.edges) = p e}

theorem tail_map_add (path : List (Site 2)) (z : Site 2) :
    (path.map (· + z)).tail = path.tail.map (· + z) := by
  cases path <;> rfl

theorem branchEdges_map (path : List (Site 2)) (z : Site 2) :
    branchEdges (path.map (· + z)) = (branchEdges path).image (Sym2.map (· + z)) := by
  ext s
  simp only [branchEdges, tail_map_add, List.zip_map, List.mem_toFinset, List.mem_map,
    Finset.mem_image, exists_exists_and_eq_and, Prod.map_fst, Prod.map_snd, Sym2.map_mk]

/-- A successful step transports its colors and its revealed edges. -/
theorem samplerStep_shift {st st' out : SamplerState} (z : Site 2)
    (hc : ∀ v, st'.colors (v + z) = st.colors v)
    (he : st'.edges = st.edges.image (Sym2.map (· + z))) (x : Site 2) (w : WalkDriver)
    (hout : samplerStep st x w = some out) :
    ∃ out', samplerStep st' (x + z) w = some out' ∧
      (∀ v, out'.colors (v + z) = out.colors v) ∧
      out'.edges = out.edges.image (Sym2.map (· + z)) := by
  have hx : x + z ∈ st'.covered ↔ x ∈ st.covered := by
    simp only [SamplerState.covered, Set.mem_setOf_eq, hc]
  by_cases hcovered : x ∈ st.covered
  · have heq : out = st := by
      simpa only [samplerStep, if_pos hcovered, Option.some.injEq] using hout.symm
    subst out
    exact ⟨st', by rw [samplerStep, if_pos (hx.mpr hcovered)], hc, he⟩
  · rw [samplerStep, if_neg hcovered] at hout
    rw [samplerStep, if_neg (fun h => hcovered (hx.mp h)), Translation.hitTime_colors z hc]
    cases hT : hitTime st.covered x w with
    | none => simp only [hT] at hout; cases hout
    | some T =>
      simp only [hT, Option.some.injEq] at hout
      subst out
      refine ⟨_, rfl, ?_, ?_⟩
      · intro v
        have hb : v + z ∈ (walkErase (x + z) w T).dropLast ↔
            v ∈ (walkErase x w T).dropLast := by
          rw [Translation.walkErase_map, ← List.map_dropLast]
          simp only [List.mem_map, add_left_inj, exists_eq_right]
        simp only [hb, Translation.position_add, hc]
      · simp only [he, Translation.walkErase_map, branchEdges_map, Finset.image_union]

/-- Arbitrary finite query lists transport colors and revealed edges. -/
theorem samplerRun_shift {st st' out : SamplerState} (z : Site 2)
    (hc : ∀ v, st'.colors (v + z) = st.colors v)
    (he : st'.edges = st.edges.image (Sym2.map (· + z))) (L : List (Site 2))
    (ξ : ℕ → WalkDriver) (hout : samplerRun st L ξ = some out) :
    ∃ out', samplerRun st' (L.map (· + z)) ξ = some out' ∧
      (∀ v, out'.colors (v + z) = out.colors v) ∧
      out'.edges = out.edges.image (Sym2.map (· + z)) := by
  induction L generalizing st st' ξ with
  | nil =>
    have h : st = out := Option.some.inj hout
    subst st
    exact ⟨st', rfl, hc, he⟩
  | cons x xs ih =>
    cases hs : samplerStep st x (ξ 0) with
    | none => simp only [samplerRun, hs, Option.bind_none] at hout; cases hout
    | some mid =>
      obtain ⟨mid', hs', hm, hme⟩ := samplerStep_shift z hc he x (ξ 0) hs
      have hr : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hs, Option.bind_some] using hout
      obtain ⟨out', ho, hc', he'⟩ := ih hm hme _ hr
      exact ⟨out', by simpa only [List.map_cons, samplerRun, hs', Option.bind_some] using ho,
        hc', he'⟩

theorem mem_image_map_add (z : Site 2) (D : Finset (Sym2 (Site 2))) (e : LatticeEdge) :
    e.val ∈ D.image (Sym2.map (· + z)) ↔ (SiteRoots.shiftEdge (-z) e).val ∈ D := by
  have he : Sym2.map (· + z) (SiteRoots.shiftEdge (-z) e).val = e.val :=
    congrArg Subtype.val (SiteRoots.shiftEdge_shiftEdge_neg z e)
  rw [← he]
  exact (Sym2.map.injective (add_left_injective z)).mem_finset_image

/-- The finite edge marginals of the wired uniform spanning tree are those of the Wilson
sampler rooted at any site `z`, for any query list revealing the observed edges. -/
theorem squareLatticeUST_edgeEvent_eq_rootSampler (z : Site 2) (q : ℕ → Site 2) (n : ℕ)
    (E : Finset LatticeEdge) (hE : ∀ e ∈ E, ∀ x ∈ e.val, ∃ i < n, q i = x)
    (p : LatticeEdge → Bool) :
    (squareLatticeUST : Measure EdgeField) {ω | ∀ e ∈ E, ω e = p e} =
      wilsonRows (rootSamplerEvent z ((List.range n).map q) E p) := by
  let E' := E.image (SiteRoots.shiftEdge (-z))
  let p' : LatticeEdge → Bool := fun e => p (SiteRoots.shiftEdge z e)
  let q' : ℕ → Site 2 := fun i => q i - z
  let L' := (List.range n).map q'
  have hE' : ∀ e ∈ E', ∀ x ∈ e.val, ∃ i < n, q' i = x := by
    intro e he x hx
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨i, hi, hqi⟩ := hE f hf _ ((SiteRoots.mem_shiftEdge (-z) f x).mp hx)
    exact ⟨i, hi, by simp only [q', hqi, sub_neg_eq_add, add_sub_cancel_right]⟩
  have h0 := wiredLimit_map_restrict squareLatticeUST squareLatticeUST_tendsto q' n E' hE'
  let pr : E' → Bool := fun e => p' e.val
  have hm : Measurable (E'.restrict : EdgeField → E' → Bool) :=
    measurable_pi_lambda _ (fun x => measurable_pi_apply x.val)
  have h1 : ((squareLatticeUST : Measure EdgeField).map E'.restrict) {pr} =
      (wilsonRows.map (originSamplerEdgeObservation L' E')) {pr} := by rw [h0]
  rw [Measure.map_apply hm (measurableSet_singleton pr),
    Measure.map_apply (measurable_originSamplerEdgeObservation L' E')
      (measurableSet_singleton pr)] at h1
  have hinv := SiteRoots.squareLatticeUST_map_shiftField z
  have hA : MeasurableSet {ω : EdgeField | ∀ e ∈ E, ω e = p e} := by
    have : {ω : EdgeField | ∀ e ∈ E, ω e = p e} = ⋂ e ∈ E, {ω | ω e = p e} := by
      ext ω
      simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun e _ =>
      (measurableSet_singleton (p e)).preimage (measurable_pi_apply e)
  calc (squareLatticeUST : Measure EdgeField) {ω | ∀ e ∈ E, ω e = p e}
      = ((squareLatticeUST : Measure EdgeField).map (SiteRoots.shiftField z))
          {ω | ∀ e ∈ E, ω e = p e} := by rw [hinv]
    _ = (squareLatticeUST : Measure EdgeField) ((E'.restrict : EdgeField → E' → Bool) ⁻¹' {pr}) := by
        rw [Measure.map_apply (SiteRoots.measurable_shiftField z) hA]
        congr 1
        ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff, SiteRoots.shiftField]
        constructor
        · intro h
          funext e
          obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp e.property
          change ω e.val = p (SiteRoots.shiftEdge z e.val)
          rw [← hfe, SiteRoots.shiftEdge_shiftEdge_neg]
          exact h f hf
        · intro h e he
          have := congrFun h ⟨SiteRoots.shiftEdge (-z) e, Finset.mem_image_of_mem _ he⟩
          change ω (SiteRoots.shiftEdge (-z) e) = p (SiteRoots.shiftEdge z (SiteRoots.shiftEdge (-z) e)) at this
          rwa [SiteRoots.shiftEdge_shiftEdge_neg] at this
    _ = wilsonRows (originSamplerEdgeObservation L' E' ⁻¹' {pr}) := h1
    _ = wilsonRows (rootSamplerEvent z ((List.range n).map q) E p) := by
        apply measure_congr
        filter_upwards [samplerRun_origin_ae_success L'] with ξ hξ
        obtain ⟨out, hout⟩ := hξ
        have hc : ∀ v, (rootSampler z).colors (v + z) = originInitialSampler.colors v := by
          intro v
          have hv : v + z = z ↔ v = 0 :=
            ⟨fun h => by simpa only [add_sub_cancel_right, sub_self] using congrArg (· - z) h,
              fun h => by rw [h, zero_add]⟩
          simp only [rootSampler, originInitialSampler, hv]
        obtain ⟨out', hout', -, he'⟩ := samplerRun_shift z hc (by simp [rootSampler,
          originInitialSampler]) L' ξ hout
        have hL : L'.map (· + z) = (List.range n).map q := by
          simp only [L', q', List.map_map, Function.comp_def, sub_add_cancel]
        rw [hL] at hout'
        have hobs := originSamplerEdgeObservation_of_success L' E' ξ out hout
        apply propext
        change originSamplerEdgeObservation L' E' ξ = pr ↔ _
        rw [hobs]
        constructor
        · intro h
          refine ⟨out', hout', fun e he => ?_⟩
          have := congrFun h ⟨SiteRoots.shiftEdge (-z) e, Finset.mem_image_of_mem _ he⟩
          change decide ((SiteRoots.shiftEdge (-z) e).val ∈ out.edges) =
            p (SiteRoots.shiftEdge z (SiteRoots.shiftEdge (-z) e)) at this
          rw [SiteRoots.shiftEdge_shiftEdge_neg] at this
          rw [he']
          simp only [mem_image_map_add]
          exact this
        · rintro ⟨out'', ho, h⟩
          rw [hout'] at ho
          cases ho
          funext e
          obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp e.property
          have := h f hf
          rw [he'] at this
          simp only [mem_image_map_add] at this
          change decide (e.val.val ∈ out.edges) = p (SiteRoots.shiftEdge z e.val)
          rw [← hfe, SiteRoots.shiftEdge_shiftEdge_neg]
          exact this

end

end FiniteAvalanches.Wilson.Lattice
