import FiniteAvalanches.Wilson.Lattice.RaySeededConvergence

/-! Joint measurability of the sampler in the root set and the rows.

A successful finite run depends only on the root membership of finitely many sites and
on finitely many increments of the rows used: every walk is read up to its hit, and the
root membership of the visited sites decides the hit. Hence the event that a run from the
root set `S` succeeds with a given set of revealed edges is open in the indicator of `S`
and the rows. Composing with the vertex indicator of a ray gives events that are jointly
measurable in the ray and the rows, and the ray-rooted probabilities are measurable in the
ray. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.RaySeeded

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice
open TreeMeasurability11
open scoped Classical ENNReal Topology

attribute [local instance] rayMeasurableSpace

noncomputable section

theorem position_congr (x : Site 2) {w w' : WalkDriver} :
    ∀ n, (∀ j < n, w' j = w j) → position x w' n = position x w n
  | 0, _ => rfl
  | n + 1, h => by
    rw [position_succ, position_succ, position_congr x n (fun j hj => h j (by omega)), h n (by omega)]

theorem walkErase_congr' (x : Site 2) {w w' : WalkDriver} (T : ℕ)
    (hp : ∀ n ≤ T, position x w' n = position x w n) : walkErase x w' T = walkErase x w T := by
  have hm : (List.range (T + 1)).map (position x w') = (List.range (T + 1)).map (position x w) :=
    List.map_congr_left (fun n hn => hp n (by have := List.mem_range.mp hn; omega))
  calc walkErase x w' T = ((List.range (T + 1)).map (position x w')).foldl eraseStep [] :=
        List.foldl_map.symm
    _ = ((List.range (T + 1)).map (position x w)).foldl eraseStep [] := by rw [hm]
    _ = walkErase x w T := List.foldl_map

/-- A successful run is decided by the root membership of finitely many sites and finitely
many increments of the rows it uses. -/
theorem samplerRun_local (L : List (Site 2)) :
    ∀ (st out : SamplerState) (ξ : ℕ → WalkDriver), samplerRun st L ξ = some out →
      ∃ (F : Finset (Site 2)) (N : ℕ), ∀ (st' : SamplerState) (ξ' : ℕ → WalkDriver),
        st'.edges = st.edges → (∀ v ∈ F, (v ∈ st'.covered ↔ v ∈ st.covered)) →
        (∀ i < L.length, ∀ j < N, ξ' i j = ξ i j) →
        ∃ out', samplerRun st' L ξ' = some out' ∧ out'.edges = out.edges := by
  induction L with
  | nil =>
    intro st out ξ hs
    have h : st = out := Option.some.inj hs
    subst h
    exact ⟨∅, 0, fun st' ξ' he _ _ => ⟨st', rfl, he⟩⟩
  | cons x xs ih =>
    intro st out ξ hs
    cases hstep : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hstep] at hs
    | some mid =>
      have htail : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hstep, Option.bind_some] using hs
      obtain ⟨F1, N1, h1⟩ := ih mid out _ htail
      by_cases hx : x ∈ st.covered
      · have hmid : mid = st := by
          simpa only [samplerStep, if_pos hx, Option.some.injEq] using hstep.symm
        subst hmid
        refine ⟨insert x F1, N1, fun st' ξ' he hc hξ => ?_⟩
        have hx' : x ∈ st'.covered := (hc x (Finset.mem_insert_self _ _)).mpr hx
        obtain ⟨out', h', he'⟩ := h1 st' (fun i => ξ' (i + 1)) he
          (fun v hv => hc v (Finset.mem_insert_of_mem hv))
          (fun i hi j hj => hξ (i + 1) (by simp; omega) j hj)
        refine ⟨out', ?_, he'⟩
        simpa only [samplerRun, samplerStep, if_pos hx', Option.bind_some] using h'
      · cases hT : hitTime st.covered x (ξ 0) with
        | none => simp [samplerStep, hx, hT] at hstep
        | some T =>
          rw [samplerStep_eq_appendWalkBranch st x (ξ 0) T hx hT, Option.some.injEq] at hstep
          subst hstep
          refine ⟨(Finset.range (T + 1)).image (position x (ξ 0)) ∪ F1, T + N1,
            fun st' ξ' he hc hξ => ?_⟩
          have hpos : ∀ n ≤ T, position x (ξ' 0) n = position x (ξ 0) n := fun n hn =>
            position_congr x n (fun j hj => hξ 0 (by simp) j (by omega))
          have hcovT : ∀ n ≤ T, (position x (ξ 0) n ∈ st'.covered ↔
              position x (ξ 0) n ∈ st.covered) := fun n hn =>
            hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _
              (Finset.mem_range.mpr (by omega))))
          have hx' : x ∉ st'.covered := by
            have := hcovT 0 (Nat.zero_le T)
            rw [position_zero] at this
            exact fun h => hx (this.mp h)
          obtain ⟨hTc, hTlt⟩ := (hitTime_eq_some_iff _ _ _ _).mp hT
          have hT' : hitTime st'.covered x (ξ' 0) = some T := by
            apply (hitTime_eq_some_iff _ _ _ _).mpr
            refine ⟨by rw [hpos T le_rfl]; exact (hcovT T le_rfl).mpr hTc, fun n hn => ?_⟩
            rw [hpos n hn.le]
            exact fun h => hTlt n hn ((hcovT n hn.le).mp h)
          have hβ := walkErase_congr' x T hpos
          have hstep' := samplerStep_eq_appendWalkBranch st' x (ξ' 0) T hx' hT'
          have hmidc : ∀ v ∈ F1, (v ∈ (appendWalkBranch st' x (ξ' 0) T).covered ↔
              v ∈ (appendWalkBranch st x (ξ 0) T).covered) := by
            intro v hv
            rw [covered_appendWalkBranch st' x (ξ' 0) T ((hitTime_eq_some_iff _ _ _ _).mp hT').1,
              covered_appendWalkBranch st x (ξ 0) T hTc, hβ]
            simp only [Set.mem_union, Set.mem_setOf_eq,
              hc v (Finset.mem_union_right _ hv)]
          have hmide : (appendWalkBranch st' x (ξ' 0) T).edges =
              (appendWalkBranch st x (ξ 0) T).edges := by
            simp only [appendWalkBranch, he, hβ]
          obtain ⟨out', h', he'⟩ := h1 _ (fun i => ξ' (i + 1)) hmide hmidc
            (fun i hi j hj => hξ (i + 1) (by simp; omega) j (by omega))
          refine ⟨out', ?_, he'⟩
          simpa only [samplerRun, hstep', Option.bind_some] using h'

/-- The covered state of a Boolean indicator. -/
def indicatorState (c : Site 2 → Bool) : SamplerState := coverState {v | c v = true}

theorem isOpen_indicatorRun (L : List (Site 2)) (P : Finset (Sym2 (Site 2)) → Prop) :
    IsOpen {q : (Site 2 → Bool) × (ℕ → WalkDriver) |
      ∃ out, samplerRun (indicatorState q.1) L q.2 = some out ∧ P out.edges} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨c, ξ⟩ ⟨out, hout, hP⟩
  obtain ⟨F, N, hloc⟩ := samplerRun_local L _ out ξ hout
  have h1 : {c' : Site 2 → Bool | ∀ v ∈ F, c' v = c v} ∈ 𝓝 c := by
    simp only [Set.setOf_forall]
    exact (Filter.biInter_finset_mem F).mpr fun v _ =>
      (continuous_apply v).continuousAt.preimage_mem_nhds
        ((isOpen_discrete {c v}).mem_nhds rfl)
  have h2 : {ξ' : ℕ → WalkDriver | ∀ i < L.length, ∀ j < N, ξ' i j = ξ i j} ∈ 𝓝 ξ := by
    have : {ξ' : ℕ → WalkDriver | ∀ i < L.length, ∀ j < N, ξ' i j = ξ i j} =
        ⋂ i ∈ Finset.range L.length, ⋂ j ∈ Finset.range N, {ξ' | ξ' i j = ξ i j} := by
      ext ξ'
      simp
    rw [this]
    exact (Filter.biInter_finset_mem _).mpr fun i _ => (Filter.biInter_finset_mem _).mpr
      fun j _ => (show Continuous fun ξ' : ℕ → WalkDriver => ξ' i j from
        (continuous_apply j).comp (continuous_apply i)).continuousAt.preimage_mem_nhds
          ((isOpen_discrete {ξ i j}).mem_nhds rfl)
  filter_upwards [prod_mem_nhds h1 h2] with q hq
  obtain ⟨out', h', he'⟩ := hloc (indicatorState q.1) q.2 rfl
    (fun v hv => by
      simp only [indicatorState, coverState_covered, Set.mem_setOf_eq, hq.1 v hv])
    hq.2
  exact ⟨out', h', he' ▸ hP⟩

/-- The vertex indicator of a ray. -/
def rayIndicator (γ : SimpleRay) : Site 2 → Bool := fun v => decide (v ∈ γ.vertices)

theorem measurable_rayVertex' (i : ℕ) : Measurable (fun γ : SimpleRay => γ.vertex i) :=
  (measurable_pi_apply i).comp (comap_measurable (fun γ : SimpleRay => γ.vertex))

theorem measurable_rayIndicator : Measurable rayIndicator := by
  apply measurable_pi_lambda
  intro v
  apply measurable_to_bool
  have he : (fun γ : SimpleRay => rayIndicator γ v) ⁻¹' {true} =
      ⋃ i : ℕ, (fun γ : SimpleRay => γ.vertex i) ⁻¹' {v} := by
    ext γ
    simp [rayIndicator, SimpleRay.vertices]
  rw [he]
  exact MeasurableSet.iUnion fun i => measurable_rayVertex' i (measurableSet_singleton v)

/-- Runs rooted at the vertices of a ray are jointly measurable in the ray and the rows. -/
theorem measurableSet_rayRun (L : List (Site 2)) (P : Finset (Sym2 (Site 2)) → Prop) :
    MeasurableSet {q : SimpleRay × (ℕ → WalkDriver) |
      ∃ out, samplerRun (coverState q.1.vertices) L q.2 = some out ∧ P out.edges} := by
  have he : {q : SimpleRay × (ℕ → WalkDriver) |
      ∃ out, samplerRun (coverState q.1.vertices) L q.2 = some out ∧ P out.edges} =
      (fun q : SimpleRay × (ℕ → WalkDriver) => (rayIndicator q.1, q.2)) ⁻¹'
        {q : (Site 2 → Bool) × (ℕ → WalkDriver) |
          ∃ out, samplerRun (indicatorState q.1) L q.2 = some out ∧ P out.edges} := by
    ext q
    have hs : {v | rayIndicator q.1 v = true} = q.1.vertices := by
      ext v
      simp [rayIndicator]
    simp only [Set.mem_setOf_eq, Set.mem_preimage, indicatorState, hs]
  rw [he]
  haveI : SecondCountableTopology Bool := DiscreteTopology.secondCountableTopology_of_countable
  exact ((measurable_rayIndicator.comp measurable_fst).prodMk measurable_snd)
    (isOpen_indicatorRun L P).measurableSet

theorem measurableSet_seedEdges (s : Sym2 (Site 2)) :
    MeasurableSet {γ : SimpleRay | s ∈ seedEdges γ} := by
  have he : {γ : SimpleRay | s ∈ seedEdges γ} =
      ⋃ i : ℕ, (fun γ : SimpleRay => (γ.vertex i, γ.vertex (i + 1))) ⁻¹'
        {p | s = s(p.1, p.2)} := by
    ext γ
    simp [seedEdges]
  rw [he]
  exact MeasurableSet.iUnion fun i =>
    ((measurable_rayVertex' i).prodMk (measurable_rayVertex' (i + 1)))
      (Set.to_countable _).measurableSet

/-- The event defining `seedTail`, jointly in the ray and the rows. -/
theorem measurableSet_seedTailEvent (L : List (Site 2)) (E : Finset LatticeEdge)
    (pE : LatticeEdge → Bool) :
    MeasurableSet {q : SimpleRay × (ℕ → WalkDriver) |
      ∃ out, samplerRun (coverState q.1.vertices) L q.2 = some out ∧
        ∀ e ∈ E, decide (e.val ∈ out.edges ∨ e.val ∈ seedEdges q.1) = pE e} := by
  have he : {q : SimpleRay × (ℕ → WalkDriver) |
      ∃ out, samplerRun (coverState q.1.vertices) L q.2 = some out ∧
        ∀ e ∈ E, decide (e.val ∈ out.edges ∨ e.val ∈ seedEdges q.1) = pE e} =
      ⋃ D ∈ E.powerset, ({q : SimpleRay × (ℕ → WalkDriver) |
        ∀ e ∈ E, (e.val ∈ seedEdges q.1 ↔ e ∈ D)} ∩
        {q | ∃ out, samplerRun (coverState q.1.vertices) L q.2 = some out ∧
          ∀ e ∈ E, decide (e.val ∈ out.edges ∨ e ∈ D) = pE e}) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_powerset,
      exists_prop]
    constructor
    · rintro ⟨out, hout, hp⟩
      refine ⟨E.filter (fun e => e.val ∈ seedEdges q.1), Finset.filter_subset _ _,
        fun e he => by simp [he], out, hout, fun e he => ?_⟩
      rw [← hp e he]
      simp [he]
    · rintro ⟨D, -, hD, out, hout, hp⟩
      refine ⟨out, hout, fun e he => ?_⟩
      rw [← hp e he]
      exact decide_eq_decide.mpr (or_congr_right (hD e he))
  rw [he]
  refine Finset.measurableSet_biUnion _ fun D _ => MeasurableSet.inter ?_
    (measurableSet_rayRun L (fun edges => ∀ e ∈ E, decide (e.val ∈ edges ∨ e ∈ D) = pE e))
  have : {q : SimpleRay × (ℕ → WalkDriver) | ∀ e ∈ E, (e.val ∈ seedEdges q.1 ↔ e ∈ D)} =
      ⋂ e ∈ E, Prod.fst ⁻¹' {γ | (e.val ∈ seedEdges γ ↔ e ∈ D)} := by
    ext q
    simp
  rw [this]
  refine Finset.measurableSet_biInter _ fun e _ => measurable_fst ?_
  by_cases hD : e ∈ D
  · have h : {γ : SimpleRay | (e.val ∈ seedEdges γ ↔ e ∈ D)} = {γ | e.val ∈ seedEdges γ} := by
      ext γ
      simp [hD]
    rw [h]
    exact measurableSet_seedEdges e.val
  · have h : {γ : SimpleRay | (e.val ∈ seedEdges γ ↔ e ∈ D)} = {γ | e.val ∈ seedEdges γ}ᶜ := by
      ext γ
      simp [hD]
    rw [h]
    exact (measurableSet_seedEdges e.val).compl

theorem measurable_seedTail (L : List (Site 2)) (E : Finset LatticeEdge) (pE : LatticeEdge → Bool) :
    Measurable (seedTail L E pE) :=
  measurable_measure_prodMk_left (measurableSet_seedTailEvent L E pE)

end

end FiniteAvalanches.Wilson.Lattice.RaySeeded
