import FiniteAvalanches.Wilson.Lattice.RaySeededMeasurability

/-! Recurrent ray-seeded Wilson sampling on the square lattice.

Seed Wilson's algorithm with an independent ray `γ` of the law of the uniform spanning tree
ray from `o`, and run the walks of the query order with independent rows, each stopped on
the ray and the earlier branches. Almost surely every walk stops (planar recurrence), and
the ray together with the branches has the law of the uniform spanning tree with its ray
from `o` (van Engelenburg–Hutchcroft, arXiv:2301.03875v1, §2.5 Lemma 10). An edge whose
endpoints are queried is decided by the corresponding finite run, so the joint law is
determined on ray-prefix and finite edge cylinders, where it is the distant-root limit
of `ray_seeded_cylinder`. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.RaySeeded

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice
open TreeMeasurability11
open scoped Classical ENNReal Topology

attribute [local instance] rayMeasurableSpace

noncomputable section

/-- Prefix runs from the seed roots reveal the same edges as runs from the covered seed. -/
theorem prefixRun_iff (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows) (n : ℕ)
    (P : Finset (Sym2 (Site 2)) → Prop) :
    (∃ st, prefixRun γ order ξ n = some st ∧ P st.edges) ↔
      ∃ out, samplerRun (coverState γ.vertices) ((List.range n).map order) ξ = some out ∧
        P out.edges := by
  have hc : (initialSampler (seedRoots γ)).covered = (coverState γ.vertices).covered := by
    rw [initial_covered, coverState_covered]
  constructor
  · rintro ⟨st, hst, hP⟩
    obtain ⟨out, hout, -, N, h1, h2⟩ := samplerRun_congr hc hst
    refine ⟨out, hout, ?_⟩
    have : out.edges = st.edges := by
      rw [h1, h2]
      rfl
    rwa [this]
  · rintro ⟨out, hout, hP⟩
    obtain ⟨st, hst, -, N, h1, h2⟩ := samplerRun_congr hc.symm hout
    refine ⟨st, hst, ?_⟩
    have : st.edges = out.edges := by
      rw [h1, h2]
      rfl
    rwa [this]

/-- The completed edge field of the algorithm. -/
def completion (order : ℕ → Site 2) (q : SimpleRay × Rows) : EdgeField :=
  fun e => decide (EdgePresent q.1 order q.2 e)

theorem measurableSet_edgePresent (order : ℕ → Site 2) (e : LatticeEdge) :
    MeasurableSet {q : SimpleRay × Rows | EdgePresent q.1 order q.2 e} := by
  have he : {q : SimpleRay × Rows | EdgePresent q.1 order q.2 e} =
      Prod.fst ⁻¹' {γ | e.val ∈ seedEdges γ} ∪ ⋃ n : ℕ, {q : SimpleRay × Rows |
        ∃ out, samplerRun (coverState q.1.vertices) ((List.range n).map order) q.2 = some out ∧
          e.val ∈ out.edges} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_preimage, Set.mem_iUnion, EdgePresent,
      seedEdges]
    apply or_congr Iff.rfl
    apply exists_congr
    intro n
    exact prefixRun_iff q.1 order q.2 n (fun s => e.val ∈ s)
  rw [he]
  exact (measurable_fst (measurableSet_seedEdges e.val)).union
    (MeasurableSet.iUnion fun n => measurableSet_rayRun ((List.range n).map order) (fun s => e.val ∈ s))

theorem measurable_completion (order : ℕ → Site 2) : Measurable (completion order) := by
  apply measurable_pi_lambda
  intro e
  apply measurable_to_bool
  have he : (fun q : SimpleRay × Rows => completion order q e) ⁻¹' {true} =
      {q | EdgePresent q.1 order q.2 e} := by
    ext q
    simp [completion]
  rw [he]
  exact measurableSet_edgePresent order e

theorem measurableSet_successful (order : ℕ → Site 2) :
    MeasurableSet {q : SimpleRay × Rows | Successful q.1 order q.2} := by
  have he : {q : SimpleRay × Rows | Successful q.1 order q.2} =
      ⋂ n : ℕ, {q : SimpleRay × Rows |
        ∃ out, samplerRun (coverState q.1.vertices) ((List.range n).map order) q.2 = some out ∧
          True} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Successful]
    apply forall_congr'
    intro n
    have := prefixRun_iff q.1 order q.2 n (fun _ => True)
    simpa only [and_true] using this
  rw [he]
  exact MeasurableSet.iInter fun n => measurableSet_rayRun ((List.range n).map order) (fun _ => True)

theorem successful_of_hits (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows)
    (h : ∀ i (x y : Site 2), ∃ n, position x (ξ i) n = y) : Successful γ order ξ := by
  intro n
  apply exists_samplerRun_of_hits _ _ ξ (γ.vertex 0) ?_ (fun i x => h i x (γ.vertex 0))
  rw [initial_covered]
  exact ⟨0, rfl⟩

theorem prefixRun_add (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows) (m d : ℕ)
    (st' : SamplerState) (h : prefixRun γ order ξ (m + d) = some st') :
    ∃ st, prefixRun γ order ξ m = some st ∧
      samplerRun st ((List.range d).map (fun i => order (m + i)))
        (fun i => ξ (i + ((List.range m).map order).length)) = some st' := by
  unfold prefixRun at h
  rw [List.range_add, List.map_append, samplerRun_append, List.map_map] at h
  cases hm : samplerRun (initialSampler (seedRoots γ)) ((List.range m).map order) ξ with
  | none => simp [hm] at h
  | some st =>
    refine ⟨st, hm, ?_⟩
    simpa only [hm, Option.bind_some, Function.comp_def] using h

/-- An edge whose endpoints are among the first `m` queries is decided by the first `m`
walks. -/
theorem edgePresent_iff_prefix (γ : SimpleRay) (order : ℕ → Site 2) (ξ : Rows) (m : ℕ) (st : SamplerState) (hst : prefixRun γ order ξ m = some st)
    (e : LatticeEdge) (he : ∀ x ∈ e.val, x ∈ (List.range m).map order) :
    EdgePresent γ order ξ e ↔ e.val ∈ seedEdges γ ∨ e.val ∈ st.edges := by
  unfold EdgePresent
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨n, st', hst', hmem⟩
    rcases le_total n m with hnm | hmn
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      obtain ⟨st'', h1, h2⟩ := prefixRun_add γ order ξ n d st hst
      rw [hst'] at h1
      cases h1
      exact samplerRun_edges_subset h2 hmem
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      obtain ⟨st'', h1, h2⟩ := prefixRun_add γ order ξ m d st' hst'
      rw [hst] at h1
      cases h1
      exact (samplerRun_edge_of_covered h2 e.val (fun v hv =>
        samplerRun_query_mem_covered hst v (he v hv))).mp hmem
  · intro hmem
    exact ⟨m, st, hst, hmem⟩

theorem exists_cover (order : ℕ → Site 2) (hsurj : Function.Surjective order)
    (E : Finset LatticeEdge) : ∃ m, ∀ e ∈ E, ∀ x ∈ e.val, x ∈ (List.range m).map order := by
  induction E using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert e E _ ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨a, b, hab⟩ : ∃ a b, e.val = s(a, b) :=
      Sym2.ind (f := fun s => ∃ a b, s = s(a, b)) (fun x y => ⟨x, y, rfl⟩) e.val
    obtain ⟨i, hi⟩ := hsurj a
    obtain ⟨j, hj⟩ := hsurj b
    refine ⟨m + i + j + 1, fun f hf x hx => ?_⟩
    simp only [List.mem_map, List.mem_range]
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rw [hab] at hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact ⟨i, by omega, hi⟩
      · exact ⟨j, by omega, hj⟩
    · obtain ⟨t, ht, hte⟩ := List.mem_map.mp (hm f hf x hx)
      exact ⟨t, by simp only [List.mem_range] at ht; omega, hte⟩

/-- For a fixed ray, the rows probability of a finite edge pattern of the completion. -/
theorem wilsonRows_completion_pattern (order : ℕ → Site 2) (γ : SimpleRay) (m : ℕ)
    (E : Finset LatticeEdge) (hE : ∀ e ∈ E, ∀ x ∈ e.val, x ∈ (List.range m).map order)
    (pE : LatticeEdge → Bool) :
    wilsonRows {ξ | ∀ e ∈ E, completion order (γ, ξ) e = pE e} =
      seedTail ((List.range m).map order) E pE γ := by
  apply measure_congr
  filter_upwards [wilsonRows_ae_hits_all] with ξ hhit
  have hs := successful_of_hits γ order ξ hhit
  obtain ⟨st, hst⟩ := hs m
  obtain ⟨out, hout, hedges⟩ := (prefixRun_iff γ order ξ m (fun s => s = st.edges)).mp ⟨st, hst, rfl⟩
  apply propext
  change (∀ e ∈ E, completion order (γ, ξ) e = pE e) ↔
    ∃ out, samplerRun (coverState γ.vertices) ((List.range m).map order) ξ = some out ∧
      ∀ e ∈ E, decide (e.val ∈ out.edges ∨ e.val ∈ seedEdges γ) = pE e
  have key : ∀ e ∈ E, completion order (γ, ξ) e =
      decide (e.val ∈ out.edges ∨ e.val ∈ seedEdges γ) := by
    intro e he
    simp only [completion]
    apply decide_eq_decide.mpr
    rw [edgePresent_iff_prefix γ order ξ m st hst e (hE e he), hedges, or_comm]
  constructor
  · intro h
    exact ⟨out, hout, fun e he => (key e he).symm.trans (h e he)⟩
  · rintro ⟨out', hout', h⟩ e he
    rw [hout] at hout'
    cases hout'
    exact (key e he).trans (h e he)

/-- Ray-prefix and finite edge cylinders. -/
def cyl (k : ℕ) (R : Set (Fin (k + 1) → Site 2)) (E : Finset LatticeEdge) (pE : LatticeEdge → Bool) :
    Set (SimpleRay × EdgeField) :=
  {q | rayPrefix k q.1 ∈ R ∧ ∀ e ∈ E, q.2 e = pE e}

/-- The family of all such cylinders. -/
def cylinders : Set (Set (SimpleRay × EdgeField)) :=
  {S | ∃ k R E pE, S = cyl k R E pE}

theorem measurable_rayPrefix (k : ℕ) : Measurable (rayPrefix k) :=
  measurable_pi_lambda _ fun i => measurable_rayVertex' i

theorem measurableSet_cyl (k : ℕ) (R : Set (Fin (k + 1) → Site 2)) (E : Finset LatticeEdge)
    (pE : LatticeEdge → Bool) : MeasurableSet (cyl k R E pE) :=
  (measurable_fst ((measurable_rayPrefix k) (Set.to_countable R).measurableSet)).inter
    (measurable_snd (measurableSet_edgePattern E pE))

theorem isPiSystem_cylinders : IsPiSystem cylinders := by
  rintro S ⟨k1, R1, E1, p1, rfl⟩ T ⟨k2, R2, E2, p2, rfl⟩ ⟨q0, hq1, hq2⟩
  refine ⟨k1 + k2, {a | (fun i : Fin (k1 + 1) => a ⟨i, by omega⟩) ∈ R1 ∧
      (fun i : Fin (k2 + 1) => a ⟨i, by omega⟩) ∈ R2}, E1 ∪ E2, q0.2, ?_⟩
  ext q
  simp only [cyl, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union]
  have hr1 : (fun i : Fin (k1 + 1) => rayPrefix (k1 + k2) q.1 ⟨i, by omega⟩) = rayPrefix k1 q.1 := rfl
  have hr2 : (fun i : Fin (k2 + 1) => rayPrefix (k1 + k2) q.1 ⟨i, by omega⟩) = rayPrefix k2 q.1 := rfl
  rw [hr1, hr2]
  constructor
  · rintro ⟨⟨h1, h1e⟩, h2, h2e⟩
    refine ⟨⟨h1, h2⟩, fun e he => ?_⟩
    rcases he with he | he
    · rw [h1e e he, hq1.2 e he]
    · rw [h2e e he, hq2.2 e he]
  · rintro ⟨⟨h1, h2⟩, he⟩
    exact ⟨⟨h1, fun e h => by rw [he e (Or.inl h), hq1.2 e h]⟩,
      ⟨h2, fun e h => by rw [he e (Or.inr h), hq2.2 e h]⟩⟩

theorem generateFrom_cylinders :
    (inferInstance : MeasurableSpace (SimpleRay × EdgeField)) =
      MeasurableSpace.generateFrom cylinders := by
  apply le_antisymm
  · change MeasurableSpace.comap Prod.fst rayMeasurableSpace ⊔
      MeasurableSpace.comap Prod.snd MeasurableSpace.pi ≤ _
    apply sup_le
    · rw [rayMeasurableSpace, MeasurableSpace.comap_comp, MeasurableSpace.pi,
        MeasurableSpace.comap_iSup]
      apply iSup_le
      intro i
      rw [MeasurableSpace.comap_comp]
      apply MeasurableSpace.comap_le_iff_le_map.mpr
      intro B _
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨i, {a | a (Fin.last i) ∈ B}, ∅, fun _ => true, ?_⟩
      ext q
      simp [cyl, rayPrefix]
    · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      apply iSup_le
      intro e
      rw [MeasurableSpace.comap_comp]
      apply MeasurableSpace.comap_le_iff_le_map.mpr
      intro B _
      have he : (fun q : SimpleRay × EdgeField => q.2 e) ⁻¹' B =
          ⋃ b ∈ B, cyl 0 Set.univ {e} (fun _ => b) := by
        ext q
        simp [cyl]
      change MeasurableSet[MeasurableSpace.generateFrom cylinders]
        ((fun q : SimpleRay × EdgeField => q.2 e) ⁻¹' B)
      rw [he]
      exact MeasurableSet.biUnion (Set.to_countable B) fun b _ =>
        MeasurableSpace.measurableSet_generateFrom ⟨0, Set.univ, {e}, fun _ => b, rfl⟩
  · apply MeasurableSpace.generateFrom_le
    rintro S ⟨k, R, E, pE, rfl⟩
    exact measurableSet_cyl k R E pE

/-- The proof of `square_lattice_ray_seeded_wilson`. -/
theorem square_lattice_ray_seeded_wilson_proof :
    ∀ (o : Site 2) (order : ℕ → Site 2), Function.Surjective order →
      ∃ ν : ProbabilityMeasure ((SimpleRay × Rows) × EdgeField),
        (ν : Measure ((SimpleRay × Rows) × EdgeField)).map Prod.fst =
          (rayLaw o).prod wilsonRows ∧
        (∀ᵐ p ∂(ν : Measure ((SimpleRay × Rows) × EdgeField)),
          Completes p.1.1 order p.1.2 p.2) ∧
        (ν : Measure ((SimpleRay × Rows) × EdgeField)).map (fun p => (p.1.1, p.2)) =
          endedUST.map (fun T => (seed o T, T.val)) := by
  intro o order hsurj
  let μ : Measure (SimpleRay × Rows) := (rayLaw o).prod wilsonRows
  let g : SimpleRay × Rows → (SimpleRay × Rows) × EdgeField := fun p => (p, completion order p)
  have hg : Measurable g := measurable_id.prodMk (measurable_completion order)
  haveI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  refine ⟨⟨μ.map g, inferInstance⟩, ?_, ?_, ?_⟩
  · change (μ.map g).map Prod.fst = μ
    rw [Measure.map_map measurable_fst hg]
    exact Measure.map_id
  · change ∀ᵐ p ∂(μ.map g), Completes p.1.1 order p.1.2 p.2
    have hC : MeasurableSet {p : (SimpleRay × Rows) × EdgeField | Completes p.1.1 order p.1.2 p.2} := by
      have he : {p : (SimpleRay × Rows) × EdgeField | Completes p.1.1 order p.1.2 p.2} =
          Prod.fst ⁻¹' {q | Successful q.1 order q.2} ∩
            ⋂ e : LatticeEdge, {p : (SimpleRay × Rows) × EdgeField |
              p.2 e = completion order p.1 e} := by
        ext p
        simp only [Completes, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_iInter, completion]
        apply and_congr Iff.rfl
        apply forall_congr'
        intro e
        rcases Bool.eq_false_or_eq_true (p.2 e) with h | h <;> simp [h]
      rw [he]
      exact (measurable_fst (measurableSet_successful order)).inter
        (MeasurableSet.iInter fun e => measurableSet_eq_fun ((measurable_pi_apply e).comp measurable_snd)
          ((measurable_pi_apply e).comp ((measurable_completion order).comp measurable_fst)))
    rw [ae_map_iff hg.aemeasurable hC]
    have hrows : ∀ᵐ q ∂μ, ∀ i (x y : Site 2), ∃ n, position x (q.2 i) n = y :=
      Measure.quasiMeasurePreserving_snd.ae wilsonRows_ae_hits_all
    filter_upwards [hrows] with q hq
    exact ⟨successful_of_hits q.1 order q.2 hq, fun e => by simp [g, completion]⟩
  · change (μ.map g).map (fun p => (p.1.1, p.2)) = _
    rw [Measure.map_map (measurable_fst.fst.prodMk measurable_snd) hg]
    have hseed := measurable_seed_tree o
    haveI : IsProbabilityMeasure (endedUST.map (fun T => (seed o T, T.val))) :=
      Measure.isProbabilityMeasure_map hseed.aemeasurable
    haveI : IsProbabilityMeasure (μ.map ((fun p : (SimpleRay × Rows) × EdgeField => (p.1.1, p.2)) ∘ g)) :=
      Measure.isProbabilityMeasure_map
        ((measurable_fst.fst.prodMk measurable_snd).comp hg).aemeasurable
    apply ext_of_generate_finite cylinders generateFrom_cylinders isPiSystem_cylinders
    · rintro S ⟨k, R, E, pE, rfl⟩
      obtain ⟨m, hm⟩ := exists_cover order hsurj E
      let L := (List.range m).map order
      have hRm : MeasurableSet R := (Set.to_countable R).measurableSet
      rw [Measure.map_apply ((measurable_fst.fst.prodMk measurable_snd).comp hg)
          (measurableSet_cyl k R E pE),
        Measure.map_apply hseed (measurableSet_cyl k R E pE)]
      have hpre : ((fun p : (SimpleRay × Rows) × EdgeField => (p.1.1, p.2)) ∘ g) ⁻¹' cyl k R E pE =
          {q : SimpleRay × Rows | rayPrefix k q.1 ∈ R ∧ ∀ e ∈ E, completion order q e = pE e} := by
        ext q
        simp [cyl, g]
      have hmeas : MeasurableSet
          {q : SimpleRay × Rows | rayPrefix k q.1 ∈ R ∧ ∀ e ∈ E, completion order q e = pE e} :=
        (measurable_fst ((measurable_rayPrefix k) hRm)).inter
          ((measurableSet_edgePattern E pE).preimage (measurable_completion order))
      rw [hpre, Measure.prod_apply hmeas]
      have hslice : ∀ γ : SimpleRay, wilsonRows (Prod.mk γ ⁻¹'
          {q : SimpleRay × Rows | rayPrefix k q.1 ∈ R ∧ ∀ e ∈ E, completion order q e = pE e}) =
          {γ : SimpleRay | rayPrefix k γ ∈ R}.indicator (seedTail L E pE) γ := by
        intro γ
        by_cases hγ : rayPrefix k γ ∈ R
        · rw [Set.indicator_of_mem (show γ ∈ {γ : SimpleRay | rayPrefix k γ ∈ R} from hγ),
            ← wilsonRows_completion_pattern order γ m E hm pE]
          congr 1
          ext ξ
          simp [hγ]
        · rw [Set.indicator_of_notMem (show γ ∉ {γ : SimpleRay | rayPrefix k γ ∈ R} from hγ)]
          have : Prod.mk γ ⁻¹' {q : SimpleRay × Rows |
              rayPrefix k q.1 ∈ R ∧ ∀ e ∈ E, completion order q e = pE e} = ∅ := by
            ext ξ
            simp [hγ]
          rw [this, measure_empty]
      simp only [hslice]
      have hcyl : (fun T : EndedTree => (seed o T, T.val)) ⁻¹' cyl k R E pE =
          {T | rayPrefix k (seed o T) ∈ R ∧ T.val ∈ {ω | ∀ e ∈ E, ω e = pE e}} := by
        ext T
        simp [cyl]
      have hF : Measurable ({γ : SimpleRay | rayPrefix k γ ∈ R}.indicator (seedTail L E pE)) :=
        (measurable_seedTail L E pE).indicator ((measurable_rayPrefix k) hRm)
      rw [hcyl, ray_seeded_cylinder o L E hm pE k R, rayLaw, lintegral_map hF (measurable_seed o)]
      congr 1
    · simp
end

end FiniteAvalanches.Wilson.Lattice.RaySeeded
