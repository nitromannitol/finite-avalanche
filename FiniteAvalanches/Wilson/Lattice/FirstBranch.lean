import FiniteAvalanches.Wilson.Lattice.SamplerPrefix
import FiniteAvalanches.Trees.Lattice.Topology
import FiniteAvalanches.Trees.Lattice.InfiniteLawProperties
import FiniteAvalanches.Wilson.Lattice.ColorMarginal

/-! The first branch of Wilson's algorithm rooted at a site.

Run the lattice sampler rooted at `z` with the walk from `o` first. Its first branch is
the loop erasure of that walk, a lattice path from `o` to `z`, and the remaining walks
use fresh rows and are stopped on this branch. For every lattice path `p` from `o` to `z`
and every finite edge pattern `A` revealed by the later queries,

  `UST(p ⊆ T, A) = UST(p ⊆ T) · P(the walks stopped on p reveal A)`.

The probability that the first branch is `p` and `A` holds is at most `UST(p ⊆ T, A)`,
since the edges of the first branch are retained; summing over `p` gives `UST(A)` on both
sides, because the uniform spanning tree contains exactly one path from `o` to `z`. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice
open scoped Classical ENNReal

noncomputable section

theorem isOpen_samplerRun_event (st : SamplerState) (L : List (Site 2))
    (P : SamplerState → Prop) :
    IsOpen {ξ : ℕ → WalkDriver | ∃ out, samplerRun st L ξ = some out ∧ P out} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ξ ⟨out, h, hp⟩
  filter_upwards [samplerRun_eventually_eq_of_some st out L ξ h] with ξ' h'
  exact ⟨out, h', hp⟩

theorem measurableSet_samplerRun_event (st : SamplerState) (L : List (Site 2))
    (P : SamplerState → Prop) :
    MeasurableSet {ξ : ℕ → WalkDriver | ∃ out, samplerRun st L ξ = some out ∧ P out} :=
  (isOpen_samplerRun_event st L P).measurableSet

theorem map_getD_range (L : List (Site 2)) :
    (List.range L.length).map (fun i => L.getD i 0) = L := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-- The finite edge marginals of the uniform spanning tree for an arbitrary query list. -/
theorem squareLatticeUST_edgeEvent_eq_rootSampler_list (z : Site 2) (L : List (Site 2))
    (E : Finset LatticeEdge) (hE : ∀ e ∈ E, ∀ x ∈ e.val, x ∈ L) (p : LatticeEdge → Bool) :
    (squareLatticeUST : Measure EdgeField) {ω | ∀ e ∈ E, ω e = p e} =
      wilsonRows (rootSamplerEvent z L E p) := by
  have h := squareLatticeUST_edgeEvent_eq_rootSampler z (fun i => L.getD i 0) L.length E
    (fun e he x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (hE e he x hx)
      exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩) p
  rwa [map_getD_range] at h

/-- Every queried site is covered after the run. -/
theorem samplerStep_query_mem_covered {st out : SamplerState} {x : Site 2} {w : WalkDriver}
    (h : samplerStep st x w = some out) : x ∈ out.covered := by
  by_cases hx : x ∈ st.covered
  · simp only [samplerStep, if_pos hx, Option.some.injEq] at h
    subst out
    exact hx
  · cases hT : hitTime st.covered x w with
    | none => simp [samplerStep, hx, hT] at h
    | some T =>
      rw [samplerStep_eq_appendWalkBranch st x w T hx hT, Option.some.injEq] at h
      subst out
      have hpos := ((hitTime_eq_some_iff _ _ _ _).mp hT).1
      rw [covered_appendWalkBranch st x w T hpos]
      exact Or.inl (walkErase_start_mem_dropLast x w T (fun he => hx (he ▸ hpos)))

theorem samplerRun_query_mem_covered {st out : SamplerState} {L : List (Site 2)}
    {ξ : ℕ → WalkDriver} (h : samplerRun st L ξ = some out) : ∀ x ∈ L, x ∈ out.covered := by
  induction L generalizing st ξ with
  | nil => simp
  | cons y ys ih =>
    cases hs : samplerStep st y (ξ 0) with
    | none => simp [samplerRun, hs] at h
    | some mid =>
      have ht : samplerRun mid ys (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hs, Option.bind_some] using h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact samplerRun_covered_subset ht (samplerStep_query_mem_covered hs)
      · exact ih ht x hx

theorem branchEdges_cons_cons (u v : Site 2) (l : List (Site 2)) :
    branchEdges (u :: v :: l) = insert s(u, v) (branchEdges (v :: l)) := by
  simp [branchEdges]

theorem mem_branchEdges_support {o z : Site 2} (p : (lattice 2).Walk o z) :
    ∀ e ∈ p.edges, e ∈ branchEdges p.support := by
  induction p with
  | nil => simp
  | cons h q ih =>
    intro e he
    rw [SimpleGraph.Walk.support_cons, ← SimpleGraph.Walk.cons_tail_support q,
      branchEdges_cons_cons, SimpleGraph.Walk.cons_tail_support q]
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (ih e he)

/-- Lattice paths from `o` to `z`. -/
abbrev LPath (o z : Site 2) := {p : (lattice 2).Walk o z // p.IsPath}

instance (o z : Site 2) : Countable ((lattice 2).Walk o z) :=
  SimpleGraph.Walk.support_injective.countable

/-- The lattice edges of a path. -/
def pathEdges {o z : Site 2} (p : (lattice 2).Walk o z) : Finset LatticeEdge :=
  (p.edges.attach.map (fun e => (⟨e.val, p.edges_subset_edgeSet e.property⟩ : LatticeEdge))).toFinset

theorem mem_pathEdges {o z : Site 2} (p : (lattice 2).Walk o z) (e : LatticeEdge) :
    e ∈ pathEdges p ↔ e.val ∈ p.edges := by
  simp only [pathEdges, List.mem_toFinset, List.mem_map, List.mem_attach, true_and]
  constructor
  · rintro ⟨f, rfl⟩
    exact f.property
  · intro he
    exact ⟨⟨e.val, he⟩, rfl⟩

/-- The edges of a path are present. -/
def Present {o z : Site 2} (p : (lattice 2).Walk o z) : Set EdgeField :=
  {ω | ∀ e ∈ pathEdges p, ω e = true}

theorem measurableSet_edgePattern (E : Finset LatticeEdge) (pE : LatticeEdge → Bool) :
    MeasurableSet {ω : EdgeField | ∀ e ∈ E, ω e = pE e} := by
  have h : {ω : EdgeField | ∀ e ∈ E, ω e = pE e} = ⋂ e ∈ E, {ω | ω e = pE e} := by
    ext ω
    simp
  rw [h]
  exact Finset.measurableSet_biInter _ fun e _ =>
    (measurableSet_singleton (pE e)).preimage (measurable_pi_apply e)

theorem measurableSet_present {o z : Site 2} (p : (lattice 2).Walk o z) :
    MeasurableSet (Present p) :=
  measurableSet_edgePattern (pathEdges p) (fun _ => true)

theorem present_iff_toGraph {o z : Site 2} (p : (lattice 2).Walk o z) (ω : EdgeField) :
    ω ∈ Present p ↔ ∀ e ∈ p.edges, e ∈ (toGraph ω).edgeSet := by
  constructor
  · intro h e he
    exact (edge_mem_toGraph_iff ω ⟨e, p.edges_subset_edgeSet he⟩).mpr
      (h _ ((mem_pathEdges p _).mpr he))
  · intro h e he
    exact (edge_mem_toGraph_iff ω e).mp (h e.val ((mem_pathEdges p e).mp he))

/-- A tree contains exactly one lattice path from `o` to `z`. -/
theorem existsUnique_present {ω : EdgeField} (hω : IsTree ω) (o z : Site 2) :
    ∃! p : LPath o z, ω ∈ Present p.val := by
  obtain ⟨q⟩ := hω.connected.preconnected o z
  let r := q.toPath
  refine ⟨⟨r.val.mapLe (toGraph_le_lattice ω), r.property.mapLe _⟩, ?_, ?_⟩
  · apply (present_iff_toGraph _ ω).mpr
    intro e he
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he
    exact r.val.edges_subset_edgeSet he
  · rintro ⟨p, hp⟩ hpres
    have hpres' := (present_iff_toGraph p ω).mp hpres
    have hu := hω.isAcyclic.path_unique ⟨p.transfer (toGraph ω) hpres', hp.transfer hpres'⟩ r
    apply Subtype.ext
    apply SimpleGraph.Walk.support_injective
    have hs := congrArg (fun s : (toGraph ω).Path o z => s.val.support) hu
    simp only [SimpleGraph.Walk.support_transfer] at hs
    rw [hs, SimpleGraph.Walk.support_mapLe_eq_support]

/-- The first branch of the walk from `o` stopped at `z` is the path `p`. -/
def FirstIs {o z : Site 2} (p : (lattice 2).Walk o z) : Set WalkDriver :=
  {w | ∃ T, hitTime {z} o w = some T ∧ walkErase o w T = p.support}

theorem measurableSet_hitTime_some (S : Set (Site 2)) (x : Site 2) (T : ℕ) :
    MeasurableSet {w : WalkDriver | hitTime S x w = some T} := by
  have he : {w : WalkDriver | hitTime S x w = some T} =
      {w | position x w T ∈ S} ∩ ⋂ n ∈ Finset.range T, {w | position x w n ∉ S} := by
    ext w
    simp [hitTime_eq_some_iff]
  rw [he]
  refine MeasurableSet.inter ?_ (Finset.measurableSet_biInter _ fun n _ => ?_)
  · exact (Set.to_countable S).measurableSet.preimage (continuous_position x T).measurable
  · exact (Set.to_countable S).measurableSet.compl.preimage (continuous_position x n).measurable

theorem measurableSet_walkErase_eq (x : Site 2) (T : ℕ) (l : List (Site 2)) :
    MeasurableSet {w : WalkDriver | walkErase x w T = l} := by
  let ps : WalkDriver → Fin (T + 1) → Site 2 := fun w n => position x w n
  have hps : Measurable ps :=
    measurable_pi_lambda _ fun n => (continuous_position x n).measurable
  let g : (Fin (T + 1) → Site 2) → List (Site 2) := fun a =>
    ((List.finRange (T + 1)).map a).foldl eraseStep []
  have he : {w : WalkDriver | walkErase x w T = l} = ps ⁻¹' {a | g a = l} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_preimage, g, ps, walkErase]
    rw [← List.foldl_map]
    have hm : (List.range (T + 1)).map (position x w) =
        (List.finRange (T + 1)).map (fun n : Fin (T + 1) => position x w n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp
    rw [hm]
  rw [he]
  exact (Set.to_countable _).measurableSet.preimage hps

theorem measurableSet_firstIs {o z : Site 2} (p : (lattice 2).Walk o z) :
    MeasurableSet (FirstIs p) := by
  have he : FirstIs p = ⋃ T : ℕ, {w | hitTime {z} o w = some T} ∩
      {w | walkErase o w T = p.support} := by
    ext w
    simp [FirstIs]
  rw [he]
  exact MeasurableSet.iUnion fun T =>
    (measurableSet_hitTime_some _ _ T).inter (measurableSet_walkErase_eq o T _)

theorem firstIs_disjoint {o z : Site 2} {p q : LPath o z} (h : p ≠ q) :
    Disjoint (FirstIs p.val) (FirstIs q.val) := by
  rw [Set.disjoint_left]
  rintro w ⟨T, hT, hp⟩ ⟨T', hT', hq⟩
  rw [hT] at hT'
  cases hT'
  exact h (Subtype.ext (SimpleGraph.Walk.support_injective (hp.symm.trans hq)))

/-- Every completed first walk has a lattice path as its loop erasure. -/
theorem exists_firstIs {o z : Site 2} (w : WalkDriver) (T : ℕ) (hT : hitTime {z} o w = some T) :
    ∃ p : LPath o z, w ∈ FirstIs p.val := by
  obtain ⟨l, hl⟩ := FiniteAvalanches.Walk.BarlowMasson.walkErase_start o w T
  have hc := FiniteAvalanches.Walk.BarlowMasson.walkErase_isChain_adj o w T
  have hnd := walkErase_nodup' o w T
  have hlast := FiniteAvalanches.Walk.BarlowMasson.walkErase_getLast o w T
  have hz : position o w T = z := ((hitTime_eq_some_iff _ _ _ _).mp hT).1
  rw [hl] at hc hnd
  have key : ∀ (m : List (Site 2)) (hm : m ≠ []), m = o :: l →
      m.getLast hm = (o :: l).getLast (List.cons_ne_nil o l) := by
    intro m hm h
    subst h
    rfl
  have hlast' := (key _ _ hl).symm.trans hlast
  rw [← FiniteAvalanches.Walk.BarlowMasson.position_eq, hz] at hlast'
  obtain ⟨p, hp, hs⟩ := exists_path_of_chain l hc hnd hlast'
  exact ⟨⟨p, hp⟩, T, hT, by rw [hl, hs]⟩

/-- The state after the first walk: the covered set is its loop erasure. -/
theorem rootSampler_firstStep {o z : Site 2} (hoz : o ≠ z) (w : WalkDriver) (T : ℕ)
    (hT : hitTime {z} o w = some T) :
    ∃ S1, samplerStep (rootSampler z) o w = some S1 ∧
      S1.covered = {v | v ∈ walkErase o w T} ∧ S1.edges = branchEdges (walkErase o w T) := by
  have hcov := rootSampler_covered z
  have ho : o ∉ (rootSampler z).covered := by rw [hcov]; exact hoz
  have hT' : hitTime (rootSampler z).covered o w = some T := by rw [hcov]; exact hT
  have hz : position o w T = z := ((hitTime_eq_some_iff _ _ _ _).mp hT).1
  refine ⟨_, samplerStep_eq_appendWalkBranch _ o w T ho hT', ?_, ?_⟩
  · rw [covered_appendWalkBranch _ o w T (by rw [hcov, hz]; rfl), hcov]
    ext v
    have happ := walkErase_dropLast_append_endpoint o w T
    rw [hz] at happ
    conv_rhs => rw [← happ]
    simp [or_comm]
  · simp [appendWalkBranch, rootSampler]

section Branch

variable (o z : Site 2) (L : List (Site 2)) (E : Finset LatticeEdge) (pE : LatticeEdge → Bool)

/-- The later walks are stopped on the path `p` and reveal the pattern `pE` on `E`. -/
def tailEvent (p : (lattice 2).Walk o z) : Set (ℕ → WalkDriver) :=
  {ξ | ∃ out, samplerRun (coverState {v | v ∈ p.support}) L ξ = some out ∧
    ∀ e ∈ E, decide (e.val ∈ out.edges ∨ e.val ∈ branchEdges p.support) = pE e}

theorem measurableSet_tailEvent (p : (lattice 2).Walk o z) :
    MeasurableSet (tailEvent o z L E pE p) :=
  measurableSet_samplerRun_event _ L _

/-- On the event that the first branch is `p`, the full run reveals `pE` exactly when the
later walks stopped on `p` do. -/
theorem firstIs_inter_rootSamplerEvent {o z : Site 2} (hoz : o ≠ z) (L : List (Site 2))
    (E : Finset LatticeEdge) (pE : LatticeEdge → Bool) (p : (lattice 2).Walk o z) :
    {ξ : ℕ → WalkDriver | ξ 0 ∈ FirstIs p} ∩ rootSamplerEvent z (o :: L) E pE =
      {ξ | ξ 0 ∈ FirstIs p} ∩ {ξ | (fun i => ξ (i + 1)) ∈ tailEvent o z L E pE p} := by
  ext ξ
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf, out, hout, hpat⟩
    refine ⟨hf, ?_⟩
    obtain ⟨T, hT, hβ⟩ := hf
    obtain ⟨S1, hS1, hcov, hedges⟩ := rootSampler_firstStep hoz (ξ 0) T hT
    have hrun : samplerRun S1 L (fun i => ξ (i + 1)) = some out := by
      simpa only [samplerRun, hS1, Option.bind_some] using hout
    have hc : S1.covered = (coverState {v | v ∈ p.support}).covered := by
      rw [hcov, coverState_covered, hβ]
    obtain ⟨out', hout', -, N, hN, hN'⟩ := samplerRun_congr hc hrun
    refine ⟨out', hout', fun e he => ?_⟩
    rw [← hpat e he, hN, hN', hedges, hβ]
    simp [coverState, or_comm]
  · rintro ⟨hf, out', hout', hpat⟩
    refine ⟨hf, ?_⟩
    obtain ⟨T, hT, hβ⟩ := hf
    obtain ⟨S1, hS1, hcov, hedges⟩ := rootSampler_firstStep hoz (ξ 0) T hT
    have hc : (coverState {v | v ∈ p.support}).covered = S1.covered := by
      rw [hcov, coverState_covered, hβ]
    obtain ⟨out, hout, -, N, hN', hN⟩ := samplerRun_congr hc hout'
    refine ⟨out, by simpa only [samplerRun, hS1, Option.bind_some] using hout, fun e he => ?_⟩
    rw [← hpat e he, hN, hN', hedges, hβ]
    simp [coverState, or_comm]

/-- The first branch is `p` and the later walks reveal `pE`: a product of probabilities. -/
theorem wilsonRows_firstIs_inter {o z : Site 2} (hoz : o ≠ z) (L : List (Site 2))
    (E : Finset LatticeEdge) (pE : LatticeEdge → Bool) (p : (lattice 2).Walk o z) :
    wilsonRows ({ξ | ξ 0 ∈ FirstIs p} ∩ rootSamplerEvent z (o :: L) E pE) =
      walkLaw (FirstIs p) * wilsonRows (tailEvent o z L E pE p) := by
  rw [firstIs_inter_rootSamplerEvent hoz L E pE p]
  exact wilsonRows_head_tail _ _ (measurableSet_firstIs p) (measurableSet_tailEvent o z L E pE p)

end Branch

theorem measurableSet_rootSamplerEvent (z : Site 2) (L : List (Site 2)) (E : Finset LatticeEdge)
    (pE : LatticeEdge → Bool) : MeasurableSet (rootSamplerEvent z L E pE) :=
  measurableSet_samplerRun_event _ L _

theorem mem_support_of_mem_edge {o z : Site 2} (p : (lattice 2).Walk o z) {e : Sym2 (Site 2)}
    (he : e ∈ p.edges) {x : Site 2} (hx : x ∈ e) : x ∈ p.support := by
  induction e using Sym2.ind with
  | h a b =>
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact p.fst_mem_support_of_mem_edges he
    · exact p.snd_mem_support_of_mem_edges he

/-- The edges of the first branch are retained by the run. -/
theorem firstIs_edges_retained {o z : Site 2} (hoz : o ≠ z) (L : List (Site 2))
    (p : (lattice 2).Walk o z) (ξ : ℕ → WalkDriver) (hf : ξ 0 ∈ FirstIs p) (out : SamplerState)
    (hout : samplerRun (rootSampler z) (o :: L) ξ = some out) :
    ∀ e ∈ pathEdges p, e.val ∈ out.edges := by
  obtain ⟨T, hT, hβ⟩ := hf
  obtain ⟨S1, hS1, -, hedges⟩ := rootSampler_firstStep hoz (ξ 0) T hT
  have hrun : samplerRun S1 L (fun i => ξ (i + 1)) = some out := by
    simpa only [samplerRun, hS1, Option.bind_some] using hout
  intro e he
  apply samplerRun_edges_subset hrun
  rw [hedges, hβ]
  exact mem_branchEdges_support p e.val ((mem_pathEdges p e).mp he)

/-- Comparison with the uniform spanning tree: the first branch is retained. -/
theorem wilsonRows_firstIs_inter_le {o z : Site 2} (hoz : o ≠ z) (L : List (Site 2))
    (E : Finset LatticeEdge) (hE : ∀ e ∈ E, ∀ x ∈ e.val, x ∈ L) (pE : LatticeEdge → Bool)
    (p : (lattice 2).Walk o z) :
    wilsonRows ({ξ : ℕ → WalkDriver | ξ 0 ∈ FirstIs p} ∩ rootSamplerEvent z (o :: L) E pE) ≤
      (squareLatticeUST : Measure EdgeField) (Present p ∩ {ω | ∀ e ∈ E, ω e = pE e}) := by
  by_cases hcons : ∀ e ∈ E, e ∈ pathEdges p → pE e = true
  · let P : LatticeEdge → Bool := fun e => if e ∈ pathEdges p then true else pE e
    let M := (o :: L) ++ p.support
    have hset : Present p ∩ {ω | ∀ e ∈ E, ω e = pE e} =
        {ω | ∀ e ∈ E ∪ pathEdges p, ω e = P e} := by
      ext ω
      simp only [Present, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union, P]
      constructor
      · rintro ⟨h1, h2⟩ e he
        by_cases hp : e ∈ pathEdges p
        · rw [if_pos hp]
          exact h1 e hp
        · rw [if_neg hp]
          exact h2 e (he.resolve_right hp)
      · intro h
        refine ⟨fun e he => by simpa [he] using h e (Or.inr he), fun e he => ?_⟩
        have h' := h e (Or.inl he)
        by_cases hp : e ∈ pathEdges p
        · rw [if_pos hp] at h'
          rw [h', hcons e he hp]
        · rwa [if_neg hp] at h'
    have hM : ∀ e ∈ E ∪ pathEdges p, ∀ x ∈ e.val, x ∈ M := by
      intro e he x hx
      rcases Finset.mem_union.mp he with he | he
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ (hE e he x hx))
      · exact List.mem_append_right _ (mem_support_of_mem_edge p ((mem_pathEdges p e).mp he) hx)
    rw [hset, squareLatticeUST_edgeEvent_eq_rootSampler_list z M _ hM P]
    apply measure_mono_ae
    filter_upwards [wilsonRows_ae_hits_all] with ξ hhit
    rintro ⟨hf, out, hout, hpat⟩
    have hz : z ∈ out.covered :=
      samplerRun_covered_subset hout (by rw [rootSampler_covered]; rfl)
    obtain ⟨out2, hout2⟩ := exists_samplerRun_of_hits out p.support
      (fun i => ξ (i + (o :: L).length)) z hz (fun i x => hhit _ x z)
    refine ⟨out2, by rw [samplerRun_append, hout, Option.bind_some, hout2], fun e he => ?_⟩
    have hret := firstIs_edges_retained hoz L p ξ hf out hout
    simp only [P]
    by_cases hp : e ∈ pathEdges p
    · rw [if_pos hp]
      exact decide_eq_true (samplerRun_edges_subset hout2 (hret e hp))
    · rw [if_neg hp]
      have heE : e ∈ E := (Finset.mem_union.mp he).resolve_right hp
      have hcov := samplerRun_edge_of_covered hout2 e.val (fun v hv =>
        samplerRun_query_mem_covered hout v (List.mem_cons_of_mem _ (hE e heE v hv)))
      rw [← hpat e heE]
      simp only [hcov]
  · simp only [not_forall, exists_prop] at hcons
    obtain ⟨e, heE, hep, hfalse⟩ := hcons
    have hempty : {ξ : ℕ → WalkDriver | ξ 0 ∈ FirstIs p} ∩ rootSamplerEvent z (o :: L) E pE = ∅ := by
      ext ξ
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hf, out, hout, hpat⟩
      have h := hpat e heE
      rw [decide_eq_true (firstIs_edges_retained hoz L p ξ hf out hout e hep)] at h
      exact hfalse h.symm
    rw [hempty, measure_empty]
    exact bot_le

theorem eq_of_le_of_tsum_eq {ι : Type*} {a b : ι → ℝ≥0∞} (hab : ∀ i, a i ≤ b i)
    (hs : ∑' i, a i = ∑' i, b i) (hfin : ∑' i, a i ≠ ∞) (i : ι) : a i = b i := by
  have h1 : ∑' j, b j = ∑' j, a j + ∑' j, (b j - a j) := by
    rw [← ENNReal.tsum_add]
    congr 1
    funext j
    rw [add_tsub_cancel_of_le (hab j)]
  have h2 : ∑' j, (b j - a j) = 0 := by
    rw [← hs] at h1
    exact ((ENNReal.add_right_inj hfin).mp (h1.symm.trans (add_zero _).symm))
  exact le_antisymm (hab i) (tsub_eq_zero_iff_le.mp (ENNReal.tsum_eq_zero.mp h2 i))

/-- Conditionally on the uniform spanning tree path from `o` to `z`, the later walks of
Wilson's algorithm are stopped on it: the joint law factorizes. -/
theorem ust_present_inter_eq {o z : Site 2} (hoz : o ≠ z) (L : List (Site 2))
    (E : Finset LatticeEdge) (hE : ∀ e ∈ E, ∀ x ∈ e.val, x ∈ L) (pE : LatticeEdge → Bool)
    (p : LPath o z) :
    (squareLatticeUST : Measure EdgeField) (Present p.val ∩ {ω | ∀ e ∈ E, ω e = pE e}) =
      walkLaw (FirstIs p.val) * wilsonRows (tailEvent o z L E pE p.val) := by
  let H := rootSamplerEvent z (o :: L) E pE
  let A := {ω : EdgeField | ∀ e ∈ E, ω e = pE e}
  let a : LPath o z → ℝ≥0∞ := fun q => wilsonRows ({ξ : ℕ → WalkDriver | ξ 0 ∈ FirstIs q.val} ∩ H)
  let b : LPath o z → ℝ≥0∞ := fun q => (squareLatticeUST : Measure EdgeField) (Present q.val ∩ A)
  have hab : ∀ q, a q ≤ b q := fun q => wilsonRows_firstIs_inter_le hoz L E hE pE q.val
  have hHA : wilsonRows H = (squareLatticeUST : Measure EdgeField) A :=
    (squareLatticeUST_edgeEvent_eq_rootSampler_list z (o :: L) E
      (fun e he x hx => List.mem_cons_of_mem _ (hE e he x hx)) pE).symm
  have hmeasA : ∀ q : LPath o z,
      MeasurableSet ({ξ : ℕ → WalkDriver | ξ 0 ∈ FirstIs q.val} ∩ H) := fun q =>
    ((measurableSet_firstIs q.val).preimage (measurable_pi_apply 0)).inter
      (measurableSet_rootSamplerEvent z _ E pE)
  have hsa : ∑' q, a q = wilsonRows H := by
    have hU := measure_iUnion (μ := wilsonRows)
      (f := fun q : LPath o z => {ξ : ℕ → WalkDriver | ξ 0 ∈ FirstIs q.val} ∩ H)
      (fun q q' hqq' => Disjoint.mono Set.inter_subset_left
        Set.inter_subset_left ((firstIs_disjoint hqq').preimage (fun ξ : ℕ → WalkDriver => ξ 0)))
      hmeasA
    rw [show (∑' q, a q) = ∑' q : LPath o z,
      wilsonRows ({ξ : ℕ → WalkDriver | ξ 0 ∈ FirstIs q.val} ∩ H) from rfl, ← hU]
    apply measure_congr
    filter_upwards [wilsonRows_ae_hits_all] with ξ hhit
    apply propext
    show ξ ∈ (⋃ q : LPath o z, {ξ : ℕ → WalkDriver | ξ 0 ∈ FirstIs q.val} ∩ H) ↔ ξ ∈ H
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, -, hH⟩
      exact hH
    · intro hH
      obtain ⟨n, hn⟩ := hhit 0 o z
      have hT : ∃ T, hitTime {z} o (ξ 0) = some T := by
        unfold hitTime
        rw [dif_pos ⟨n, hn⟩]
        exact ⟨_, rfl⟩
      obtain ⟨T, hT⟩ := hT
      obtain ⟨q, hq⟩ := exists_firstIs (ξ 0) T hT
      exact ⟨q, hq, hH⟩
  have htree : MeasurableSet {ω : EdgeField | IsTree ω} :=
    FiniteAvalanches.Trees.Lattice.BarlowMasson.measurableSet_isTree
  have hconull : (squareLatticeUST : Measure EdgeField) {ω : EdgeField | IsTree ω}ᶜ = 0 := by
    have h := squareLatticeUST_ae_tree_oneEnded
    rw [ae_iff] at h
    exact measure_mono_null (fun ω (hω : ω ∈ {ω : EdgeField | IsTree ω}ᶜ) =>
      (show ω ∈ {a : EdgeField | ¬(IsTree a ∧ OneEnded a)} from fun hboth => hω hboth.1)) h
  have hsb : ∑' q, b q = (squareLatticeUST : Measure EdgeField) A := by
    have hb : ∀ q : LPath o z, b q = (squareLatticeUST : Measure EdgeField)
        (Present q.val ∩ A ∩ {ω | IsTree ω}) := fun q =>
      (measure_inter_conull hconull).symm
    rw [show (∑' q, b q) = ∑' q : LPath o z, (squareLatticeUST : Measure EdgeField)
      (Present q.val ∩ A ∩ {ω | IsTree ω}) from tsum_congr hb]
    rw [← measure_iUnion]
    · rw [← measure_inter_conull (s := A) hconull]
      congr 1
      ext ω
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨q, ⟨-, hA⟩, hT⟩
        exact ⟨hA, hT⟩
      · rintro ⟨hA, hT⟩
        obtain ⟨q, hq, -⟩ := existsUnique_present hT o z
        exact ⟨q, ⟨hq, hA⟩, hT⟩
    · intro q q' hqq'
      rw [Function.onFun, Set.disjoint_left]
      rintro ω ⟨⟨hq, -⟩, hT⟩ ⟨⟨hq', -⟩, -⟩
      exact hqq' ((existsUnique_present hT o z).unique hq hq')
    · intro q
      exact ((measurableSet_present q.val).inter (measurableSet_edgePattern E pE)).inter htree
  have hfin : ∑' q, a q ≠ ∞ := by
    rw [hsa]
    exact measure_ne_top _ _
  have h := eq_of_le_of_tsum_eq hab (by rw [hsa, hsb, hHA]) hfin p
  exact h.symm.trans (wilsonRows_firstIs_inter hoz L E pE p.val)

end

end FiniteAvalanches.Wilson.Lattice
