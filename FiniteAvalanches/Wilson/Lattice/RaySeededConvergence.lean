import FiniteAvalanches.Wilson.Lattice.RaySeededLimit
import FiniteAvalanches.Wilson.Lattice.RootContinuity

/-! The distant-root limit of Wilson's algorithm with the walk from `o` first.

For every one-ended spanning tree, the tree path from `o` to the distant site eventually
contains each vertex of the ray from `o`, eventually avoids each vertex off the ray, and
eventually has the same edges as the ray on every finite set. With the same rows, the
later walks stopped on the path therefore eventually make the same hits as the walks
stopped on the ray (root continuity of the sampler). Bounded convergence then identifies
every ray-prefix and finite edge pattern probability of the uniform spanning tree with
the probability that Wilson's algorithm rooted at the ray reveals the pattern. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.RaySeeded

open LatticeProb MeasureTheory Filter FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice
open TreeMeasurability11 FiniteAvalanches.Trees.Lattice.BarlowMasson
open scoped Classical ENNReal Topology

attribute [local instance] rayMeasurableSpace

noncomputable section

theorem seed_vertex (o : Site 2) (T : EndedTree) :
    (seed o T).vertex = infiniteRay T.val T.property.1
      (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) o := rfl

theorem eventually_branchPath_eq (o : Site 2) (T : EndedTree) (K : ℕ) :
    ∀ᶠ n in atTop, branchPath o n T = (List.range (K + 1)).map (seed o T).vertex ++
      (treePath T.val T.property.1 ((seed o T).vertex K) (distantSite o n)).support.tail := by
  filter_upwards [eventually_distantSite_not_mem o (rayPast_finite T.val T.property.1
    (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2)
    ((seed o T).vertex K))] with n hn
  exact treePath_support_eq_of_not_mem_rayPast T.val T.property.1 _ o (distantSite o n) K hn

theorem getElem_map_range_append (f : ℕ → Site 2) (K : ℕ) (t : List (Site 2)) {i : ℕ}
    (hi : i < K + 1) (h : i < ((List.range (K + 1)).map f ++ t).length) :
    ((List.range (K + 1)).map f ++ t)[i] = f i := by
  rw [List.getElem_append_left (by simpa using hi)]
  simp

theorem eventually_prefix (o : Site 2) (T : EndedTree) (k : ℕ) :
    ∀ᶠ n in atTop, prefixOf k (branchPath o n T) = rayPrefix k (seed o T) := by
  filter_upwards [eventually_branchPath_eq o T k] with n hn
  funext i
  have hi : (i : ℕ) < ((List.range (k + 1)).map (seed o T).vertex ++
      (treePath T.val T.property.1 ((seed o T).vertex k) (distantSite o n)).support.tail).length := by
    simp only [List.length_append, List.length_map, List.length_range]
    omega
  simp only [prefixOf, rayPrefix, hn, List.getD_eq_getElem _ _ hi]
  exact getElem_map_range_append _ k _ i.isLt hi

theorem eventually_mem_branchPath (o : Site 2) (T : EndedTree) (v : Site 2) :
    ∀ᶠ n in atTop, (v ∈ branchPath o n T ↔ v ∈ (seed o T).vertices) := by
  by_cases hv : v ∈ (seed o T).vertices
  · obtain ⟨i, rfl⟩ := hv
    filter_upwards [eventually_branchPath_eq o T i] with n hn
    refine iff_of_true ?_ ⟨i, rfl⟩
    rw [hn]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_self i), rfl⟩)
  · filter_upwards [eventually_distantSite_not_mem o (rayPast_finite T.val T.property.1
      (unique_infinite_components_of_oneEnded T.val T.property.1 T.property.2) v)] with n hn
    refine iff_of_false (fun h => hn ?_) hv
    exact mem_rayPast_of_mem_treePath T.val T.property.1 _ o (distantSite o n) v h hv

theorem mem_branchEdges_iff (l : List (Site 2)) (s : Sym2 (Site 2)) :
    s ∈ branchEdges l ↔ ∃ (t : ℕ) (h : t + 1 < l.length), s = s(l[t], l[t + 1]) := by
  simp only [branchEdges, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hq
    simp only [List.length_zip, List.length_tail] at ht
    refine ⟨t, by omega, ?_⟩
    simp [List.getElem_zip, List.getElem_tail]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(l[t], l[t + 1]), List.mem_iff_getElem.mpr ⟨t, by simp; omega, ?_⟩, rfl⟩
    simp [List.getElem_zip, List.getElem_tail]

theorem mem_of_mem_branchEdges {l : List (Site 2)} {a b : Site 2}
    (h : s(a, b) ∈ branchEdges l) : a ∈ l ∧ b ∈ l := by
  obtain ⟨t, ht, heq⟩ := (mem_branchEdges_iff l _).mp h
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨List.getElem_mem _, List.getElem_mem _⟩
  · exact ⟨List.getElem_mem _, List.getElem_mem _⟩

theorem branchPath_nodup (o : Site 2) (n : ℕ) (T : EndedTree) : (branchPath o n T).Nodup :=
  (FiniteAvalanches.Trees.RootedPaths.path_isPath T.property.1 _ _).support_nodup

theorem eventually_mem_branchEdges (o : Site 2) (T : EndedTree) (s : Sym2 (Site 2)) :
    ∀ᶠ n in atTop, (s ∈ branchEdges (branchPath o n T) ↔ s ∈ seedEdges (seed o T)) := by
  by_cases hs : s ∈ seedEdges (seed o T)
  · obtain ⟨i, rfl⟩ := hs
    filter_upwards [eventually_branchPath_eq o T (i + 1)] with n hn
    refine iff_of_true ?_ ⟨i, rfl⟩
    rw [hn, mem_branchEdges_iff]
    refine ⟨i, by simp; omega, ?_⟩
    rw [getElem_map_range_append _ _ _ (by omega), getElem_map_range_append _ _ _ (by omega)]
  · induction s using Sym2.ind with
    | h a b =>
    by_cases ha : a ∈ (seed o T).vertices
    · by_cases hb : b ∈ (seed o T).vertices
      · obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        filter_upwards [eventually_branchPath_eq o T (i + j + 1)] with n hn
        refine iff_of_false (fun h => hs ?_) hs
        have hnd := branchPath_nodup o n T
        rw [hn] at h hnd
        obtain ⟨t, ht, heq⟩ := (mem_branchEdges_iff _ _).mp h
        have hl : ∀ m (hm : m < i + j + 1 + 1)
            (hm' : m < ((List.range (i + j + 1 + 1)).map (seed o T).vertex ++
            (treePath T.val T.property.1 ((seed o T).vertex (i + j + 1))
              (distantSite o n)).support.tail).length),
            ((List.range (i + j + 1 + 1)).map (seed o T).vertex ++
            (treePath T.val T.property.1 ((seed o T).vertex (i + j + 1))
              (distantSite o n)).support.tail)[m] = (seed o T).vertex m :=
          fun m hm hm' => getElem_map_range_append _ _ _ hm hm'
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hti : i = t :=
            (List.Nodup.getElem_inj_iff hnd).mp ((hl i (by omega) (by simp; omega)).trans h1)
          subst hti
          rw [hl (i + 1) (by omega) ht] at h2
          exact ⟨i, by rw [h2]⟩
        · have htj : j = t :=
            (List.Nodup.getElem_inj_iff hnd).mp ((hl j (by omega) (by simp; omega)).trans h2)
          subst htj
          rw [hl (j + 1) (by omega) ht] at h1
          exact ⟨j, by rw [h1]; exact Sym2.eq_swap⟩
      · filter_upwards [eventually_mem_branchPath o T b] with n hn
        exact iff_of_false (fun h => hb (hn.mp (mem_of_mem_branchEdges h).2)) hs
    · filter_upwards [eventually_mem_branchPath o T a] with n hn
      exact iff_of_false (fun h => ha (hn.mp (mem_of_mem_branchEdges h).1)) hs

/-- Root continuity along the tree paths toward distant sites. -/
theorem tendsto_pathTail (o : Site 2) (L : List (Site 2)) (E : Finset LatticeEdge)
    (pE : LatticeEdge → Bool) (T : EndedTree) :
    Tendsto (fun n => pathTail L E pE (branchPath o n T)) atTop
      (𝓝 (seedTail L E pE (seed o T))) := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (measurableSet_samplerRun_event _ L _) (fun n => measurableSet_samplerRun_event _ L _)
  filter_upwards [wilsonRows_ae_hits_all] with ξ hhit
  have ho : o ∈ (coverState (seed o T).vertices).covered := by
    rw [coverState_covered]
    exact ⟨0, rfl⟩
  obtain ⟨out, hout⟩ := exists_samplerRun_of_hits _ L ξ o ho (fun i x => hhit i x o)
  have hc : ∀ v, ∀ᶠ n in atTop, (coverState {v | v ∈ branchPath o n T}).colors v =
      (coverState (seed o T).vertices).colors v := by
    intro v
    filter_upwards [eventually_mem_branchPath o T v] with n hn
    simp only [coverState, Set.mem_setOf_eq, hn]
  obtain ⟨outj, hrun, -, hedges, -⟩ := samplerRun_local_colors
    (fun n => coverState {v | v ∈ branchPath o n T}) _ out hc
    (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun _ => rfl) L ξ hout
  have hE : ∀ᶠ n in atTop, ∀ e ∈ E,
      (e.val ∈ branchEdges (branchPath o n T) ↔ e.val ∈ seedEdges (seed o T)) :=
    (Filter.eventually_all_finset E).mpr fun e _ => eventually_mem_branchEdges o T e.val
  filter_upwards [hrun, hedges, hE] with n hr he hb
  have key : ∀ e ∈ E, (e.val ∈ (outj n).edges ∨ e.val ∈ branchEdges (branchPath o n T)) ↔
      (e.val ∈ out.edges ∨ e.val ∈ seedEdges (seed o T)) := fun e he' => by
    rw [he, hb e he']
  constructor
  · rintro ⟨out', h', hp⟩
    rw [hr] at h'
    cases h'
    exact ⟨out, hout, fun e he' => by
      rw [← hp e he']
      exact decide_eq_decide.mpr (key e he').symm⟩
  · rintro ⟨out', h', hp⟩
    rw [hout] at h'
    cases h'
    exact ⟨outj n, hr, fun e he' => by
      rw [← hp e he']
      exact decide_eq_decide.mpr (key e he')⟩

theorem measurable_rayPrefix_seed (o : Site 2) (k : ℕ) :
    Measurable (fun T : EndedTree => rayPrefix k (seed o T)) :=
  measurable_pi_lambda _ fun i => measurable_rayVertex o i

/-- Ray-prefix and finite edge pattern probabilities of the uniform spanning tree are those
of Wilson's algorithm rooted at the ray from `o`. -/
theorem ray_seeded_cylinder (o : Site 2) (L : List (Site 2)) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ x ∈ e.val, x ∈ L) (pE : LatticeEdge → Bool) (k : ℕ)
    (R : Set (Fin (k + 1) → Site 2)) :
    endedUST {T | rayPrefix k (seed o T) ∈ R ∧ T.val ∈ {ω | ∀ e ∈ E, ω e = pE e}} =
      ∫⁻ T, {T : EndedTree | rayPrefix k (seed o T) ∈ R}.indicator
        (fun T => seedTail L E pE (seed o T)) T ∂endedUST := by
  let A := {ω : EdgeField | ∀ e ∈ E, ω e = pE e}
  have hA : MeasurableSet A := measurableSet_edgePattern E pE
  have hR : MeasurableSet R := (Set.to_countable R).measurableSet
  have h1 : Tendsto (fun n => endedUST {T | prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ A})
      atTop (𝓝 (endedUST {T | rayPrefix k (seed o T) ∈ R ∧ T.val ∈ A})) := by
    apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      (((measurable_rayPrefix_seed o k) hR).inter (measurable_subtype_coe hA))
      (fun n => (measurableSet_branchPath_pred o n (fun l => prefixOf k l ∈ R)).inter
        (measurable_subtype_coe hA))
    refine ae_of_all _ fun T => ?_
    filter_upwards [eventually_prefix o T k] with n hn
    show (prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ A) ↔ (rayPrefix k (seed o T) ∈ R ∧ T.val ∈ A)
    rw [hn]
  let F : ℕ → EndedTree → ℝ≥0∞ := fun n T =>
    {T : EndedTree | prefixOf k (branchPath o n T) ∈ R}.indicator
      (fun T => pathTail L E pE (branchPath o n T)) T
  have hF : ∀ n, Measurable (F n) := by
    intro n
    have he : F n = fun T => (fun l => if prefixOf k l ∈ R then pathTail L E pE l else 0)
        (branchPath o n T) := by
      funext T
      simp only [F, Set.indicator, Set.mem_setOf_eq]
    rw [he]
    exact measurable_branchPath_comp o n
      (fun l => if prefixOf k l ∈ R then pathTail L E pE l else 0)
  have h2 : Tendsto (fun n => ∫⁻ T, F n T ∂endedUST) atTop
      (𝓝 (∫⁻ T, {T : EndedTree | rayPrefix k (seed o T) ∈ R}.indicator
        (fun T => seedTail L E pE (seed o T)) T ∂endedUST)) := by
    apply tendsto_lintegral_of_dominated_convergence (fun _ => 1) hF
    · intro n
      refine ae_of_all _ fun T => ?_
      simp only [F, Set.indicator]
      split_ifs
      · exact prob_le_one
      · exact zero_le_one
    · simp
    · refine ae_of_all _ fun T => ?_
      by_cases hT : rayPrefix k (seed o T) ∈ R
      · simp only [Set.indicator, Set.mem_setOf_eq, hT, if_true]
        apply (tendsto_pathTail o L E pE T).congr'
        filter_upwards [eventually_prefix o T k] with n hn
        simp only [F, Set.indicator, Set.mem_setOf_eq, hn, hT, if_true]
      · simp only [Set.indicator, Set.mem_setOf_eq, hT, if_false]
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_prefix o T k] with n hn
        simp only [F, Set.indicator, Set.mem_setOf_eq, hn, hT, if_false]
  have h3 : ∀ n, endedUST {T | prefixOf k (branchPath o n T) ∈ R ∧ T.val ∈ A} =
      ∫⁻ T, F n T ∂endedUST := fun n => branch_identity o L E hE pE k R n
  exact tendsto_nhds_unique h1 (h2.congr fun n => (h3 n).symm)

end

end FiniteAvalanches.Wilson.Lattice.RaySeeded
