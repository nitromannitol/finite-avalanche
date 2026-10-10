import FiniteAvalanches.Trees.ForestColorMonotonicity
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.ForestProjectionConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Electrical

/-- Two parallel exits to the zero root, one exit to the one root, and one root-root copy. -/
def graph : Multigraph (Fin 3) (Fin 4) where
  left e := if e = 2 then 2 else 0
  right e := if e = 3 then 2 else 1
  loopless e := by fin_cases e <;> decide

def roots : Finset (Fin 3) := {0, 2}

theorem roots_nonempty : roots.Nonempty := ⟨0, by simp [roots]⟩

theorem graph_connected : (supportGraph graph.left graph.right).Preconnected := by
  have hr (x : Fin 3) : (supportGraph graph.left graph.right).Reachable x 1 := by
    fin_cases x
    · apply SimpleGraph.Adj.reachable
      exact ⟨by decide, 0, Or.inl ⟨by simp [graph], by simp [graph]⟩⟩
    · exact .rfl
    · apply SimpleGraph.Adj.reachable
      exact ⟨by decide, 2, Or.inl ⟨by simp [graph], by simp [graph]⟩⟩
  exact fun x y => (hr x).trans (hr y).symm

attribute [-instance] Unique.fintype

instance freeVertexUnique : Unique {v : Fin 3 // v ∉ roots} where
  default := ⟨1, by simp [roots]⟩
  uniq v := by
    apply Subtype.ext
    have hv := v.property
    rcases v with ⟨v, hv⟩
    fin_cases v <;> simp_all [roots]

local instance freeDecidableEq : DecidableEq {v : Fin 3 // v ∉ roots} :=
  @Subtype.instDecidableEq (Fin 3) (fun v => v ∉ roots) (Classical.decEq _)

local instance freeFintype : Fintype {v : Fin 3 // v ∉ roots} :=
  @Subtype.fintype (Fin 3) (fun v => v ∉ roots)
    (fun v => @instDecidableNot (v ∈ roots)
      (@Finset.decidableMem (Fin 3) (Classical.decEq _) v roots)) (inferInstance)

@[simp] theorem free_default_val : (default : {v : Fin 3 // v ∉ roots}).val = 1 := rfl

theorem gram_det_three : (graph.rootGram roots).det = 3 := by
  rw [Matrix.det_unique]
  norm_num [rootGram, Matrix.mul_apply, Matrix.transpose_apply, rootIncidence_apply,
    graph, roots, Fin.sum_univ_succ, free_default_val, Fin.ext_iff]

theorem each_exit_minor (e : Fin 4) (he : e ≠ 3) :
    ((graph.rootIncidence roots).submatrix (fun _ => e) id).det ^ 2 = 1 := by
  rw [Matrix.det_unique]
  fin_cases e <;> norm_num [Matrix.submatrix_apply, rootIncidence_apply, graph,
    roots, free_default_val, Fin.ext_iff] at *

theorem root_root_minor_zero :
    ((graph.rootIncidence roots).submatrix (fun _ => (3 : Fin 4)) id).det = 0 := by
  rw [Matrix.det_unique]
  norm_num [Matrix.submatrix_apply, rootIncidence_apply, graph, roots, free_default_val, Fin.ext_iff]

theorem reaches_empty_iff {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (x y : V) : G.reaches ∅ x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ h _ => obtain ⟨e, he, _⟩ := h; simp at he
  · rintro rfl
    exact .refl

theorem reaches_singleton_iff {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (e : E) (x y : V) :
    G.reaches {e} x y ↔ x = y ∨
      ((x = G.left e ∨ x = G.right e) ∧ (y = G.left e ∨ y = G.right e)) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ h ih =>
      obtain ⟨f, hf, h⟩ := h
      have hf' : f = e := Finset.mem_singleton.mp hf
      subst f
      rcases h with h | h <;> rcases ih with ih | ih
      · exact Or.inr ⟨Or.inl (ih.trans h.1.symm), Or.inr h.2.symm⟩
      · exact Or.inr ⟨ih.1, Or.inr h.2.symm⟩
      · exact Or.inr ⟨Or.inr (ih.trans h.1.symm), Or.inl h.2.symm⟩
      · exact Or.inr ⟨ih.1, Or.inl h.2.symm⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · exact .refl
    · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact .refl
      · exact .single ⟨e, Finset.mem_singleton_self _, Or.inl ⟨rfl, rfl⟩⟩
      · exact .single ⟨e, Finset.mem_singleton_self _, Or.inr ⟨rfl, rfl⟩⟩
      · exact .refl

theorem singleton_exit_rooted (e : Fin 4) (he : e ≠ 3) :
    graph.is_rooted_forest (roots : Set (Fin 3)) {e} := by
  fin_cases e <;>
    simp [is_rooted_forest, is_forest, reaches_empty_iff, reaches_singleton_iff,
      roots, graph, Fin.forall_fin_succ] at *

/-- The two equal incidence rows belong to different valid original copied forests. -/
theorem parallel_forests_distinct :
    (⟨{0}, singleton_exit_rooted 0 (by decide)⟩ : graph.RootedForest (roots : Set (Fin 3))) ≠
      ⟨{1}, singleton_exit_rooted 1 (by decide)⟩ := by
  intro h
  have hh : ({0} : Finset (Fin 4)) = {1} := congrArg Subtype.val h
  have hm : (0 : Fin 4) ∈ ({1} : Finset (Fin 4)) := hh ▸ Finset.mem_singleton_self _
  simp at hm

/-- The mixed roots retain their original labels after selecting a root exit. -/
theorem singleton_exit_one_color (e : Fin 4) (he : e ≠ 3) :
    (1 : Fin 3) ∈ graph.oneVertices {e} ({2} : Set (Fin 3)) ↔ e = 2 := by
  simp only [oneVertices, Set.mem_setOf_eq, Set.mem_singleton_iff, exists_eq_left,
    reaches_singleton_iff]
  have h12 : (1 : Fin 3) ≠ 2 := by intro h; have hv := congrArg Fin.val h; omega
  have h20 : (2 : Fin 3) ≠ 0 := by intro h; have hv := congrArg Fin.val h; omega
  have h21 : (2 : Fin 3) ≠ 1 := h12.symm
  by_cases h2 : e = 2
  · subst e
    have h23 : (2 : Fin 4) ≠ 3 := by intro h; have hv := congrArg Fin.val h; omega
    have hl : graph.left 2 = 2 := by simp only [graph, if_true]
    have hr : graph.right 2 = 1 := by simp only [graph, if_neg h23]
    rw [hl, hr]
    exact ⟨fun _ => rfl, fun _ => Or.inr ⟨Or.inr rfl, Or.inl rfl⟩⟩
  · have hl : graph.left e = 0 := by simp only [graph, if_neg h2]
    have hr : graph.right e = 1 := by simp only [graph, if_neg he]
    rw [hl, hr]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact (h12 h).elim
      · exact h.elim (fun h => (h20 h).elim) (fun h => (h21 h).elim)
    · intro h
      exact (h2 h).elim

theorem rooted_forest_classification (F : Finset (Fin 4)) :
    graph.is_rooted_forest (roots : Set (Fin 3)) F ↔ F = {0} ∨ F = {1} ∨ F = {2} := by
  constructor
  · intro hF
    have h3 : (3 : Fin 4) ∉ F := by
      intro h3
      obtain ⟨r, _, _, hu⟩ := hF.2 0
      have h0r : (0 : Fin 3) = r := hu 0 (by simp [roots]) .refl
      have h2r : (2 : Fin 3) = r := hu 2 (by simp [roots])
        (.single ⟨3, h3, Or.inl ⟨by simp [graph], by simp [graph]⟩⟩)
      have h := h0r.trans h2r.symm
      norm_num [Fin.ext_iff] at h
    have h01 : ¬((0 : Fin 4) ∈ F ∧ (1 : Fin 4) ∈ F) := by
      rintro ⟨h0, h1⟩
      apply hF.1 0 h0
      exact .single ⟨1, (@Finset.mem_erase (Fin 4) (Classical.decEq _) 1 0 F).mpr
        ⟨by decide, h1⟩,
        Or.inl ⟨by simp [graph], by simp [graph]⟩⟩
    have hmixed (e : Fin 4) (he2 : e ≠ 2) (he3 : e ≠ 3) :
        ¬(e ∈ F ∧ (2 : Fin 4) ∈ F) := by
      rintro ⟨he, h2⟩
      obtain ⟨r, _, _, hu⟩ := hF.2 1
      have h0r : (0 : Fin 3) = r := hu 0 (by simp [roots])
        (.single ⟨e, he, Or.inr ⟨by simp [graph, he3], by simp [graph, he2]⟩⟩)
      have h2r : (2 : Fin 3) = r := hu 2 (by simp [roots])
        (.single ⟨2, h2, Or.inr ⟨by simp [graph], by simp [graph]⟩⟩)
      have h := h0r.trans h2r.symm
      norm_num [Fin.ext_iff] at h
    have h02 := hmixed 0 (by norm_num [Fin.ext_iff]) (by norm_num [Fin.ext_iff])
    have h12 := hmixed 1 (by norm_num [Fin.ext_iff]) (by norm_num [Fin.ext_iff])
    have hnonempty : F ≠ ∅ := by
      intro hempty
      obtain ⟨r, hr, hreach, _⟩ := hF.2 1
      rw [hempty, reaches_empty_iff] at hreach
      rw [← hreach] at hr
      norm_num [roots, Fin.ext_iff] at hr
    by_cases h0 : (0 : Fin 4) ∈ F
    · left
      ext e
      fin_cases e <;> simp_all [Fin.ext_iff]
    · right
      by_cases h1 : (1 : Fin 4) ∈ F
      · left
        ext e
        fin_cases e <;> simp_all [Fin.ext_iff]
      · right
        have h2 : (2 : Fin 4) ∈ F := by
          by_contra h2
          apply hnonempty
          ext e
          fin_cases e <;> simp_all
        ext e
        fin_cases e <;> simp_all [Fin.ext_iff]
  · rintro (rfl | rfl | rfl)
    · exact singleton_exit_rooted 0 (by norm_num [Fin.ext_iff])
    · exact singleton_exit_rooted 1 (by norm_num [Fin.ext_iff])
    · exact singleton_exit_rooted 2 (by norm_num [Fin.ext_iff])

/-- The normalizer is the actual number of original rooted copied forests. -/
theorem forest_count_three : Fintype.card (graph.RootedForest (roots : Set (Fin 3))) = 3 := by
  have h := Fintype.card_of_subtype (p := graph.is_rooted_forest (roots : Set (Fin 3)))
    ({{0}, {1}, {2}} : Finset (Finset (Fin 4)))
    (fun F => by simp [rooted_forest_classification])
  exact h

/-- The Gram determinant equals the actual original-forest count in the adversarial example. -/
theorem gram_det_eq_forest_count : (graph.rootGram roots).det =
    (Fintype.card (graph.RootedForest (roots : Set (Fin 3))) : ℝ) := by
  rw [gram_det_three, forest_count_three]
  norm_num

/-- The formula keeps the parallel zero exits and the mixed-color exit as three distinct outcomes. -/
theorem exit_projection_mass (e : Fin 4) (he : e ≠ 3) :
    ((graph.rootProjection roots roots_nonempty graph_connected).submatrix (fun _ => e)
      (fun _ : {v : Fin 3 // v ∉ roots} => e)).det = 1 / 3 := by
  have h := graph.rootProjection_minor_det roots roots_nonempty graph_connected (fun _ => e)
  rw [each_exit_minor e he, gram_det_three] at h
  convert h using 1

/-- An original root-to-root copy has zero probability in the projection formula. -/
theorem root_root_projection_mass_zero :
    ((graph.rootProjection roots roots_nonempty graph_connected).submatrix (fun _ => (3 : Fin 4))
      (fun _ : {v : Fin 3 // v ∉ roots} => (3 : Fin 4))).det = 0 := by
  have h := graph.rootProjection_minor_det roots roots_nonempty graph_connected (fun _ => (3 : Fin 4))
  rw [root_root_minor_zero] at h
  simpa using h

/-- Each original forest singleton gets its true uniform mass, not a renamed DPP law. -/
theorem projection_det_eq_uniform_forest_mass (e : Fin 4) (he : e ≠ 3) :
    ((graph.rootProjection roots roots_nonempty graph_connected).submatrix
      (fun _ : {v : Fin 3 // v ∉ roots} => e) (fun _ => e)).det =
      1 / (Fintype.card (graph.RootedForest (roots : Set (Fin 3))) : ℝ) := by
  rw [forest_count_three]
  exact exit_projection_mass e he

instance originalForestNonempty : Nonempty (graph.RootedForest (roots : Set (Fin 3))) :=
  ⟨⟨{0}, singleton_exit_rooted 0 (by decide)⟩⟩

/-- The actual uniform original-forest atom agrees with the projection minor. -/
theorem uniform_forest_atom_eq_projection (e : Fin 4) (he : e ≠ 3) :
    PMF.uniformOfFintype (graph.RootedForest (roots : Set (Fin 3)))
      ⟨{e}, singleton_exit_rooted e he⟩ =
      ENNReal.ofReal (((graph.rootProjection roots roots_nonempty graph_connected).submatrix
        (fun _ : {v : Fin 3 // v ∉ roots} => e) (fun _ => e)).det) := by
  rw [PMF.uniformOfFintype_apply, forest_count_three, exit_projection_mass e he]
  simp

end FiniteAvalanches.ForestProjectionConsumer

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.ForestDppAdversarialConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.ForestProjectionConsumer

theorem original_graph_connected : ∀ x y : Fin 3, graph.reaches Finset.univ x y := by
  have hr (x : Fin 3) : graph.reaches Finset.univ x 1 := by
    fin_cases x
    · exact .single ⟨0, Finset.mem_univ _, Or.inl ⟨by simp [graph], by simp [graph]⟩⟩
    · exact .refl
    · exact .single ⟨2, Finset.mem_univ _, Or.inl ⟨by simp [graph], by simp [graph]⟩⟩
  exact fun x y => (hr x).trans (graph.reaches_symm (hr y))

/-- Every inclusion event is identified for the actual original forest law, not only its atoms. -/
theorem all_original_forest_inclusion_laws (A : Finset (Fin 4)) :
    ∑ F : Finset (Fin 4), Set.indicator {F : Finset (Fin 4) | A ⊆ F}
      (graph.uniformRootedForestMass (roots : Set (Fin 3)) roots_nonempty original_graph_connected) F =
      (letI : DecidableEq (Fin 4) := Classical.decEq _
       ((graph.rootProjection roots roots_nonempty graph_connected).submatrix
        (Subtype.val : A → Fin 4) Subtype.val).det) :=
  graph.uniformRootedForestMass_inclusion_det roots roots_nonempty original_graph_connected A

/-- The atom probabilities still divide by the three original forests and retain parallel exits. -/
theorem original_exit_atom (e : Fin 4) (he : e ≠ 3) :
    graph.uniformRootedForestMass (roots : Set (Fin 3)) roots_nonempty original_graph_connected {e} =
      1 / 3 := by
  simp only [uniformRootedForestMass, if_pos (singleton_exit_rooted e he),
    Nat.card_eq_fintype_card, forest_count_three]
  norm_num

/-- A forbidden original root-root copy has zero joint-inclusion probability in every event. -/
theorem root_root_joint_inclusion_zero (A : Finset (Fin 4)) (h3 : 3 ∈ A) :
    ∑ F : Finset (Fin 4), Set.indicator {F : Finset (Fin 4) | A ⊆ F}
      (graph.uniformRootedForestMass (roots : Set (Fin 3)) roots_nonempty original_graph_connected) F = 0 := by
  apply Finset.sum_eq_zero
  intro F _
  by_cases hAF : A ⊆ F
  · have hnot : ¬graph.is_rooted_forest (roots : Set (Fin 3)) F := by
      intro hF
      have hf3 := hAF h3
      rcases (rooted_forest_classification F).mp hF with rfl | rfl | rfl <;> simp at hf3
    simp [Set.indicator, hAF, uniformRootedForestMass, hnot]
  · simp [Set.indicator, hAF]

theorem root_root_joint_minor_zero (A : Finset (Fin 4)) (h3 : 3 ∈ A) :
    (letI : DecidableEq (Fin 4) := Classical.decEq _
     ((graph.rootProjection roots roots_nonempty graph_connected).submatrix
      (Subtype.val : A → Fin 4) Subtype.val).det) = 0 := by
  rw [← all_original_forest_inclusion_laws]
  exact root_root_joint_inclusion_zero A h3

end FiniteAvalanches.ForestDppAdversarialConsumer

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.LyonsActualForestConsumer
open FiniteAvalanches.Trees FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.ForestProjectionConsumer
open FiniteAvalanches.ForestDppAdversarialConsumer
open FiniteAvalanches.External

/-- Add vertex one as a zero root on the actual mixed-color, parallel-copy graph. -/
theorem actual_add_zero (H : Set (Set (Fin 3)))
    (hH : ∀ U ∈ H, ∀ W : Set (Fin 3), U ⊆ W → W ∈ H) :
    (Nat.card {F : graph.RootedForest (({0, 1} : Set (Fin 3)) ∪ {2}) |
      graph.oneVertices F.val {2} ∈ H} : ℝ) /
      Nat.card (graph.RootedForest (({0, 1} : Set (Fin 3)) ∪ {2})) ≤
    (Nat.card {F : graph.RootedForest (({0} : Set (Fin 3)) ∪ {2}) |
      graph.oneVertices F.val {2} ∈ H} : ℝ) /
      Nat.card (graph.RootedForest (({0} : Set (Fin 3)) ∪ {2})) := by
  exact (graph.finite_forest_color_monotonicity original_graph_connected
    {0} {2} (by simp) (by simp) (by simp)).2
      {0, 1} (by simp) (by simp) H hH

/-- Remove vertex one as a one root while retaining the original one root at vertex two. -/
theorem actual_remove_one (H : Set (Set (Fin 3)))
    (hH : ∀ U ∈ H, ∀ W : Set (Fin 3), U ⊆ W → W ∈ H) :
    (Nat.card {F : graph.RootedForest (({0} : Set (Fin 3)) ∪ {2}) |
      graph.oneVertices F.val {2} ∈ H} : ℝ) /
      Nat.card (graph.RootedForest (({0} : Set (Fin 3)) ∪ {2})) ≤
    (Nat.card {F : graph.RootedForest (({0} : Set (Fin 3)) ∪ {1, 2}) |
      graph.oneVertices F.val {1, 2} ∈ H} : ℝ) /
      Nat.card (graph.RootedForest (({0} : Set (Fin 3)) ∪ {1, 2})) := by
  exact (graph.finite_forest_color_monotonicity original_graph_connected
    {0} {1, 2} (by simp) (by simp) (by simp)).1
      {2} (by simp) (by simp) H hH

/-- A joint inclusion coupling of two actual original uniform forest laws. -/
theorem actual_nested_forest_joint_coupling :
    ∃ q : Finset (Fin 4) → Finset (Fin 4) → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = graph.uniformRootedForestMass Set.univ
        ⟨0, Set.mem_univ _⟩ original_graph_connected S) ∧
      (∀ T, ∑ S, q S T = graph.uniformRootedForestMass (roots : Set (Fin 3))
        roots_nonempty original_graph_connected T) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, ¬ S ⊆ T → q S T = 0) := by
  letI : DecidableEq (Fin 4) := Classical.decEq _
  letI : Fintype {v : Fin 3 // v ∈ (Set.univ : Set (Fin 3))} :=
    @Subtype.fintype (Fin 3) (fun v => v ∈ (Set.univ : Set (Fin 3)))
      (fun v => Classical.propDecidable _) inferInstance
  letI : Fintype {v : Fin 3 // v ∈ (roots : Set (Fin 3))} :=
    @Subtype.fintype (Fin 3) (fun v => v ∈ (roots : Set (Fin 3)))
      (fun v => Classical.propDecidable _) inferInstance
  have hc := graph.supportGraph_preconnected_of_reaches original_graph_connected
  have ha : (Set.univ : Set (Fin 3)).Nonempty := ⟨0, Set.mem_univ _⟩
  have hr : (roots : Set (Fin 3)).Nonempty := roots_nonempty
  have hi := graph.range_rootProjection_antitone
    (Set.toFinset_subset_toFinset.mpr (Set.subset_univ (roots : Set (Fin 3))))
    (Set.toFinset_nonempty.mpr hr) (Set.toFinset_nonempty.mpr ha) hc
  exact (lyons_nestedProjectionDomination
    (graph.rootProjection Set.univ.toFinset (Set.toFinset_nonempty.mpr ha) hc)
    (graph.rootProjection (roots : Set (Fin 3)).toFinset (Set.toFinset_nonempty.mpr hr) hc)
    (graph.rootProjection_transpose Set.univ.toFinset (Set.toFinset_nonempty.mpr ha) hc)
    (graph.rootProjection_idempotent Set.univ.toFinset (Set.toFinset_nonempty.mpr ha) hc)
    (graph.rootProjection_transpose (roots : Set (Fin 3)).toFinset (Set.toFinset_nonempty.mpr hr) hc)
    (graph.rootProjection_idempotent (roots : Set (Fin 3)).toFinset (Set.toFinset_nonempty.mpr hr) hc) hi
    (graph.uniformRootedForestMass Set.univ ha original_graph_connected)
    (graph.uniformRootedForestMass (roots : Set (Fin 3)) hr original_graph_connected)
    (graph.uniformRootedForestMass_nonneg Set.univ ha original_graph_connected)
    (graph.uniformRootedForestMass_nonneg (roots : Set (Fin 3)) hr original_graph_connected)
    (graph.uniformRootedForestMass_set_inclusion_det Set.univ ha original_graph_connected)
    (graph.uniformRootedForestMass_set_inclusion_det (roots : Set (Fin 3)) hr original_graph_connected)).2

end FiniteAvalanches.LyonsActualForestConsumer
