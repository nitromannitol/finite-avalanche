module

public import FiniteAvalanches.Trees.Past

@[expose] public section

/-! Exact common-ancestor-past counting for ordinary copied-edge spanning trees. -/
open scoped Classical
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Trees.RootedPaths
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : Multigraph V E)

theorem existsUnique_component_path {C : Set V} (t : G.ComponentTree C) (x y : C) :
    ∃! p : (G.toSimple t.val).Walk x.val y.val, p.IsPath := by
  have hr := (G.toSimple_reachable t.val x.val y.val).mpr
    (t.property.2.2.1 x.val x.property y.val y.property)
  obtain ⟨p, hp⟩ := hr.exists_isPath
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact Subtype.mk.inj ((G.toSimple_isAcyclic t.property.2.2.2).path_unique ⟨q, hq⟩ ⟨p, hp⟩)

/-- The unique path in the actual induced component, retaining original vertices. -/
noncomputable def componentPath {C : Set V} (t : G.ComponentTree C) (x y : C) :
    (G.toSimple t.val).Walk x.val y.val := (G.existsUnique_component_path t x y).choose

theorem componentPath_isPath {C : Set V} (t : G.ComponentTree C) (x y : C) :
    (G.componentPath t x y).IsPath := (G.existsUnique_component_path t x y).choose_spec.1

/-- The actual minimal component subtree connecting S. The support premise is used to
construct both path endpoints, rather than silently discarding off-support marked vertices. -/
noncomputable def componentSpan {C : Set V} (t : G.ComponentTree C) (S : Set V)
    (hSC : S ⊆ C) : Set V :=
  {a | ∃ (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ S),
    a ∈ (G.componentPath t ⟨x, hSC hx⟩ ⟨y, hSC hy⟩).support}

theorem componentSpan_subset {C : Set V} (t : G.ComponentTree C) (S : Set V)
    (hSC : S ⊆ C) : G.componentSpan t S hSC ⊆ C := by
  rintro a ⟨x, hx, y, hy, ha⟩
  exact G.walk_mem_side (fun e he => iff_of_true (t.property.2.1 e he).1
    (t.property.2.1 e he).2) (G.componentPath t ⟨x, hSC hx⟩ ⟨y, hSC hy⟩) (hSC hx) a ha

theorem span_eq_componentSpan {C : Set V} (t : G.ComponentTree C) (u : G.SpanningTree)
    (S : Set V) (hSC : S ⊆ C) (htu : t.val ⊆ u.val) :
    G.span u S = G.componentSpan t S hSC := by
  have hle : G.toSimple t.val ≤ G.toSimple u.val := by
    intro x y h
    obtain ⟨e, he, h⟩ := h
    exact ⟨e, htu he, h⟩
  have heq (x y : C) :
      (path (G.toSimple_isTree u.property) x.val y.val).support =
        (G.componentPath t x y).support := by
    rw [path_eq _ ((G.componentPath t x y).mapLe hle)
      ((G.componentPath_isPath t x y).mapLe hle), SimpleGraph.Walk.support_mapLe_eq_support]
  ext a
  constructor
  · rintro ⟨x, hx, y, hy, ha⟩
    exact ⟨x, hx, y, hy, (heq ⟨x, hSC hx⟩ ⟨y, hSC hy⟩) ▸ ha⟩
  · rintro ⟨x, hx, y, hy, ha⟩
    exact ⟨x, hx, y, hy, (heq ⟨x, hSC hx⟩ ⟨y, hSC hy⟩).symm ▸ ha⟩

/-- An event in the ordinary tree carrier, with no marked edge and no forest-pair input.
The descendant expression is proved equal to the source past on this event below. -/
abbrev AncestorPastTree (C S : Set V) (r : V) (hS : S.Nonempty) (t : G.ComponentTree C) :=
  {u : G.SpanningTree // G.descendants u r (G.ancestorOf u r S hS) = C ∧
    G.internalEdges C u.val = t.val}

theorem ancestor_ne_root_of_event {C S : Set V} {r : V} (hr : r ∉ C) (hS : S.Nonempty)
    {t : G.ComponentTree C} (u : G.AncestorPastTree C S r hS t) :
    G.ancestorOf u.val r S hS ≠ r := by
  intro h
  have hm : r ∈ G.descendants u.val r (G.ancestorOf u.val r S hS) := by
    rw [h]
    exact ancestor_root _ r r
  rw [u.property.1] at hm
  exact hr hm

theorem event_iff_past {C S : Set V} {r : V} (hr : r ∉ C) (hS : S.Nonempty)
    (u : G.SpanningTree) :
    G.descendants u r (G.ancestorOf u r S hS) = C ↔
      ∃ hne : G.ancestorOf u r S hS ≠ r, G.past u r (G.ancestorOf u r S hS) hne = C := by
  constructor
  · intro h
    have hne : G.ancestorOf u r S hS ≠ r := by
      intro he
      have hm : r ∈ G.descendants u r (G.ancestorOf u r S hS) := by
        rw [he]
        exact ancestor_root _ r r
      rw [h] at hm
      exact hr hm
    exact ⟨hne, (G.past_eq_descendants u r _ hne).trans h⟩
  · rintro ⟨hne, h⟩
    exact (G.past_eq_descendants u r _ hne).symm.trans h

/-- Recover the unique outgoing copy from the source event, rather than assuming a cut. -/
noncomputable def eventCut {C S : Set V} {r : V} (hr : r ∉ C) (hS : S.Nonempty)
    {t : G.ComponentTree C} (u : G.AncestorPastTree C S r hS t) : G.CutTree C := by
  let a := G.ancestorOf u.val r S hS
  have hne := G.ancestor_ne_root_of_event hr hS u
  let e := G.parentEdge u.val r a hne
  have he := G.parentEdge_spec u.val r a hne
  have hcut := G.cut_components_componentAfter u.val e he.1 a
    (path (G.toSimple_isTree u.val.property) a r).snd he.2
  have hC : G.componentAfter u.val.val e a = C :=
    (G.past_eq_descendants u.val r a hne).trans u.property.1
  rw [hC] at hcut
  exact ⟨(u.val.val, e), u.val.property, hcut⟩

noncomputable def sourceEventEquiv {C S : Set V} (r : V) (hr : r ∉ C)
    (hS : S.Nonempty) (t : G.ComponentTree C) (hSC : S ⊆ C) :
    G.FixedCutTree C (G.componentSpan t S hSC) t ≃ G.AncestorPastTree C S r hS t where
  toFun p := by
    let u : G.SpanningTree := ⟨p.val.val.1, p.val.property.1⟩
    have htu : t.val ⊆ u.val := by
      rw [← p.property.1]
      exact Finset.filter_subset _ _
    have hspan := G.span_eq_componentSpan t u S hSC htu
    have hdesc : G.descendants u r (G.ancestorOf u r S hS) = C := by
      rcases (G.admissible_iff_of_subset (G.componentSpan_subset t S hSC) _).mp
        p.property.2 with hp | hp
      · have hvC := G.componentSpan_subset t S hSC hp.1
        have hgeom := G.ancestor_descendants_eq_cut_iff p.val r (G.left p.val.val.2)
          hr hvC hSC hS (Or.inl rfl)
        exact hgeom.mpr (hspan.symm ▸ hp.1)
      · have hvC := G.componentSpan_subset t S hSC hp.1
        have hgeom := G.ancestor_descendants_eq_cut_iff p.val r (G.right p.val.val.2)
          hr hvC hSC hS (Or.inr rfl)
        exact hgeom.mpr (hspan.symm ▸ hp.1)
    exact ⟨u, hdesc, p.property.1⟩
  invFun u := by
    let p := G.eventCut hr hS u
    have he := G.parentEdge_spec u.val r (G.ancestorOf u.val r S hS)
      (G.ancestor_ne_root_of_event hr hS u)
    have hca : G.ancestorOf u.val r S hS ∈ G.span u.val S :=
      commonAncestor_mem_connectingSubtree _ r S hS
    have htu : t.val ⊆ u.val.val :=
      (Finset.subset_of_eq u.property.2.symm).trans (Finset.filter_subset _ _)
    have hspan := G.span_eq_componentSpan t u.val S hSC htu
    have hcaK : G.ancestorOf u.val r S hS ∈ G.componentSpan t S hSC := hspan ▸ hca
    have hcaC : G.ancestorOf u.val r S hS ∈ C :=
      Eq.mp (congrArg (fun A : Set V => G.ancestorOf u.val r S hS ∈ A) u.property.1)
        (ancestor_refl _ _ _)
    have hc := p.property.2.2.1
    have hadm : G.admissible C (G.componentSpan t S hSC) p.val.2 := by
      apply (G.admissible_iff_of_subset (G.componentSpan_subset t S hSC) _).mpr
      rcases he.2 with he | he
      · have hl : G.left p.val.2 = G.ancestorOf u.val r S hS := he.1
        rcases hc with hc | hc
        · exact Or.inl ⟨(by rw [hl]; exact hcaK), hc.2⟩
        · exact (hc.1 ((by rw [hl]; exact hcaC))).elim
      · have hr' : G.right p.val.2 = G.ancestorOf u.val r S hS := he.1
        rcases hc with hc | hc
        · exact (hc.2 ((by rw [hr']; exact hcaC))).elim
        · exact Or.inr ⟨(by rw [hr']; exact hcaK), hc.1⟩
    exact ⟨p, u.property.2, hadm⟩
  left_inv p := by
    apply Subtype.ext
    apply G.cutTree_edges_injective C
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The exact unmarked ordinary-tree cardinal law, with K the actual component span. -/
theorem card_ancestorPastTree {C S : Set V} (r : V) (hr : r ∉ C) (hS : S.Nonempty)
    (t : G.ComponentTree C) (hSC : S ⊆ C) :
    Fintype.card (G.AncestorPastTree C S r hS t) =
      Fintype.card (G.ComponentTree Cᶜ) *
        (G.admissibleEdges C (G.componentSpan t S hSC)).card := by
  rw [← Fintype.card_congr (G.sourceEventEquiv r hr hS t hSC)]
  exact G.card_fixedCutTree C _ t (G.componentSpan_subset t S hSC)

/-- Uniform counting probability is defined only for an inhabited actual finite tree carrier. -/
noncomputable def uniformTreeProbability [Nonempty G.SpanningTree]
    (A : Set G.SpanningTree) : ℝ := (Nat.card A : ℝ) / Nat.card G.SpanningTree

/-- Exact finite normalized counting law for the source event, retaining every edge copy. -/
theorem probability_ancestorPastTree [Nonempty G.SpanningTree] {C S : Set V}
    (r : V) (hr : r ∉ C) (hS : S.Nonempty) (t : G.ComponentTree C) (hSC : S ⊆ C) :
    G.uniformTreeProbability {u | G.descendants u r (G.ancestorOf u r S hS) = C ∧
      G.internalEdges C u.val = t.val} =
      (Fintype.card (G.ComponentTree Cᶜ) : ℝ) / Fintype.card G.SpanningTree *
        (G.admissibleEdges C (G.componentSpan t S hSC)).card := by
  unfold uniformTreeProbability
  have hc : Nat.card {u : G.SpanningTree | G.descendants u r (G.ancestorOf u r S hS) = C ∧
      G.internalEdges C u.val = t.val} =
      Fintype.card (G.AncestorPastTree C S r hS t) := by
    exact (Nat.card_congr (show
      {u : G.SpanningTree | G.descendants u r (G.ancestorOf u r S hS) = C ∧
        G.internalEdges C u.val = t.val} ≃ G.AncestorPastTree C S r hS t
      from Equiv.refl _)).trans Nat.card_eq_fintype_card
  rw [hc, Nat.card_eq_fintype_card]
  rw [G.card_ancestorPastTree r hr hS t hSC, Nat.cast_mul]
  ring

/-- The literal boundary-degree formulation used in the manuscript. -/
theorem probability_ancestorPastTree_eq_sum [Nonempty G.SpanningTree] {C S : Set V}
    (r : V) (hr : r ∉ C) (hS : S.Nonempty) (t : G.ComponentTree C) (hSC : S ⊆ C) :
    G.uniformTreeProbability {u | G.descendants u r (G.ancestorOf u r S hS) = C ∧
      G.internalEdges C u.val = t.val} =
      (Fintype.card (G.ComponentTree Cᶜ) : ℝ) / Fintype.card G.SpanningTree *
        (∑ v ∈ (G.componentSpan t S hSC).toFinset, (G.crossingAt C v).card) := by
  rw [G.probability_ancestorPastTree r hr hS t hSC,
    G.card_admissibleEdges C _ (G.componentSpan_subset t S hSC)]

/-- Reciprocal cancellation on actual unmarked completions, with their own connecting span.
The common real mass remains explicit; an empty joining-copy fiber contributes zero. -/
theorem reciprocal_ancestorPastTree {C S : Set V} (r : V) (hr : r ∉ C)
    (hS : S.Nonempty) (t : G.ComponentTree C) (hSC : S ⊆ C) (c : ℝ) :
    (∑ u : G.AncestorPastTree C S r hS t,
      c / (G.admissibleEdges C (G.span u.val S)).card) =
      if (G.admissibleEdges C (G.componentSpan t S hSC)).Nonempty then
        c * Fintype.card (G.ComponentTree Cᶜ) else 0 := by
  have hs : (∑ u : G.AncestorPastTree C S r hS t,
      c / (G.admissibleEdges C (G.span u.val S)).card) =
      ∑ _u : G.AncestorPastTree C S r hS t,
        c / (G.admissibleEdges C (G.componentSpan t S hSC)).card := by
    apply Finset.sum_congr rfl
    intro u _
    have htu : t.val ⊆ u.val.val :=
      (Finset.subset_of_eq u.property.2.symm).trans (Finset.filter_subset _ _)
    rw [G.span_eq_componentSpan t u.val S hSC htu]
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    G.card_ancestorPastTree r hr hS t hSC, Nat.cast_mul]
  by_cases h : (G.admissibleEdges C (G.componentSpan t S hSC)).Nonempty
  · rw [if_pos h]
    have hc : ((G.admissibleEdges C (G.componentSpan t S hSC)).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr h
    field_simp
  · have hc : (G.admissibleEdges C (G.componentSpan t S hSC)).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    simp [h, hc]

/-- The actual finite counting normalization has total mass one. -/
theorem uniformTreeProbability_univ [Nonempty G.SpanningTree] :
    G.uniformTreeProbability Set.univ = 1 := by
  have hc : (Fintype.card G.SpanningTree : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [uniformTreeProbability, hc]

end FiniteAvalanches.Trees.Multigraph
