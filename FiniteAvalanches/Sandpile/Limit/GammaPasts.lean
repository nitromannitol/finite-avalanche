import FiniteAvalanches.Sandpile.Limit.GammaLaw
import FiniteAvalanches.Trees.Lattice.WiredTreePasts

/-! Spanning trees of the wired graph of a finite volume `Γ` are wired trees linked to
their lattice edge fields. Hence the union of the pasts of `B` satisfies its local event,
and it lies in a box whenever the edges at `B` are dual-certified in that box. -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.GammaGraph

open LatticeProb MeasureTheory FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Trees.RootedPaths FiniteAvalanches.Wilson.Lattice.SiteRoots
open scoped Classical

noncomputable section

/-- The vertex of the wired graph of `Γ` at a site, and the sink off `Γ`. -/
def siteVertex (Γ : Finset Site2) (x : Site2) : Vertex Γ :=
  if hx : x ∈ Γ then (vertexEquiv Γ ⟨x, hx⟩).val else none

theorem siteVertex_of_mem {Γ : Finset Site2} {x : Site2} (hx : x ∈ Γ) :
    siteVertex Γ x = (vertexEquiv Γ ⟨x, hx⟩).val := dif_pos hx

theorem siteVertex_eq_some {Γ : Finset Site2} {x : Site2} (hx : x ∈ Γ) :
    siteVertex Γ x = some ⟨some (ambient ⟨x, hx⟩), (activeEquiv Γ ⟨x, hx⟩).property⟩ := by
  rw [siteVertex_of_mem hx]
  rfl

theorem projectVertex_eq_siteVertex_iff {Γ : Finset Site2} {x : Site2} (hx : x ∈ Γ)
    (v : FiniteWired.Vertex (radius Γ)) :
    Burning.projectVertex (activeVertices Γ) v = siteVertex Γ x ↔ v = some (ambient ⟨x, hx⟩) := by
  rw [siteVertex_eq_some hx, Burning.project_vertex_eq_some_iff]

theorem projectVertex_eq_none_iff {Γ : Finset Site2} (v : FiniteWired.Vertex (radius Γ)) :
    Burning.projectVertex (activeVertices Γ) v = none ↔ v ∉ activeVertices Γ := by
  unfold Burning.projectVertex
  split_ifs with hv <;> simp [hv]

theorem mem_activeVertices_some {Γ : Finset Site2} (a : FiniteWired.Active (radius Γ)) :
    (some a : FiniteWired.Vertex (radius Γ)) ∈ activeVertices Γ ↔ FiniteWired.site a ∈ Γ := by
  simp [activeVertices]

theorem site_ambient' {Γ : Finset Site2} {x : Site2} (hx : x ∈ Γ) :
    FiniteWired.site (ambient ⟨x, hx⟩) = x := rfl

theorem ambient_site {Γ : Finset Site2} (a : FiniteWired.Active (radius Γ))
    (ha : FiniteWired.site a ∈ Γ) : ambient ⟨FiniteWired.site a, ha⟩ = a :=
  FiniteWired.site_injective _ rfl

theorem inBox_of_mem {Γ : Finset Site2} {x : Site2} (hx : x ∈ Γ) :
    FiniteWired.inBox (radius Γ) x := in_radius ⟨x, hx⟩

variable (Γ : Finset Site2) (t : (graph Γ).SpanningTree)

/-- The simple graph of a spanning tree of the wired graph of `Γ`. -/
abbrev treeGraph : SimpleGraph (Vertex Γ) := (graph Γ).toSimple t.val

theorem treeGraph_isTree : (treeGraph Γ t).IsTree := (graph Γ).toSimple_isTree t.property

theorem graph_left (c : Copy Γ) :
    (graph Γ).left c = Burning.projectVertex (activeVertices Γ)
      (FiniteWired.endpoints c.val).1 := rfl

theorem graph_right (c : Copy Γ) :
    (graph Γ).right c = Burning.projectVertex (activeVertices Γ)
      (FiniteWired.endpoints c.val).2 := rfl

/-- A copy joining the vertices of two sites of `Γ` is an interior copy of the lattice edge. -/
theorem copy_between_sites {x y : Site2} (hx : x ∈ Γ) (hy : y ∈ Γ) (c : Copy Γ)
    (hl : (graph Γ).left c = siteVertex Γ x) (hr : (graph Γ).right c = siteVertex Γ y) :
    ∃ h : (lattice 2).Adj x y,
      TreeMeasurability11.originalCopyEdge c.val = ⟨s(x, y), h⟩ := by
  rw [graph_left, projectVertex_eq_siteVertex_iff hx] at hl
  rw [graph_right, projectVertex_eq_siteVertex_iff hy] at hr
  rcases hcv : c.val with i | ex
  · rw [hcv] at hl hr
    simp only [FiniteWired.endpoints, Option.some.injEq] at hl hr
    obtain ⟨j, hj⟩ := i.property
    have hyx : y = x + unit j := by
      rw [← site_ambient' hx, ← site_ambient' hy, ← hl, ← hr]
      exact hj
    refine ⟨⟨j, Or.inl hyx⟩, ?_⟩
    apply Subtype.ext
    change s(FiniteWired.site i.val.1, FiniteWired.site i.val.2) = s(x, y)
    rw [hl, hr]
    rfl
  · rw [hcv] at hr
    simp [FiniteWired.endpoints] at hr

theorem toSimple_adj_siteVertex_iff {x y : Site2} (hx : x ∈ Γ) (hy : y ∈ Γ) :
    (treeGraph Γ t).Adj (siteVertex Γ x) (siteVertex Γ y) ↔
      (toGraph (gammaField Γ t)).Adj x y := by
  constructor
  · rintro ⟨c, hc, h⟩
    have key : ∀ {a b : Site2} (ha : a ∈ Γ) (hb : b ∈ Γ),
        (graph Γ).left c = siteVertex Γ a → (graph Γ).right c = siteVertex Γ b →
        (toGraph (gammaField Γ t)).Adj a b := by
      intro a b ha hb hl hr
      obtain ⟨hab, he⟩ := copy_between_sites Γ ha hb c hl hr
      refine ⟨hab, (forestField_eq_true _ _ _).mpr ⟨c.val, Finset.mem_image_of_mem _ hc, he, ?_⟩⟩
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact ha
      · exact hb
    rcases h with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact key hx hy hl hr
    · exact (key hy hx hl hr).symm
  · rintro ⟨hlat, hω⟩
    obtain ⟨c', hc', hce, hz⟩ := (forestField_eq_true _ _ _).mp hω
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
    refine ⟨c, hc, ?_⟩
    rcases hcv : c.val with i | ex
    · rw [hcv] at hce
      have hs : s(FiniteWired.site i.val.1, FiniteWired.site i.val.2) = s(x, y) :=
        congrArg Subtype.val hce
      rw [graph_left, graph_right, hcv]
      simp only [FiniteWired.endpoints]
      rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [projectVertex_eq_siteVertex_iff hx, projectVertex_eq_siteVertex_iff hy]
        exact ⟨congrArg some (FiniteWired.site_injective _ h1),
          congrArg some (FiniteWired.site_injective _ h2)⟩
      · right
        rw [projectVertex_eq_siteVertex_iff hx, projectVertex_eq_siteVertex_iff hy]
        exact ⟨congrArg some (FiniteWired.site_injective _ h2),
          congrArg some (FiniteWired.site_injective _ h1)⟩
    · exfalso
      rw [hcv] at hce
      have hmem : FiniteWired.site ex.val.1 + FiniteWired.step ex.val.2 ∈
          (⟨s(x, y), hlat⟩ : LatticeEdge).val := by
        rw [← hce]
        exact Sym2.mem_mk_right _ _
      exact ex.property (inBox_of_mem (hz _ hmem))

theorem gammaField_adj_mem {x y : Site2} (h : (toGraph (gammaField Γ t)).Adj x y) :
    x ∈ Γ ∧ y ∈ Γ := by
  obtain ⟨hlat, hω⟩ := h
  obtain ⟨-, -, -, hz⟩ := (forestField_eq_true _ _ _).mp hω
  exact ⟨hz x (Sym2.mem_mk_left _ _), hz y (Sym2.mem_mk_right _ _)⟩

theorem toSimple_adj_sink {x : Site2} (hx : x ∈ Γ)
    (h : (treeGraph Γ t).Adj (siteVertex Γ x) none) :
    ∃ z, (lattice 2).Adj x z ∧ z ∉ Γ := by
  obtain ⟨c, -, h⟩ := h
  have key : ∀ (v w : FiniteWired.Vertex (radius Γ)), FiniteWired.endpoints c.val = (v, w) ∨
      FiniteWired.endpoints c.val = (w, v) →
      Burning.projectVertex (activeVertices Γ) v = siteVertex Γ x →
      Burning.projectVertex (activeVertices Γ) w = none → ∃ z, (lattice 2).Adj x z ∧ z ∉ Γ := by
    intro v w hvw hv hw
    rw [projectVertex_eq_siteVertex_iff hx] at hv
    rw [projectVertex_eq_none_iff] at hw
    subst hv
    rcases hcv : c.val with i | ex
    · rw [hcv] at hvw
      simp only [FiniteWired.endpoints, Prod.mk.injEq] at hvw
      obtain ⟨j, hj⟩ := i.property
      rcases hvw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h2
        refine ⟨FiniteWired.site i.val.2, ⟨j, Or.inl ?_⟩, fun hm => hw ?_⟩
        · rw [hj, Option.some.inj h1]
          rfl
        · rw [mem_activeVertices_some]
          exact hm
      · subst h1
        refine ⟨FiniteWired.site i.val.1, ⟨j, Or.inr ?_⟩, fun hm => hw ?_⟩
        · rw [← site_ambient' hx, ← Option.some.inj h2]
          exact hj
        · rw [mem_activeVertices_some]
          exact hm
    · rw [hcv] at hvw
      simp only [FiniteWired.endpoints, Prod.mk.injEq] at hvw
      rcases hvw with ⟨h1, -⟩ | ⟨-, h2⟩
      · have hex : ex.val.1 = ambient ⟨x, hx⟩ := Option.some.inj h1
        refine ⟨x + FiniteWired.step ex.val.2, ?_, fun hm => ex.property ?_⟩
        · rcases ex.val.2 with ⟨j, b⟩
          cases b
          · exact ⟨j, Or.inr (by simp [FiniteWired.step])⟩
          · exact ⟨j, Or.inl (by simp [FiniteWired.step])⟩
        · rw [hex, site_ambient']
          exact inBox_of_mem hm
      · exact absurd h2 (by simp)
  rcases h with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · exact key _ _ (Or.inl rfl) hl hr
  · exact key _ _ (Or.inr rfl) hr hl

/-- A spanning tree of the wired graph of `Γ` is linked to its lattice edge field. -/
theorem wiredTreeLink :
    WiredTreeLink (T := treeGraph Γ t) none (siteVertex Γ) Γ (gammaField Γ t) where
  inj := by
    intro x hx y hy he
    rw [siteVertex_of_mem hx, siteVertex_of_mem hy] at he
    exact congrArg Subtype.val ((vertexEquiv Γ).injective (Subtype.ext he))
  ne_root := by
    intro x hx
    rw [siteVertex_eq_some hx]
    exact Option.some_ne_none _
  cover := by
    intro v
    rcases v with _ | a
    · exact Or.inl rfl
    · right
      obtain ⟨⟨x, hx⟩, rfl⟩ := (activeEquiv Γ).surjective a
      exact ⟨x, hx, (siteVertex_of_mem hx).symm⟩
  adj := fun x hx y hy => toSimple_adj_siteVertex_iff Γ t hx hy
  field := fun x y h => gammaField_adj_mem Γ t h
  exit := fun x hx h => toSimple_adj_sink Γ t hx h

theorem mem_pastSites_iff {B : Finset Site2} (hB : B ⊆ Γ) (x : Site2) :
    x ∈ pastSites Γ B t ↔ x ∈ Γ ∧ InPast (treeGraph_isTree Γ t) none (siteVertex Γ) B x := by
  simp only [pastSites, sitesOf, gammaPastUnion, InPast, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hx, _, b', hb', hmem⟩
    refine ⟨hx, ((vertexEquiv Γ).symm b').val, (mem_vertexSet_iff b').mp hb', ?_⟩
    rw [Multigraph.past_eq_descendants] at hmem
    rw [siteVertex_of_mem ((vertexEquiv Γ).symm b').property, siteVertex_of_mem hx]
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    exact hmem
  · rintro ⟨hx, b, hb, hmem⟩
    refine ⟨hx, hx, vertexEquiv Γ ⟨b, hB hb⟩, mem_vertexSet.mpr hb, ?_⟩
    rw [Multigraph.past_eq_descendants]
    rw [siteVertex_of_mem (hB hb), siteVertex_of_mem hx] at hmem
    exact hmem

theorem measurableSet_pastEvent (B S W : Finset Site2) : MeasurableSet (pastEvent B S W) :=
  (isClopen_pastEvent B S W).isClosed.measurableSet

theorem measurableSet_tightEvent (b : Site2) (W : Finset Site2) :
    MeasurableSet (tightEvent b W) :=
  (isClopen_tightEvent b W).isClosed.measurableSet

theorem treeLaw_preimage_gammaField (A : Set EdgeField) (hA : MeasurableSet A) :
    (graph Γ).treeLaw {t | gammaField Γ t ∈ A} = forestLaw (Γ : Set Site2) (radius Γ) A := by
  rw [← map_gammaField_treeLaw, Measure.map_apply (measurable_of_countable _) hA]
  rfl

/-- The past of `B` in the wired volume is controlled by its local event. -/
theorem treeLaw_pastSites_le {B S W : Finset Site2} (hBΓ : B ⊆ Γ) (hWΓ : W ⊆ Γ)
    (hnbr : ∀ b ∈ B, ∀ w, (lattice 2).Adj b w → w ∈ W) :
    (graph Γ).treeLaw {t | pastSites Γ B t = S} ≤
      forestLaw (Γ : Set Site2) (radius Γ) (pastEvent B S W) := by
  rw [← treeLaw_preimage_gammaField Γ _ (measurableSet_pastEvent B S W)]
  apply measure_mono
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  refine pastEvent_of_inPast (hT := treeGraph_isTree Γ t) (wiredTreeLink Γ t) hBΓ hWΓ hnbr
    fun x => ?_
  rw [← ht]
  exact mem_pastSites_iff Γ t hBΓ x

/-- The past of `B` leaves a box only on a tightness event at some site of `B`. -/
theorem treeLaw_pastSites_not_subset_le {B : Finset Site2} (hBΓ : B ⊆ Γ)
    (hnbr : ∀ b ∈ B, ∀ z, (lattice 2).Adj b z → z ∈ Γ) (k : ℕ)
    (hbox : ∀ x : Site2, |x 0| ≤ k → |x 1| ≤ k → ∀ z, (lattice 2).Adj x z → z ∈ Γ) :
    (graph Γ).treeLaw {t | ¬pastSites Γ B t ⊆ boxFinset k} ≤
      ∑ b ∈ B, forestLaw (Γ : Set Site2) (radius Γ) (tightEvent b (boxFinset k)) := by
  have hsub : {t : (graph Γ).SpanningTree | ¬pastSites Γ B t ⊆ boxFinset k} ⊆
      ⋃ b ∈ B, {t | gammaField Γ t ∈ tightEvent b (boxFinset k)} := by
    intro t ht
    simp only [Set.mem_setOf_eq, Finset.not_subset] at ht
    obtain ⟨x, hx, hxk⟩ := ht
    obtain ⟨hxΓ, b, hb, hmem⟩ := (mem_pastSites_iff Γ t hBΓ x).mp hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨b, hb, ?_⟩
    by_contra hcert
    obtain ⟨h0, h1⟩ := inPast_bounded (hT := treeGraph_isTree Γ t) (wiredTreeLink Γ t) (hBΓ hb)
      (hnbr b hb) hbox hcert hxΓ hmem
    apply hxk
    rw [mem_boxFinset]
    intro i
    fin_cases i
    · exact abs_le.mp h0
    · exact abs_le.mp h1
  calc (graph Γ).treeLaw {t | ¬pastSites Γ B t ⊆ boxFinset k}
      ≤ (graph Γ).treeLaw (⋃ b ∈ B, {t | gammaField Γ t ∈ tightEvent b (boxFinset k)}) :=
        measure_mono hsub
    _ ≤ ∑ b ∈ B, (graph Γ).treeLaw {t | gammaField Γ t ∈ tightEvent b (boxFinset k)} :=
        measure_biUnion_finset_le _ _
    _ = ∑ b ∈ B, forestLaw (Γ : Set Site2) (radius Γ) (tightEvent b (boxFinset k)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        exact treeLaw_preimage_gammaField Γ _ (measurableSet_tightEvent b _)

end

end FiniteAvalanches.Sandpile.GammaGraph
