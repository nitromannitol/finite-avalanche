import FiniteAvalanches.Sandpile.Limit.GammaInner
import FiniteAvalanches.Sandpile.Limit.GammaForests
import FiniteAvalanches.Paper.Current.RawGraphConnectivity

/-! The finite-volume sandpile law of the heights on a finite set `B` of sites, as a mixture
over the union of the pasts of `B` in the uniform spanning tree of the wired graph. The
mixture weights `innerRatio` depend only on lattice data (held burning, Lemma 2.1, and the
uniformity of the inner heights). -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.GammaGraph

open LatticeProb MeasureTheory FiniteAvalanches.Trees FiniteAvalanches.External.SandpileLimit
open scoped Classical ENNReal

noncomputable section

/-- An auxiliary order on copies, needed only to apply the burning bijection. -/
abbrev copyOrder (Γ : Finset Site2) : LinearOrder (Copy Γ) :=
  LinearOrder.lift' (Fintype.equivFin (Copy Γ)) (Fintype.equivFin (Copy Γ)).injective

/-- Pasts do not depend on the decidable equality used to state tree certificates. -/
theorem past_decidable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
    (d f : DecidableEq E) (t : @Multigraph.SpanningTree V E _ _ d G) (r a : V) (hne : a ≠ r) :
    @Multigraph.past V E _ _ d G t r a hne =
      @Multigraph.past V E _ _ f G (G.spanningTreeDecidableEquiv d f t) r a hne := by
  obtain rfl : d = f := Subsingleton.elim _ _
  rfl

local instance finsetVertexMeasurableSpace (Γ : Finset Site2) :
    MeasurableSpace (Finset (Vertex Γ)) := ⊤

local instance finsetVertexMeasurableSingletonClass (Γ : Finset Site2) :
    MeasurableSingletonClass (Finset (Vertex Γ)) := ⟨fun _ => trivial⟩

/-- Discrete σ-algebra on finite sets of sites. -/
local instance finsetSiteMeasurableSpace : MeasurableSpace (Finset Site2) := ⊤

local instance finsetSiteMeasurableSingletonClass : MeasurableSingletonClass (Finset Site2) :=
  ⟨fun _ => trivial⟩

/-- The sites of `Γ` whose vertices lie in a set of vertices of the wired graph. -/
def sitesOf (Γ : Finset Site2) (W : Finset (Vertex Γ)) : Finset Site2 :=
  Γ.filter fun x => ∃ hx : x ∈ Γ, (vertexEquiv Γ ⟨x, hx⟩).val ∈ W

theorem sitesOf_subset (Γ : Finset Site2) (W : Finset (Vertex Γ)) : sitesOf Γ W ⊆ Γ :=
  Finset.filter_subset _ _

theorem sitesOf_image (Γ : Finset Site2) (H : Finset (Burning.SourceVertex (none : Vertex Γ))) :
    sitesOf Γ (H.image Subtype.val) = siteSet Γ H := by
  ext x
  rw [sitesOf, siteSet, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hx, _, hmem⟩
    obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hmem
    refine ⟨v, hv, ?_⟩
    have : v = vertexEquiv Γ ⟨x, hx⟩ := Subtype.ext hve
    rw [this, Equiv.symm_apply_apply]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨((vertexEquiv Γ).symm v).property, ((vertexEquiv Γ).symm v).property,
      Finset.mem_image.mpr ⟨v, hv, ?_⟩⟩
    rw [Equiv.apply_symm_apply]

theorem uniformMeasure_fintype_irrel (α : Type*) [MeasurableSpace α] [MeasurableSingletonClass α]
    [Nonempty α] (f g : Fintype α) :
    @FiniteAvalanches.uniformMeasure α f _ _ _ = @FiniteAvalanches.uniformMeasure α g _ _ _ := by
  obtain rfl : f = g := Subsingleton.elim f g
  rfl

/-- The decidable equality on copies induced by the auxiliary order. -/
abbrev orderDecEq (Γ : Finset Site2) : DecidableEq (Copy Γ) :=
  fun a b => @LinearOrder.toDecidableEq _ (copyOrder Γ) a b

instance gammaTreeNonempty (Γ : Finset Site2) : Nonempty (graph Γ).SpanningTree :=
  (graph Γ).nonempty_spanning_tree
    ((FiniteAvalanches.Paper.CurrentRawBurning.connected_iff_reaches (graph Γ)).mp
      (graph_connected Γ))

/-- The union of the pasts of the vertices at `B` in a spanning tree of the wired graph. -/
def gammaPastUnion (Γ B : Finset Site2) (t : (graph Γ).SpanningTree) : Finset (Vertex Γ) :=
  Finset.univ.filter fun x => ∃ b ∈ vertexSet Γ B,
    x ∈ (graph Γ).past t none b.val (Burning.source_vertex_ne_sink none b)

/-- The sites of the union of the pasts of the vertices at `B` in a spanning tree. -/
def pastSites (Γ B : Finset Site2) (t : (graph Γ).SpanningTree) : Finset Site2 :=
  sitesOf Γ (gammaPastUnion Γ B t)

/-- The sites of the held-burning remainder with held sites `B`. -/
def remainderSites (Γ B : Finset Site2) (h : AllowedHeights Γ) : Finset Site2 :=
  siteSet Γ (Burning.heldBurning (graph Γ) (Finset.univ.erase none) h.val (vertexSet Γ B))

/-- Held burning (Lemma 2.1): the remainder has the law of the union of the pasts. -/
theorem map_remainderSites (Γ B : Finset Site2) :
    Measure.map (remainderSites Γ B) (FiniteAvalanches.uniformMeasure (AllowedHeights Γ)) =
      Measure.map (pastSites Γ B) (graph Γ).treeLaw := by
  have hne : Nonempty (@Multigraph.SpanningTree _ _ _ _ (orderDecEq Γ) (graph Γ)) :=
    Nonempty.map ((graph Γ).spanningTreeDecidableEquiv inferInstance (orderDecEq Γ))
      (gammaTreeNonempty Γ)
  have h := @Burning.canonical_uniform_held_past_law (Vertex Γ) (Copy Γ) _ _ _ (copyOrder Γ)
    (graph Γ) (none : Vertex Γ) hne _ (vertexSet Γ B)
  have hlaw : Measure.map ((graph Γ).spanningTreeDecidableEquiv inferInstance (orderDecEq Γ))
      (graph Γ).treeLaw = @Multigraph.treeLaw _ _ _ _ (orderDecEq Γ) (graph Γ) hne :=
    (graph Γ).tree_law_map_spanning_tree_decidable_equiv inferInstance (orderDecEq Γ)
  have h2 : Measure.map (fun t => @Burning.canonicalPastUnion (Vertex Γ) (Copy Γ) _ _ _
      (copyOrder Γ) (graph Γ) (none : Vertex Γ) t (vertexSet Γ B))
      (@Multigraph.treeLaw _ _ _ _ (orderDecEq Γ) (graph Γ) hne) =
      Measure.map (gammaPastUnion Γ B) (graph Γ).treeLaw := by
    rw [← hlaw, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext t
    ext x
    simp only [Function.comp_apply, Burning.canonicalPastUnion, gammaPastUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine exists_congr fun b => and_congr_right fun _ => ?_
    rw [past_decidable (graph Γ) (orderDecEq Γ) inferInstance]
    rfl
  have h3 := congrArg (Measure.map (sitesOf Γ)) (h.trans h2)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at h3
  convert h3 using 2
  all_goals first
    | (funext h; exact (sitesOf_image Γ _).symm)
    | exact uniformMeasure_fintype_irrel _ _ _
    | rfl

theorem treeLaw_pastSites_eq (Γ B S : Finset Site2) :
    (graph Γ).treeLaw {t | pastSites Γ B t = S} =
      FiniteAvalanches.uniformMeasure (AllowedHeights Γ) {h | remainderSites Γ B h = S} := by
  have h := congrArg (fun μ : Measure (Finset Site2) => μ {S}) (map_remainderSites Γ B)
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton S),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton S)] at h
  exact h.symm

theorem subset_remainderSites {Γ B : Finset Site2} (hB : B ⊆ Γ) (h : AllowedHeights Γ) :
    B ⊆ remainderSites Γ B h := by
  have hc := (Burning.held_burning_largest (graph Γ) (Finset.univ.erase none) h.val
    (vertexSet Γ B)).1.1
  intro x hx
  rw [remainderSites, siteSet, Finset.mem_image]
  refine ⟨vertexEquiv Γ ⟨x, hB hx⟩, hc (mem_vertexSet.mpr hx), ?_⟩
  rw [Equiv.symm_apply_apply]

theorem remainderSites_eq_iff {Γ B S : Finset Site2} (hS : S ⊆ Γ) (h : AllowedHeights Γ) :
    remainderSites Γ B h = S ↔
      Burning.heldBurning (graph Γ) (Finset.univ.erase none) h.val (vertexSet Γ B) =
        vertexSet Γ S := by
  constructor
  · intro he
    rw [← he, remainderSites, vertexSet_siteSet]
  · intro he
    rw [remainderSites, he, siteSet_vertexSet hS]

theorem values_iff {Γ B : Finset Site2} (hB : B ⊆ Γ) (ξ : Site2 → ℕ) (h : AllowedHeights Γ) :
    (∀ x ∈ B, ((allowedHeightsEquiv Γ h).val x).val = ξ x) ↔
      ∀ v ∈ vertexSet Γ B, (h.val v).val = ξ ((vertexEquiv Γ).symm v).val := by
  constructor
  · intro hv v hvB
    have hx := (mem_vertexSet_iff v).mp hvB
    have := hv _ hx
    rw [show ((vertexEquiv Γ).symm v).val = ((vertexEquiv Γ).symm v).val from rfl] at this
    have hval := allowedHeightsEquiv_value_nat Γ h ((vertexEquiv Γ).symm v)
    rw [Equiv.apply_symm_apply] at hval
    rw [← hval]
    exact this
  · intro hv x hx
    have := hv (vertexEquiv Γ ⟨x, hB hx⟩) (mem_vertexSet.mpr hx)
    rw [Equiv.symm_apply_apply] at this
    rw [allowedHeightsEquiv_value_nat Γ h ⟨x, hB hx⟩]
    exact this

/-- The conditional probability of prescribed heights on `B` given the remainder `S`. -/
def innerRatio (B S : Finset Site2) (ξ : Site2 → ℕ) : ℝ≥0∞ :=
  ((latticeInnerValues B S ξ).card : ℝ≥0∞) / (latticeInner B S).card

theorem latticeInnerValues_card_le (B S : Finset Site2) (ξ : Site2 → ℕ) :
    (latticeInnerValues B S ξ).card ≤ (latticeInner B S).card :=
  Finset.card_filter_le _ _

private theorem ratio_identity (a b c d o N : ℕ) (ha : a = d * o) (hb : b = c * o) (hdc : d ≤ c) :
    (a : ℝ≥0∞) / N = (b : ℝ≥0∞) / N * ((d : ℝ≥0∞) / c) := by
  by_cases hc : c = 0
  · have hd : d = 0 := Nat.le_zero.mp (hc ▸ hdc)
    subst hc hd
    simp [ha]
  · rw [ha, hb]
    push_cast
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    have hct : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
    calc (N : ℝ≥0∞)⁻¹ * (d * o) = (N : ℝ≥0∞)⁻¹ * (d * o) * ((c : ℝ≥0∞)⁻¹ * c) := by
          rw [ENNReal.inv_mul_cancel hc' hct, mul_one]
      _ = (N : ℝ≥0∞)⁻¹ * (c * o) * ((c : ℝ≥0∞)⁻¹ * d) := by ring

/-- Given the remainder, prescribed heights on `B` have probability `innerRatio`. -/
theorem uniform_remainder_values {Γ B S : Finset Site2} (hB : B ⊆ Γ) (hS : S ⊆ Γ)
    (ξ : Site2 → ℕ) :
    FiniteAvalanches.uniformMeasure (AllowedHeights Γ)
        {h | remainderSites Γ B h = S ∧ ∀ x ∈ B, ((allowedHeightsEquiv Γ h).val x).val = ξ x} =
      FiniteAvalanches.uniformMeasure (AllowedHeights Γ) {h | remainderSites Γ B h = S} *
        innerRatio B S ξ := by
  by_cases hBS : B ⊆ S
  · rw [FiniteAvalanches.uniformMeasure_apply, FiniteAvalanches.uniformMeasure_apply, innerRatio]
    let G := graph Γ
    let U : Finset (Vertex Γ) := Finset.univ.erase none
    have hBA : vertexSet Γ B ⊆ vertexSet Γ S := vertexSet_mono hBS
    let ξ' : Burning.SourceVertex (none : Vertex Γ) → ℕ := fun v => ξ ((vertexEquiv Γ).symm v).val
    have e1 : {h : AllowedHeights Γ | remainderSites Γ B h = S ∧
        ∀ x ∈ B, ((allowedHeightsEquiv Γ h).val x).val = ξ x} ≃
        {h : Burning.Heights G U // Burning.noForbidden G U h ∧
          Burning.heldBurning G U h (vertexSet Γ B) = vertexSet Γ S ∧
          ∀ x ∈ vertexSet Γ B, (h x).val = ξ' x} :=
      (Equiv.subtypeEquivRight (fun h => and_congr (remainderSites_eq_iff hS h)
        (values_iff hB ξ h))).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun h : Burning.Heights G U =>
          Burning.noForbidden G U h) (fun h => Burning.heldBurning G U h (vertexSet Γ B) =
            vertexSet Γ S ∧ ∀ x ∈ vertexSet Γ B, (h x).val = ξ' x))
    have e2 : {h : AllowedHeights Γ | remainderSites Γ B h = S} ≃
        {h : Burning.Heights G U // Burning.noForbidden G U h ∧
          Burning.heldBurning G U h (vertexSet Γ B) = vertexSet Γ S} :=
      (Equiv.subtypeEquivRight (fun h => remainderSites_eq_iff hS h)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun h : Burning.Heights G U =>
          Burning.noForbidden G U h) (fun h => Burning.heldBurning G U h (vertexSet Γ B) =
            vertexSet Γ S))
    rw [Nat.card_congr e1, Nat.card_congr e2]
    apply ratio_identity
    · rw [Burning.card_held_values G U _ _ hBA ξ', card_inner_values hS hBS ξ]
    · rw [Burning.card_held G U _ _ hBA, card_inner hS]
    · exact latticeInnerValues_card_le B S ξ
  · have hempty : {h : AllowedHeights Γ | remainderSites Γ B h = S} = ∅ := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro he
      exact hBS (he ▸ subset_remainderSites hB h)
    have hempty' : {h : AllowedHeights Γ | remainderSites Γ B h = S ∧
        ∀ x ∈ B, ((allowedHeightsEquiv Γ h).val x).val = ξ x} = ∅ := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro he
      exact absurd (he ▸ subset_remainderSites hB h) hBS
    rw [hempty, hempty', measure_empty, zero_mul]

/-- The cylinder event of prescribed heights on a finite set. -/
def heightEvent (B : Finset Site2) (ξ : Site2 → ℕ) : Set StableField :=
  {η | ∀ x ∈ B, (η x).val = ξ x}

theorem measurableSet_heightEvent (B : Finset Site2) (ξ : Site2 → ℕ) :
    MeasurableSet (heightEvent B ξ) := by
  have h : heightEvent B ξ = ⋂ x ∈ B, (fun η : StableField => η x) ⁻¹' {k | k.val = ξ x} := by
    ext η
    simp [heightEvent]
  rw [h]
  exact Finset.measurableSet_biInter _ fun x _ =>
    measurable_pi_apply x (Set.toFinite _).measurableSet

/-- The finite-volume law of prescribed heights on `B` as a mixture over the union of the
pasts of `B` in the uniform spanning tree of the wired graph of `Γ`. -/
theorem finiteFieldLawOn_heightEvent {Γ B : Finset Site2} (hB : B ⊆ Γ) (ξ : Site2 → ℕ) :
    finiteFieldLawOn Γ (heightEvent B ξ) =
      ∑ S ∈ Γ.powerset, (graph Γ).treeLaw {t | pastSites Γ B t = S} * innerRatio B S ξ := by
  rw [finiteFieldLawOn_eq_map, Measure.map_apply (measurable_of_countable _)
    (measurableSet_heightEvent B ξ)]
  have hcover : (fun h => (allowedHeightsEquiv Γ h).val) ⁻¹' heightEvent B ξ =
      ⋃ S ∈ Γ.powerset, {h : AllowedHeights Γ | remainderSites Γ B h = S ∧
        ∀ x ∈ B, ((allowedHeightsEquiv Γ h).val x).val = ξ x} := by
    ext h
    simp only [Set.mem_preimage, heightEvent, Set.mem_setOf_eq, Set.mem_iUnion,
      Finset.mem_powerset, exists_prop]
    constructor
    · intro hv
      exact ⟨remainderSites Γ B h, siteSet_subset Γ _, rfl, hv⟩
    · rintro ⟨S, -, -, hv⟩
      exact hv
  rw [hcover, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun S hS => ?_
    rw [uniform_remainder_values hB (Finset.mem_powerset.mp hS) ξ, treeLaw_pastSites_eq]
  · intro S _ S' _ hne
    exact Set.disjoint_left.mpr fun h h1 h2 => hne (h1.1.symm.trans h2.1)
  · exact fun _ _ => trivial

end

end FiniteAvalanches.Sandpile.GammaGraph
