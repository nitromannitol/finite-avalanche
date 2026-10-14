import FiniteAvalanches.Sandpile.Components.Trees

/-! Incoming main.tex324–330: the literal restriction/degree shift and inverse
reconstruction on every source-containing shape, followed by actual burning maps. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Literal inner restriction and outer degree subtraction on the full core fiber. -/
def restrictShape {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (η : CoreField o C.val) : InnerAllowed o C × OuterAllowed C := splitField η

/-- Literal two-coordinate reconstruction; source height is set by the minus-one
extension. Allowedness and exact maximal core are derived from the given pair. -/
def reconstructShape {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (r : InnerAllowed o C × OuterAllowed C) : CoreField o C.val :=
  ⟨⟨joinField r.1.val r.2.val, (join_field_allowed_core r.1 r.2).1⟩,
    (join_field_allowed_core r.1 r.2).2⟩

theorem restriction_inner {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (η : CoreField o C.val) (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) :
    wiredHeight (-1) η.val.val x.val = (((restrictShape C η).1.val x).val : ℤ) :=
  restrict_inner_height η x

theorem restriction_outer {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (η : CoreField o C.val) (x : {x : Site2 // x ∈ boxSites N \ C.val}) :
    wiredHeight (-1) η.val.val x.val - (degree C.val x.val : ℤ) =
      (((restrictShape C η).2.val x).val : ℤ) := restrict_outer_height η x

/-- The toNat outer carrier is exact: maximality proves nonnegativity first. -/
theorem outer_shift_nonnegative {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (η : CoreField o C.val) (x : {x : Site2 // x ∈ boxSites N \ C.val}) :
    0 ≤ wiredHeight (-1) η.val.val x.val - (degree C.val x.val : ℤ) := by
  have h := height_ge_degree_core_outside η.val.val (Finset.mem_sdiff.mp x.property).1
    (fun hx => (Finset.mem_sdiff.mp x.property).2 (by simpa only [η.property] using hx))
  rw [η.property] at h
  omega

theorem reconstruction_inner {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (r : InnerAllowed o C × OuterAllowed C)
    (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) :
    wiredHeight (-1) (reconstructShape C r).val.val x.val = ((r.1.val x).val : ℤ) :=
  join_field_height_inner r.1.val r.2.val x

theorem reconstruction_outer {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (r : InnerAllowed o C × OuterAllowed C)
    (x : {x : Site2 // x ∈ boxSites N \ C.val}) :
    wiredHeight (-1) (reconstructShape C r).val.val x.val =
      ((r.2.val x).val : ℤ) + (degree C.val x.val : ℤ) :=
  join_field_height_outer r.1.val r.2.val x

theorem reconstruction_source {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (r : InnerAllowed o C × OuterAllowed C) :
    wiredHeight (-1) (reconstructShape C r).val.val (FiniteWired.site o) = -1 := by
  rw [wired_height_site, active_height_source]

/-- All actual box coordinates obey the source stability bound, including source=-1. -/
theorem reconstruction_le_three {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (r : InnerAllowed o C × OuterAllowed C) :
    ∀ x ∈ boxSites N, wiredHeight (-1) (reconstructShape C r).val.val x ≤ 3 := by
  intro x hx
  by_cases hxo : x = FiniteWired.site o
  · rw [hxo, reconstruction_source C r]
    norm_num
  · rw [wired_height_off (-1) 4 _ hxo]
    exact wired_height_le_three _ hx hxo

theorem reconstruction_allowed_core {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (r : InnerAllowed o C × OuterAllowed C) :
    punctured_allowed (reconstructShape C r).val.val ∧
      core (reconstructShape C r).val.val = C.val :=
  join_field_allowed_core r.1 r.2

/-- Every reconstructed FSC lies inside Ω and contains the actual source.
This is derived from the constructed allowed field and its proved largest core. -/
theorem reconstruction_forbidden_location {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (r : InnerAllowed o C × OuterAllowed C)
    (B : Finset Site2) (hB : B ⊆ boxSites N)
    (hf : forbidden (wiredHeight (-1) (reconstructShape C r).val.val) B) :
    B ⊆ C.val ∧ FiniteWired.site o ∈ B := by
  constructor
  · have h := forbidden_subset_core hB hf
    change B ⊆ core (reconstructShape C r).val.val at h
    rw [(reconstruction_allowed_core C r).2] at h
    exact h
  · by_contra ho
    apply (reconstruction_allowed_core C r).1 B
    · intro x hx
      exact Finset.mem_erase.mpr ⟨fun he => ho (he ▸ hx), hB hx⟩
    · exact hf

theorem reconstruct_restrict {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (η : CoreField o C.val) : reconstructShape C (restrictShape C η) = η :=
  assemble_split_field η

theorem restrict_reconstruct {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (r : InnerAllowed o C × OuterAllowed C) : restrictShape C (reconstructShape C r) = r :=
  split_assemble_field r

/-- The current source bijection in inner-first order on EVERY admitted shape. -/
def sourceFieldEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    CoreField o C.val ≃ InnerAllowed o C × OuterAllowed C where
  toFun := restrictShape C
  invFun := reconstructShape C
  left_inv := reconstruct_restrict C
  right_inv := restrict_reconstruct C

/-- Counting uses the real stable/noFSC pair, not an assumed shape-count equality. -/
theorem card_source_field_pairs {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Nat.card (CoreField o C.val) = Nat.card (InnerAllowed o C) * Nat.card (OuterAllowed C) := by
  rw [Nat.card_congr (sourceFieldEquiv C), Nat.card_prod]

/-- The literal restriction route followed by two ordinary original-copy burning maps. -/
def sourceTreeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    CoreField o C.val ≃ InnerTrees C × OuterTrees C :=
  (sourceFieldEquiv C).trans (Equiv.prodCongr (innerAllowedTreeEquiv C) (outerAllowedTreeEquiv C))

theorem card_source_tree_product {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Nat.card (CoreField o C.val) = Nat.card (InnerTrees C) * Nat.card (OuterTrees C) := by
  rw [Nat.card_congr (sourceTreeEquiv C), Nat.card_prod]

/-- A genuine disconnected inner graph retains its carrier but has neither an
allowed sandpile nor an original-copy spanning tree. No connectivity restriction. -/
theorem inner_disconnected_zero {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (v : insideSupport C)
    (hv : ¬(inducedGraph (insideSupport C)).reaches Finset.univ v (innerRoot C)) :
    Nat.card (InnerAllowed o C) = 0 ∧ Nat.card (InnerTrees C) = 0 ∧
      Nat.card (CoreField o C.val) = 0 := by
  have ht : IsEmpty ((inducedGraph (insideSupport C)).SpanningTree) := ⟨fun t => by
    exact hv ((inducedGraph (insideSupport C)).reaches_mono (Finset.subset_univ _)
      (t.property.2.2.1 v (Set.mem_univ _) (innerRoot C) (Set.mem_univ _)))⟩
  letI : IsEmpty (InnerTrees C) := ⟨fun t => ht.false ((innerInducedTreeEquiv C).symm t)⟩
  letI : IsEmpty (InnerAllowed o C) :=
    ⟨fun r => isEmptyElim (innerAllowedTreeEquiv C r)⟩
  refine ⟨Nat.card_of_isEmpty, Nat.card_of_isEmpty, ?_⟩
  rw [card_source_field_pairs C, (Nat.card_of_isEmpty (α := InnerAllowed o C)), zero_mul]

theorem outer_disconnected_zero {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (v : outsideSupport C)
    (hv : ¬(inducedGraph (outsideSupport C)).reaches Finset.univ v (outerRoot C)) :
    Nat.card (OuterAllowed C) = 0 ∧ Nat.card (OuterTrees C) = 0 ∧
      Nat.card (CoreField o C.val) = 0 := by
  have ht : IsEmpty ((inducedGraph (outsideSupport C)).SpanningTree) := ⟨fun t => by
    exact hv ((inducedGraph (outsideSupport C)).reaches_mono (Finset.subset_univ _)
      (t.property.2.2.1 v (Set.mem_univ _) (outerRoot C) (Set.mem_univ _)))⟩
  letI : IsEmpty (OuterTrees C) := ⟨fun t => ht.false ((outerInducedTreeEquiv C).symm t)⟩
  letI : IsEmpty (OuterAllowed C) := ⟨fun r => isEmptyElim (outerAllowedTreeEquiv C r)⟩
  refine ⟨Nat.card_of_isEmpty, Nat.card_of_isEmpty, ?_⟩
  rw [card_source_field_pairs C, (Nat.card_of_isEmpty (α := OuterAllowed C)), mul_zero]

/-- Every counted carrier is finite; zero card is never an infinite-carrier convention. -/
theorem finite_source_carriers {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Finite (CoreField o C.val) ∧ Finite (InnerAllowed o C) ∧ Finite (OuterAllowed C) ∧
      Finite (InnerTrees C) ∧ Finite (OuterTrees C) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end
end FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction

/-! Exact declarations and imported meaning/providers used by this source route. -/
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.restrictShape
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.restrictShape
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstructShape
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstructShape
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.restriction_inner
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.restriction_inner
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.restriction_outer
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.restriction_outer
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.outer_shift_nonnegative
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.outer_shift_nonnegative
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_inner
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_inner
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_outer
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_outer
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_source
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_source
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_le_three
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_le_three
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_allowed_core
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_allowed_core
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_forbidden_location
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruction_forbidden_location
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruct_restrict
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.reconstruct_restrict
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.restrict_reconstruct
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.restrict_reconstruct
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.sourceFieldEquiv
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.sourceFieldEquiv
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.card_source_field_pairs
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.card_source_field_pairs
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.sourceTreeEquiv
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.sourceTreeEquiv
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.card_source_tree_product
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.card_source_tree_product
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.inner_disconnected_zero
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.inner_disconnected_zero
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.outer_disconnected_zero
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.outer_disconnected_zero
#print FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.finite_source_carriers
#print axioms FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction.finite_source_carriers
#print FiniteAvalanches.Sandpile.Components.ComponentShape
#print axioms FiniteAvalanches.Sandpile.Components.ComponentShape
#print FiniteAvalanches.Sandpile.Components.allowedOn
#print axioms FiniteAvalanches.Sandpile.Components.allowedOn
#print FiniteAvalanches.Sandpile.Components.InnerField
#print axioms FiniteAvalanches.Sandpile.Components.InnerField
#print FiniteAvalanches.Sandpile.Components.OuterField
#print axioms FiniteAvalanches.Sandpile.Components.OuterField
#print FiniteAvalanches.Sandpile.Components.InnerAllowed
#print axioms FiniteAvalanches.Sandpile.Components.InnerAllowed
#print FiniteAvalanches.Sandpile.Components.OuterAllowed
#print axioms FiniteAvalanches.Sandpile.Components.OuterAllowed
#print FiniteAvalanches.Sandpile.Components.CoreField
#print axioms FiniteAvalanches.Sandpile.Components.CoreField
#print FiniteAvalanches.Sandpile.Components.restrictInner
#print axioms FiniteAvalanches.Sandpile.Components.restrictInner
#print FiniteAvalanches.Sandpile.Components.restrictOuter
#print axioms FiniteAvalanches.Sandpile.Components.restrictOuter
#print FiniteAvalanches.Sandpile.Components.splitField
#print axioms FiniteAvalanches.Sandpile.Components.splitField
#print FiniteAvalanches.Sandpile.Components.assembleField
#print axioms FiniteAvalanches.Sandpile.Components.assembleField
#print FiniteAvalanches.Sandpile.Components.joinField
#print axioms FiniteAvalanches.Sandpile.Components.joinField
#print FiniteAvalanches.Sandpile.Components.join_field_allowed_core
#print axioms FiniteAvalanches.Sandpile.Components.join_field_allowed_core
#print FiniteAvalanches.Sandpile.Components.join_field_height_inner
#print axioms FiniteAvalanches.Sandpile.Components.join_field_height_inner
#print FiniteAvalanches.Sandpile.Components.join_field_height_outer
#print axioms FiniteAvalanches.Sandpile.Components.join_field_height_outer
#print FiniteAvalanches.Sandpile.Components.restrict_inner_height
#print axioms FiniteAvalanches.Sandpile.Components.restrict_inner_height
#print FiniteAvalanches.Sandpile.Components.restrict_outer_height
#print axioms FiniteAvalanches.Sandpile.Components.restrict_outer_height
#print FiniteAvalanches.Sandpile.Components.assemble_split_field
#print axioms FiniteAvalanches.Sandpile.Components.assemble_split_field
#print FiniteAvalanches.Sandpile.Components.split_assemble_field
#print axioms FiniteAvalanches.Sandpile.Components.split_assemble_field
#print FiniteAvalanches.Sandpile.Components.punctured_core_iff
#print axioms FiniteAvalanches.Sandpile.Components.punctured_core_iff
#print FiniteAvalanches.Sandpile.Components.height_ge_degree_core_outside
#print axioms FiniteAvalanches.Sandpile.Components.height_ge_degree_core_outside
#print FiniteAvalanches.Sandpile.Components.shifted_core_allowed
#print axioms FiniteAvalanches.Sandpile.Components.shifted_core_allowed
#print FiniteAvalanches.Sandpile.Components.shifted_core_height_stable
#print axioms FiniteAvalanches.Sandpile.Components.shifted_core_height_stable
#print FiniteAvalanches.Sandpile.Components.InducedEdge
#print axioms FiniteAvalanches.Sandpile.Components.InducedEdge
#print FiniteAvalanches.Sandpile.Components.inducedGraph
#print axioms FiniteAvalanches.Sandpile.Components.inducedGraph
#print FiniteAvalanches.Sandpile.Components.insideSupport
#print axioms FiniteAvalanches.Sandpile.Components.insideSupport
#print FiniteAvalanches.Sandpile.Components.outsideSupport
#print axioms FiniteAvalanches.Sandpile.Components.outsideSupport
#print FiniteAvalanches.Sandpile.Components.innerRoot
#print axioms FiniteAvalanches.Sandpile.Components.innerRoot
#print FiniteAvalanches.Sandpile.Components.outerRoot
#print axioms FiniteAvalanches.Sandpile.Components.outerRoot
#print FiniteAvalanches.Sandpile.Components.insideVertex
#print axioms FiniteAvalanches.Sandpile.Components.insideVertex
#print FiniteAvalanches.Sandpile.Components.outsideVertex
#print axioms FiniteAvalanches.Sandpile.Components.outsideVertex
#print FiniteAvalanches.Sandpile.Components.InnerTrees
#print axioms FiniteAvalanches.Sandpile.Components.InnerTrees
#print FiniteAvalanches.Sandpile.Components.OuterTrees
#print axioms FiniteAvalanches.Sandpile.Components.OuterTrees
#print FiniteAvalanches.Sandpile.Components.graphDegree
#print axioms FiniteAvalanches.Sandpile.Components.graphDegree
#print FiniteAvalanches.Sandpile.Components.inner_source_degree
#print axioms FiniteAvalanches.Sandpile.Components.inner_source_degree
#print FiniteAvalanches.Sandpile.Components.outer_source_degree
#print axioms FiniteAvalanches.Sandpile.Components.outer_source_degree
#print FiniteAvalanches.Sandpile.Components.inner_subset_degree
#print axioms FiniteAvalanches.Sandpile.Components.inner_subset_degree
#print FiniteAvalanches.Sandpile.Components.outer_subset_degree
#print axioms FiniteAvalanches.Sandpile.Components.outer_subset_degree
#print FiniteAvalanches.Sandpile.Components.innerAllowedSourceEquiv
#print axioms FiniteAvalanches.Sandpile.Components.innerAllowedSourceEquiv
#print FiniteAvalanches.Sandpile.Components.outerAllowedSourceEquiv
#print axioms FiniteAvalanches.Sandpile.Components.outerAllowedSourceEquiv
#print FiniteAvalanches.Sandpile.Components.innerSourceHeightsEquiv
#print axioms FiniteAvalanches.Sandpile.Components.innerSourceHeightsEquiv
#print FiniteAvalanches.Sandpile.Components.outerSourceHeightsEquiv
#print axioms FiniteAvalanches.Sandpile.Components.outerSourceHeightsEquiv
#print FiniteAvalanches.Sandpile.Components.innerGraphTreeEquiv
#print axioms FiniteAvalanches.Sandpile.Components.innerGraphTreeEquiv
#print FiniteAvalanches.Sandpile.Components.outerGraphTreeEquiv
#print axioms FiniteAvalanches.Sandpile.Components.outerGraphTreeEquiv
#print FiniteAvalanches.Sandpile.Components.innerInducedTreeEquiv
#print axioms FiniteAvalanches.Sandpile.Components.innerInducedTreeEquiv
#print FiniteAvalanches.Sandpile.Components.outerInducedTreeEquiv
#print axioms FiniteAvalanches.Sandpile.Components.outerInducedTreeEquiv
#print FiniteAvalanches.Sandpile.Components.innerAllowedTreeEquiv
#print axioms FiniteAvalanches.Sandpile.Components.innerAllowedTreeEquiv
#print FiniteAvalanches.Sandpile.Components.outerAllowedTreeEquiv
#print axioms FiniteAvalanches.Sandpile.Components.outerAllowedTreeEquiv
#print FiniteAvalanches.Sandpile.Components.direction_edge_injective
#print axioms FiniteAvalanches.Sandpile.Components.direction_edge_injective
#print FiniteAvalanches.Sandpile.Components.singleton_inner_unique
#print axioms FiniteAvalanches.Sandpile.Components.singleton_inner_unique
#print FiniteAvalanches.Sandpile.Components.full_outer_unique
#print axioms FiniteAvalanches.Sandpile.Components.full_outer_unique
#print FiniteAvalanches.Sandpile.Components.inner_allowed_empty_of_closed_part
#print axioms FiniteAvalanches.Sandpile.Components.inner_allowed_empty_of_closed_part
#print FiniteAvalanches.Sandpile.Waves.OffVertex
#print axioms FiniteAvalanches.Sandpile.Waves.OffVertex
#print FiniteAvalanches.Sandpile.Waves.OffField
#print axioms FiniteAvalanches.Sandpile.Waves.OffField
#print FiniteAvalanches.Sandpile.Waves.activeHeight
#print axioms FiniteAvalanches.Sandpile.Waves.activeHeight
#print FiniteAvalanches.Sandpile.Waves.wiredHeight
#print axioms FiniteAvalanches.Sandpile.Waves.wiredHeight
#print FiniteAvalanches.Sandpile.Waves.punctured_allowed
#print axioms FiniteAvalanches.Sandpile.Waves.punctured_allowed
#print FiniteAvalanches.Sandpile.Waves.Punctured
#print axioms FiniteAvalanches.Sandpile.Waves.Punctured
#print FiniteAvalanches.Sandpile.Waves.core
#print axioms FiniteAvalanches.Sandpile.Waves.core
#print FiniteAvalanches.Sandpile.Waves.forbidden
#print axioms FiniteAvalanches.Sandpile.Waves.forbidden
#print FiniteAvalanches.Sandpile.Waves.allowed
#print axioms FiniteAvalanches.Sandpile.Waves.allowed
#print FiniteAvalanches.Sandpile.Waves.degree
#print axioms FiniteAvalanches.Sandpile.Waves.degree
#print FiniteAvalanches.Sandpile.Waves.forbiddenCore
#print axioms FiniteAvalanches.Sandpile.Waves.forbiddenCore
#print FiniteAvalanches.Sandpile.Waves.forbidden_subset_core
#print axioms FiniteAvalanches.Sandpile.Waves.forbidden_subset_core
#print FiniteAvalanches.Sandpile.Waves.degree_le_sdiff_add
#print axioms FiniteAvalanches.Sandpile.Waves.degree_le_sdiff_add
#print FiniteAvalanches.Sandpile.Waves.core_forbidden
#print axioms FiniteAvalanches.Sandpile.Waves.core_forbidden
#print FiniteAvalanches.Sandpile.Waves.wired_height_le_three
#print axioms FiniteAvalanches.Sandpile.Waves.wired_height_le_three
#print FiniteAvalanches.Sandpile.Waves.wired_height_off
#print axioms FiniteAvalanches.Sandpile.Waves.wired_height_off
#print FiniteAvalanches.Sandpile.Waves.wired_height_site
#print axioms FiniteAvalanches.Sandpile.Waves.wired_height_site
#print FiniteAvalanches.Sandpile.Waves.active_height_source
#print axioms FiniteAvalanches.Sandpile.Waves.active_height_source
#print FiniteAvalanches.Sandpile.FiniteWired.Active
#print axioms FiniteAvalanches.Sandpile.FiniteWired.Active
#print FiniteAvalanches.Sandpile.FiniteWired.Vertex
#print axioms FiniteAvalanches.Sandpile.FiniteWired.Vertex
#print FiniteAvalanches.Sandpile.FiniteWired.InteriorEdge
#print axioms FiniteAvalanches.Sandpile.FiniteWired.InteriorEdge
#print FiniteAvalanches.Sandpile.FiniteWired.ExitEdge
#print axioms FiniteAvalanches.Sandpile.FiniteWired.ExitEdge
#print FiniteAvalanches.Sandpile.FiniteWired.Edge
#print axioms FiniteAvalanches.Sandpile.FiniteWired.Edge
#print FiniteAvalanches.Sandpile.FiniteWired.endpoints
#print axioms FiniteAvalanches.Sandpile.FiniteWired.endpoints
#print FiniteAvalanches.Sandpile.FiniteWired.Heights
#print axioms FiniteAvalanches.Sandpile.FiniteWired.Heights
#print FiniteAvalanches.Sandpile.FiniteWired.recurrent
#print axioms FiniteAvalanches.Sandpile.FiniteWired.recurrent
#print FiniteAvalanches.Sandpile.FiniteWired.Recurrent
#print axioms FiniteAvalanches.Sandpile.FiniteWired.Recurrent
#print FiniteAvalanches.Sandpile.FiniteWired.site
#print axioms FiniteAvalanches.Sandpile.FiniteWired.site
#print FiniteAvalanches.Sandpile.FiniteWired.inBox
#print axioms FiniteAvalanches.Sandpile.FiniteWired.inBox
#print FiniteAvalanches.Sandpile.FiniteWired.activeOfSite
#print axioms FiniteAvalanches.Sandpile.FiniteWired.activeOfSite
#print FiniteAvalanches.Sandpile.FiniteWired.directionEdge
#print axioms FiniteAvalanches.Sandpile.FiniteWired.directionEdge
#print FiniteAvalanches.Sandpile.FiniteWired.direction_edge_exit
#print axioms FiniteAvalanches.Sandpile.FiniteWired.direction_edge_exit
#print FiniteAvalanches.Sandpile.Burning.SourceVertex
#print axioms FiniteAvalanches.Sandpile.Burning.SourceVertex
#print FiniteAvalanches.Sandpile.Burning.SourceHeights
#print axioms FiniteAvalanches.Sandpile.Burning.SourceHeights
#print FiniteAvalanches.Sandpile.Burning.Heights
#print axioms FiniteAvalanches.Sandpile.Burning.Heights
#print FiniteAvalanches.Sandpile.Burning.noForbidden
#print axioms FiniteAvalanches.Sandpile.Burning.noForbidden
#print FiniteAvalanches.Sandpile.Burning.activeDegree
#print axioms FiniteAvalanches.Sandpile.Burning.activeDegree
#print FiniteAvalanches.Sandpile.Burning.incidentInto
#print axioms FiniteAvalanches.Sandpile.Burning.incidentInto
#print FiniteAvalanches.Sandpile.Burning.degreeInto
#print axioms FiniteAvalanches.Sandpile.Burning.degreeInto
#print FiniteAvalanches.Sandpile.Burning.degree
#print axioms FiniteAvalanches.Sandpile.Burning.degree
#print FiniteAvalanches.Sandpile.Burning.copiedTreeGraph
#print axioms FiniteAvalanches.Sandpile.Burning.copiedTreeGraph
#print FiniteAvalanches.Sandpile.Burning.burningEquiv
#print axioms FiniteAvalanches.Sandpile.Burning.burningEquiv
#print FiniteAvalanches.Sandpile.Burning.canonicalBurningEquiv
#print axioms FiniteAvalanches.Sandpile.Burning.canonicalBurningEquiv
#print FiniteAvalanches.Sandpile.WiredTrees.graph
#print axioms FiniteAvalanches.Sandpile.WiredTrees.graph
#print FiniteAvalanches.Trees.Multigraph.is_tree
#print axioms FiniteAvalanches.Trees.Multigraph.is_tree
#print FiniteAvalanches.Trees.Multigraph.supported
#print axioms FiniteAvalanches.Trees.Multigraph.supported
#print FiniteAvalanches.Trees.Multigraph.reaches
#print axioms FiniteAvalanches.Trees.Multigraph.reaches
#print FiniteAvalanches.Trees.Multigraph.is_forest
#print axioms FiniteAvalanches.Trees.Multigraph.is_forest
#print FiniteAvalanches.Trees.Multigraph.SpanningTree
#print axioms FiniteAvalanches.Trees.Multigraph.SpanningTree
#print FiniteAvalanches.Trees.Multigraph.reaches_mono
#print axioms FiniteAvalanches.Trees.Multigraph.reaches_mono
#print FiniteAvalanches.Trees.Multigraph.eq_empty_of_is_tree_singleton
#print axioms FiniteAvalanches.Trees.Multigraph.eq_empty_of_is_tree_singleton
#print Nat.card_congr
#print axioms Nat.card_congr
#print Nat.card_prod
#print axioms Nat.card_prod
#print Nat.card_of_isEmpty
#print axioms Nat.card_of_isEmpty
#print Nat.card_eq_one_iff_exists
#print axioms Nat.card_eq_one_iff_exists
