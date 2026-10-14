import FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction
import FiniteAvalanches.Sandpile.Components.Marked.ContactLaw

/-! Forward restriction bounds for the full shape fiber. -/
namespace FiniteAvalanches.Sandpile.Components.ShapeInjection
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile Waves
open MeasureTheory
open scoped Classical ENNReal BigOperators
noncomputable section

open CurrentShapeRestriction

/-- Literal equality of the two restrictions determines every off-source height. -/
theorem restrict_shape_injective {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) : Function.Injective (restrictShape C) := by
  intro h k he
  apply Subtype.ext
  apply Subtype.ext
  funext x
  apply Fin.ext
  have hxo : FiniteWired.site x.val ≠ FiniteWired.site o :=
    fun h => x.property (FiniteWired.site_injective N h)
  by_cases hx : FiniteWired.site x.val ∈ C.val
  · let y : {y : Site2 // y ∈ C.val.erase (FiniteWired.site o)} :=
      ⟨FiniteWired.site x.val, Finset.mem_erase.mpr ⟨hxo, hx⟩⟩
    have hh := restriction_inner C h y
    have hk := restriction_inner C k y
    rw [he] at hh
    rw [wired_height_off_vertex] at hh hk
    exact_mod_cast hh.trans hk.symm
  · let y : {y : Site2 // y ∈ boxSites N \ C.val} :=
      ⟨FiniteWired.site x.val, Finset.mem_sdiff.mpr ⟨site_mem_box x.val, hx⟩⟩
    have hh := restriction_outer C h y
    have hk := restriction_outer C k y
    rw [he] at hh
    rw [wired_height_off_vertex] at hh hk
    change (h.val.val x).val = (k.val.val x).val
    omega

theorem card_core_le_field_pairs {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) :
    Nat.card (CoreField o C.val) ≤ Nat.card (InnerAllowed o C) * Nat.card (OuterAllowed C) := by
  simpa only [Nat.card_prod] using
    Nat.card_le_card_of_injective (restrictShape C) (restrict_shape_injective C)

/-- Only the forward restrictions are followed by the two ordinary burning maps. -/
def restrictTrees {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (h : CoreField o C.val) : InnerTrees C × OuterTrees C :=
  (innerAllowedTreeEquiv C (restrictShape C h).1,
    outerAllowedTreeEquiv C (restrictShape C h).2)

theorem restrict_trees_injective {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) : Function.Injective (restrictTrees C) := by
  intro h k he
  apply restrict_shape_injective C
  exact Prod.ext ((innerAllowedTreeEquiv C).injective (congrArg Prod.fst he))
    ((outerAllowedTreeEquiv C).injective (congrArg Prod.snd he))

theorem card_core_le_tree_product {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) :
    Nat.card (CoreField o C.val) ≤ Nat.card (InnerTrees C) * Nat.card (OuterTrees C) := by
  simpa only [Nat.card_prod] using
    Nat.card_le_card_of_injective (restrictTrees C) (restrict_trees_injective C)

/-- Forward existence proves positivity without reconstructing a field. -/
theorem tree_cards_pos_of_core {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val) :
    0 < Fintype.card (InnerTrees C) ∧ 0 < Fintype.card (OuterTrees C) := by
  exact ⟨Fintype.card_pos_iff.mpr ⟨(restrictTrees C h).1⟩,
    Fintype.card_pos_iff.mpr ⟨(restrictTrees C h).2⟩⟩

/-- A marked vertex remains in the actual held burning on the inner graph. -/
def innerStopMeets {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (S : Finset Site2) (r : InnerGraphAllowed C) : Prop :=
  ∃ v ∈ Marked.markedVertices C S,
    v ∈ (Burning.heldBurning (inducedGraph (insideSupport C))
      (Finset.univ.erase (innerRoot C)) r.val (boundaryVertices C)).image Subtype.val

theorem card_held_missing_le_pairs {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (S : Finset Site2) (hS : S ⊆ C.val) :
    Nat.card {h : CoreField o C.val // ¬S ⊆ heldInterior h.val.val C} ≤
      Nat.card {r : InnerGraphAllowed C // innerStopMeets C S r} * Nat.card (OuterAllowed C) := by
  let f : {h : CoreField o C.val // ¬S ⊆ heldInterior h.val.val C} →
      {r : InnerGraphAllowed C // innerStopMeets C S r} × OuterAllowed C := fun h =>
    (⟨innerAllowedSourceEquiv C (restrictShape C h.val).1,
      (Marked.marked_omitted_iff_stop_meets C h.val S hS).mp h.property⟩,
      (restrictShape C h.val).2)
  have hi : Function.Injective f := by
    intro h k he
    apply Subtype.ext
    apply restrict_shape_injective C
    have ho : (restrictShape C h.val).2 = (restrictShape C k.val).2 :=
      congrArg (fun p : {r : InnerGraphAllowed C // innerStopMeets C S r} × OuterAllowed C =>
        p.2) he
    refine Prod.ext ((innerAllowedSourceEquiv C).injective ?_) ho
    exact congrArg (fun p => p.1.val) he
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hi

/-- The inner law uses the full recurrent inner carrier, independently of outer fields. -/
theorem inner_stop_law {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (C : PositiveCoreShape o S)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    letI : Nonempty (InnerGraphAllowed C.val) :=
      Nonempty.map (innerGraphTreeEquiv C.val).symm
        (Fintype.card_pos_iff.mp C.property.2.1)
    FiniteAvalanches.uniformMeasure (InnerGraphAllowed C.val)
      {r | innerStopMeets C.val (markedSites S) r} =
    (WiredTrees.graph N).componentLaw
      (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)
      ((WiredTrees.graph N).insideContact
        (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)) := by
  let dE : DecidableEq (InducedEdge (insideSupport C.val)) := inferInstance
  letI : Nonempty (InnerTrees C.val) := Fintype.card_pos_iff.mp C.property.2.1
  letI : Nonempty (InnerGraphAllowed C.val) :=
    Nonempty.map (innerGraphTreeEquiv C.val).symm inferInstance
  let nf : Nonempty (@FiniteAvalanches.Trees.Multigraph.SpanningTree
      (insideSupport C.val) (InducedEdge (insideSupport C.val)) _ _ dE
      (inducedGraph (insideSupport C.val))) :=
    Nonempty.map (innerInducedTreeEquiv C.val).symm inferInstance
  letI : LinearOrder (InducedEdge (insideSupport C.val)) :=
    LinearOrder.lift' (Fintype.equivFin (InducedEdge (insideSupport C.val)))
      (Fintype.equivFin (InducedEdge (insideSupport C.val))).injective
  letI : DecidableEq (InducedEdge (insideSupport C.val)) := LinearOrder.toDecidableEq
  letI : Nonempty (inducedGraph (insideSupport C.val)).SpanningTree := by
    exact Nonempty.map
      ((inducedGraph (insideSupport C.val)).spanningTreeDecidableEquiv dE
        LinearOrder.toDecidableEq) nf
  let event : Set (Finset (insideSupport C.val)) :=
    {T | ∃ v ∈ Marked.markedVertices C.val (markedSites S), v ∈ T}
  have he := congrArg (fun μ : Measure (Finset (insideSupport C.val)) => μ event)
    (Burning.canonical_uniform_held_past_law
      (inducedGraph (insideSupport C.val)) (innerRoot C.val) (boundaryVertices C.val))
  rw [Measure.map_apply (measurable_of_finite _) (by trivial),
    Measure.map_apply (measurable_of_finite _) (by trivial)] at he
  change FiniteAvalanches.uniformMeasure (InnerGraphAllowed C.val)
      {r | innerStopMeets C.val (markedSites S) r} =
    (inducedGraph (insideSupport C.val)).treeLaw
      {t | ∃ v ∈ Marked.markedVertices C.val (markedSites S),
        v ∈ Burning.canonicalPastUnion (inducedGraph (insideSupport C.val))
          (innerRoot C.val) t (boundaryVertices C.val)} at he
  have hb : {t : (inducedGraph (insideSupport C.val)).SpanningTree |
      ∃ v ∈ Marked.markedVertices C.val (markedSites S),
        v ∈ Burning.canonicalPastUnion (inducedGraph (insideSupport C.val))
          (innerRoot C.val) t (boundaryVertices C.val)} =
      {t | ∃ v : insideSupport C.val,
        Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C.val)).span t
          (Marked.markedVertices C.val (markedSites S))} := by
    ext t
    exact (Marked.past_meets_marked_iff_boundary_span C.val (markedSites S)
      (hN (Finset.mem_insert_self _ _)) t).trans
      (Marked.marked_boundary_contact_iff C.val (markedSites S) C.property.1 hN t)
  rw [hb] at he
  let A : Set (@FiniteAvalanches.Trees.Multigraph.SpanningTree
      (insideSupport C.val) (InducedEdge (insideSupport C.val)) _ _ dE
      (inducedGraph (insideSupport C.val))) :=
    {t | ∃ v : insideSupport C.val,
      Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
      v ∈ @FiniteAvalanches.Trees.Multigraph.span _ _ _ _ dE
        (inducedGraph (insideSupport C.val)) t (Marked.markedVertices C.val (markedSites S))}
  have hp := congrArg (fun μ => μ A)
    ((inducedGraph (insideSupport C.val)).tree_law_map_spanning_tree_decidable_equiv
      LinearOrder.toDecidableEq dE (nf := nf))
  rw [Measure.map_apply (measurable_of_finite _) (by trivial)] at hp
  have ha : ((inducedGraph (insideSupport C.val)).spanningTreeDecidableEquiv
      LinearOrder.toDecidableEq dE) ⁻¹' A =
      {t | ∃ v : insideSupport C.val,
        Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
        v ∈ (inducedGraph (insideSupport C.val)).span t
          (Marked.markedVertices C.val (markedSites S))} := by
    ext t
    change (∃ v : insideSupport C.val, Burning.degree (inducedGraph (insideSupport C.val)) v < 4 ∧
      v ∈ @FiniteAvalanches.Trees.Multigraph.span _ _ _ _ dE
        (inducedGraph (insideSupport C.val))
        ((inducedGraph (insideSupport C.val)).spanningTreeDecidableEquiv
          LinearOrder.toDecidableEq dE t) (Marked.markedVertices C.val (markedSites S))) ↔ _
    rw [FiniteAvalanches.Trees.Multigraph.spanning_tree_decidable_equiv_span]
    rfl
  rw [ha] at hp
  have ht := congrArg (fun μ => μ ((WiredTrees.graph N).insideContact
    (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)))
    (Marked.inner_induced_tree_law S (Marked.source_mem_of_marked_neighbors S hN) C)
  rw [Measure.map_apply (measurable_of_finite _) (by trivial),
    Marked.inside_contact_preimage S (Marked.source_mem_of_marked_neighbors S hN) C] at ht
  exact he.trans (hp.trans ht)

theorem card_held_missing_le_tree_weight {N : ℕ} {o : FiniteWired.Active N}
    (S : Finset (FiniteWired.Active N)) (C : PositiveCoreShape o S)
    (hN : insert (FiniteWired.site o) (nbrFinset (FiniteWired.site o)) ⊆ markedSites S) :
    (Nat.card {h : CoreField o C.val.val //
      ¬markedSites S ⊆ heldInterior h.val.val C.val} : ℝ) ≤
      (Fintype.card (InnerTrees C.val) : ℝ) * Fintype.card (OuterTrees C.val) *
        ((WiredTrees.graph N).componentLaw
          (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)).real
          ((WiredTrees.graph N).insideContact
            (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)) := by
  letI : Nonempty (InnerGraphAllowed C.val) :=
    Nonempty.map (innerGraphTreeEquiv C.val).symm
      (Fintype.card_pos_iff.mp C.property.2.1)
  have he := congrArg ENNReal.toReal (inner_stop_law S C hN)
  change (FiniteAvalanches.uniformMeasure (InnerGraphAllowed C.val)).real
      {r | innerStopMeets C.val (markedSites S) r} = _ at he
  have hci : Nat.card (InnerGraphAllowed C.val) = Fintype.card (InnerTrees C.val) :=
    (Nat.card_congr (innerGraphTreeEquiv C.val)).trans Nat.card_eq_fintype_card
  rw [FiniteAvalanches.uniformMeasure_real_apply, hci] at he
  have hpos : (Fintype.card (InnerTrees C.val) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt C.property.2.1
  have hc := (div_eq_iff hpos).mp he
  change (Nat.card {r : InnerGraphAllowed C.val // innerStopMeets C.val (markedSites S) r} : ℝ) =
    ((WiredTrees.graph N).componentLaw
      (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)).real
      ((WiredTrees.graph N).insideContact
        (positiveSupportEquiv S (Marked.source_mem_of_marked_neighbors S hN) C)) *
      Fintype.card (InnerTrees C.val) at hc
  have ho : Nat.card (OuterAllowed C.val) = Fintype.card (OuterTrees C.val) := by
    rw [Nat.card_congr (outerAllowedTreeEquiv C.val), Nat.card_eq_fintype_card]
  have hi := card_held_missing_le_pairs C.val (markedSites S) C.property.1
  calc
    _ ≤ (Nat.card {r : InnerGraphAllowed C.val //
          innerStopMeets C.val (markedSites S) r} : ℝ) * Nat.card (OuterAllowed C.val) := by
      exact_mod_cast hi
    _ = _ := by rw [hc, ho]; ring

/-- Partition into positive tree shapes uses forward existence only; empty fibers vanish. -/
theorem sum_held_omissions_eq_positive {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset (FiniteWired.Active N)) :
    (∑ g : Punctured N o,
      (if markedSites S ⊆ core g.val ∧
        ¬markedSites S ⊆ heldInterior g.val (coreShape g.val) then 1 else 0 : ℝ)) =
      ∑ C : PositiveCoreShape o S,
        (Nat.card {h : CoreField o C.val.val //
          ¬markedSites S ⊆ heldInterior h.val.val C.val} : ℝ) := by
  rw [sum_held_omissions_by_core]
  apply Finset.sum_congr_set {C : ComponentShape o | markedSites S ⊆ C.val ∧
    0 < Fintype.card (InnerTrees C) ∧ 0 < Fintype.card (OuterTrees C)}
  · intro C hC
    rw [if_pos hC.1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.sum_boole _ _
  · intro C hC
    by_cases hS : markedSites S ⊆ C.val
    · rw [if_pos hS]
      letI : IsEmpty (CoreField o C.val) := ⟨fun h => hC ⟨hS, tree_cards_pos_of_core C h⟩⟩
      exact Finset.sum_eq_zero (fun h _ => isEmptyElim h)
    · exact if_neg hS

end
end FiniteAvalanches.Sandpile.Components.ShapeInjection
