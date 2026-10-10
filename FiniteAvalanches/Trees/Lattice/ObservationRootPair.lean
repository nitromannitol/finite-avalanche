import FiniteAvalanches.Trees.OrderedConnectorObservation
import FiniteAvalanches.Wilson.Lattice.WiredForestLaw

/-! The actual finite observation defines the source's two lattice root sets:
the marked span and the strict ancestor tail together with the whole exterior. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

theorem wiredSite_active (N : ℕ) (x : FiniteWired.Active N) :
    wiredSite N (FiniteWired.site x) = some x := by
  have hx : FiniteWired.inBox N (FiniteWired.site x) := fun i => (x i).property
  rw [wiredSite, dif_pos hx]
  congr 1

theorem sink_not_mem_observed_span (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    none ∉ (graph N).span t S :=
  Set.disjoint_left.mp ((graph N).orderedAncestorTail_disjoint_span t none S hS)
    ((graph N).root_mem_orderedAncestorTail t none S hS hne)

/-- The literal inverse images under wiring, with all exterior sites retained. -/
def observationRootPair (N : ℕ) (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) : RootPair where
  zero := {x | wiredSite N x ∈ (graph N).span t S}
  one := {x | wiredSite N x ∈
    (graph N).connectorRootSupport t none S hS \ (graph N).span t S}
  disjoint := Set.disjoint_left.mpr (fun _ hx hΓ => hΓ.2 hx)
  zero_nonempty := by
    have ha : (graph N).ancestorOf t none S hS ∈ (graph N).span t S :=
      RootedPaths.commonAncestor_mem_connectingSubtree
        ((graph N).toSimple_isTree t.property) none S hS
    cases hval : (graph N).ancestorOf t none S hS with
    | none => exact (hne hval).elim
    | some a =>
      refine ⟨FiniteWired.site a, ?_⟩
      change wiredSite N (FiniteWired.site a) ∈ (graph N).span t S
      rw [wiredSite_active, ← hval]
      exact ha
  one_nonempty := by
    let x : Site 2 := fun i => if i = 0 then (N : ℤ) + 1 else 0
    have hx : ¬FiniteWired.inBox N x := by
      intro h
      have hh := (h 0).2
      change (N : ℤ) + 1 ≤ N at hh
      omega
    refine ⟨x, ?_⟩
    change wiredSite N x ∈ (graph N).connectorRootSupport t none S hS \ (graph N).span t S
    rw [wiredSite, dif_neg hx]
    exact ⟨Or.inr (SimpleGraph.Walk.end_mem_support _),
      sink_not_mem_observed_span N S hS t hne⟩

/-- On the source nonsink event, zero roots lie entirely in the original box. -/
theorem observationRootPair_zero_inBox (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) {x : Site 2}
    (hx : x ∈ (observationRootPair N S hS t hne).zero) : FiniteWired.inBox N x := by
  by_contra ho
  change wiredSite N x ∈ (graph N).span t S at hx
  rw [wiredSite, dif_neg ho] at hx
  exact sink_not_mem_observed_span N S hS t hne hx

/-- Every exterior site is a one root, without selecting a finite exterior subset. -/
theorem observationRootPair_exterior_one (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) {x : Site 2}
    (hx : ¬FiniteWired.inBox N x) : x ∈ (observationRootPair N S hS t hne).one := by
  change wiredSite N x ∈ (graph N).connectorRootSupport t none S hS \ (graph N).span t S
  rw [wiredSite, dif_neg hx]
  exact ⟨Or.inr (SimpleGraph.Walk.end_mem_support _), sink_not_mem_observed_span N S hS t hne⟩

/-- The one-root set is exactly the whole exterior and the strict tail inside. -/
theorem observationRootPair_one_eq_exterior_union_tail (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    (observationRootPair N S hS t hne).one =
      {x | ¬FiniteWired.inBox N x} ∪
        {x | FiniteWired.inBox N x ∧ wiredSite N x ∈ (graph N).orderedAncestorTail t none S hS} := by
  ext x
  change (wiredSite N x ∈ (graph N).connectorRootSupport t none S hS \ (graph N).span t S) ↔ _
  rw [(graph N).connectorRootSupport_sdiff_span_eq_tail]
  by_cases hx : FiniteWired.inBox N x
  · simp only [Set.mem_setOf_eq, Set.mem_union, hx, not_true_eq_false, false_or, true_and]
  · simp only [Set.mem_setOf_eq, Set.mem_union, hx, not_false_eq_true, true_or]
    rw [wiredSite, dif_neg hx]
    exact iff_true_intro ((graph N).root_mem_orderedAncestorTail t none S hS hne)

theorem observationRootPair_wiredZero (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    wiredZero (observationRootPair N S hS t hne) N = (graph N).span t S := by
  ext v
  cases v with
  | none =>
    change False ↔ none ∈ (graph N).span t S
    exact (iff_false_intro (sink_not_mem_observed_span N S hS t hne)).symm
  | some x =>
    change (wiredSite N (FiniteWired.site x) ∈ (graph N).span t S) ↔ _
    rw [wiredSite_active]

theorem observationRootPair_wiredOne (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    wiredOne (observationRootPair N S hS t hne) N =
      (graph N).connectorRootSupport t none S hS \ (graph N).span t S := by
  ext v
  cases v with
  | none =>
    change True ↔ none ∈ (graph N).connectorRootSupport t none S hS \ (graph N).span t S
    constructor
    · intro _
      exact ⟨Or.inr (SimpleGraph.Walk.end_mem_support _), sink_not_mem_observed_span N S hS t hne⟩
    · intro _
      trivial
  | some x =>
    change (wiredSite N (FiniteWired.site x) ∈
      (graph N).connectorRootSupport t none S hS \ (graph N).span t S) ↔ _
    rw [wiredSite_active]

theorem observationRootPair_wiredRoots (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    (wiredRoots (observationRootPair N S hS t hne) N).val =
      (graph N).connectorRootSupport t none S hS := by
  change wiredZero _ N ∪ wiredOne _ N = _
  rw [observationRootPair_wiredZero, observationRootPair_wiredOne]
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact hx.1
  · intro hx
    by_cases hxK : x ∈ (graph N).span t S
    · exact Or.inl hxK
    · exact Or.inr ⟨hx, hxK⟩

end
end FiniteAvalanches.ConditioningConsumer
