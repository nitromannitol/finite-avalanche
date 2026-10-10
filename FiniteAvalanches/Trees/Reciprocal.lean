module

public import FiniteAvalanches.Trees.Partition

@[expose] public section

/-! Global reciprocal occupation on the actual ordinary-tree measure, with a zero root branch. -/
open scoped Classical
open MeasureTheory
namespace FiniteAvalanches.Trees.Multigraph
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E] (G : Multigraph V E)

/-- Literal reciprocal, with the source's zero branch when the ancestor is the root. -/
noncomputable def reciprocalWeight (r : V) (S : Set V) (hS : S.Nonempty)
    (c : ℝ) (u : G.SpanningTree) : ℝ :=
  if G.ancestorOf u r S hS ≠ r then
    c / (G.admissibleEdges (G.descendants u r (G.ancestorOf u r S hS)) (G.span u S)).card
  else 0

/-- Boundary contact event on the actual inside-tree carrier. -/
noncomputable def insideContact {r : V} {S : Set V} (C : G.PositiveSupport r S) :
    Set (G.ComponentTree C.val) :=
  {t | (G.admissibleEdges C.val (G.componentSpan t S C.property.1)).Nonempty}

noncomputable def componentLaw {r : V} {S : Set V} (C : G.PositiveSupport r S) :
    Measure (G.ComponentTree C.val) := by
  letI : Nonempty (G.ComponentTree C.val) := Fintype.card_pos_iff.mp C.property.2.2.1
  exact FiniteAvalanches.uniformMeasure (G.ComponentTree C.val)

instance componentLaw_probability {r : V} {S : Set V} (C : G.PositiveSupport r S) :
    IsProbabilityMeasure (G.componentLaw C) := by
  letI : Nonempty (G.ComponentTree C.val) := Fintype.card_pos_iff.mp C.property.2.2.1
  exact FiniteAvalanches.uniformMeasure_probability _

theorem componentLaw_real_contact {r : V} {S : Set V} (C : G.PositiveSupport r S) :
    (G.componentLaw C).real (G.insideContact C) =
      (Nat.card (G.insideContact C) : ℝ) / Fintype.card (G.ComponentTree C.val) := by
  letI : Nonempty (G.ComponentTree C.val) := Fintype.card_pos_iff.mp C.property.2.2.1
  rw [show G.componentLaw C = FiniteAvalanches.uniformMeasure (G.ComponentTree C.val)
    from rfl, FiniteAvalanches.uniformMeasure_real_apply]
  simp only [Nat.card_eq_fintype_card]

/-- Sum of all completions, partitioned by their derived support and inside restriction. -/
theorem sum_reciprocalWeight (r : V) (S : Set V) (hS : S.Nonempty) (c : ℝ) :
    (∑ u : G.SpanningTree, G.reciprocalWeight r S hS c u) =
      ∑ C : G.PositiveSupport r S, ∑ t : G.ComponentTree C.val,
        if (G.admissibleEdges C.val (G.componentSpan t S C.property.1)).Nonempty then
          c * Fintype.card (G.ComponentTree C.valᶜ) else 0 := by
  have ha : (∑ u : G.SpanningTree, G.reciprocalWeight r S hS c u) =
      ∑ u : G.ActiveAncestorTree r S hS,
        c / (G.admissibleEdges (G.descendants u.val r (G.ancestorOf u.val r S hS))
          (G.span u.val S)).card := by
    apply Finset.sum_congr_set {u : G.SpanningTree | G.ancestorOf u r S hS ≠ r}
    · intro u hu
      change G.ancestorOf u r S hS ≠ r at hu
      rw [reciprocalWeight, if_pos hu]
    · intro u hu
      change ¬G.ancestorOf u r S hS ≠ r at hu
      rw [reciprocalWeight, if_neg hu]
  rw [ha, ← Equiv.sum_comp (G.treeFiberEquiv r S hS)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro C _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  change (∑ u : G.AncestorPastTree C.val S r hS t,
    c / (G.admissibleEdges (G.descendants u.val r (G.ancestorOf u.val r S hS))
      (G.span u.val S)).card) = _
  have he : (∑ u : G.AncestorPastTree C.val S r hS t,
      c / (G.admissibleEdges (G.descendants u.val r (G.ancestorOf u.val r S hS))
        (G.span u.val S)).card) =
      ∑ u : G.AncestorPastTree C.val S r hS t,
        c / (G.admissibleEdges C.val (G.span u.val S)).card := by
    apply Finset.sum_congr rfl
    intro u _
    rw [u.property.1]
  rw [he]
  exact G.reciprocal_ancestorPastTree r C.property.2.1 hS t C.property.1 c

/-- The common mass is explicit, and component contact uses its actual probability measure. -/
theorem sum_reciprocalWeight_eq_componentLaw (r : V) (S : Set V)
    (hS : S.Nonempty) (c : ℝ) :
    (∑ u : G.SpanningTree, G.reciprocalWeight r S hS c u) =
      ∑ C : G.PositiveSupport r S,
        c * Fintype.card (G.ComponentTree C.val) * Fintype.card (G.ComponentTree C.valᶜ) *
          (G.componentLaw C).real (G.insideContact C) := by
  rw [G.sum_reciprocalWeight r S hS c]
  apply Finset.sum_congr rfl
  intro C _
  have hs : (∑ t : G.ComponentTree C.val,
      if (G.admissibleEdges C.val (G.componentSpan t S C.property.1)).Nonempty then
        c * Fintype.card (G.ComponentTree C.valᶜ) else 0) =
      ∑ _t : G.insideContact C, c * Fintype.card (G.ComponentTree C.valᶜ) := by
    apply Finset.sum_congr_set (G.insideContact C)
    · intro t ht
      simp only [insideContact, Set.mem_setOf_eq] at ht
      rw [if_pos ht]
    · intro t ht
      simp only [insideContact, Set.mem_setOf_eq] at ht
      rw [if_neg ht]
  rw [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, G.componentLaw_real_contact C]
  have hc : (Fintype.card (G.ComponentTree C.val) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt C.property.2.2.1)
  field_simp

/-- Expectation under the real uniform tree law, preserving mass tau^-1 and the root zero case. -/
theorem integral_reciprocalWeight [Nonempty G.SpanningTree]
    (r : V) (S : Set V) (hS : S.Nonempty) :
    (∫ u, G.reciprocalWeight r S hS 1 u ∂G.treeLaw) =
      ∑ C : G.PositiveSupport r S,
        ((Fintype.card (G.ComponentTree C.val) : ℝ) *
          Fintype.card (G.ComponentTree C.valᶜ) / Fintype.card G.SpanningTree) *
            (G.componentLaw C).real (G.insideContact C) := by
  have hm : (∑ u : G.SpanningTree,
      G.reciprocalWeight r S hS (1 / (Fintype.card G.SpanningTree : ℝ)) u) =
      (∑ u : G.SpanningTree, G.reciprocalWeight r S hS 1 u) /
        Fintype.card G.SpanningTree := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    unfold reciprocalWeight
    split <;> ring
  change (∫ u, G.reciprocalWeight r S hS 1 u
    ∂FiniteAvalanches.uniformMeasure G.SpanningTree) = _
  rw [FiniteAvalanches.integral_uniformMeasure, Nat.card_eq_fintype_card, ← hm,
    G.sum_reciprocalWeight_eq_componentLaw r S hS]
  apply Finset.sum_congr rfl
  intro C _
  ring

end FiniteAvalanches.Trees.Multigraph
