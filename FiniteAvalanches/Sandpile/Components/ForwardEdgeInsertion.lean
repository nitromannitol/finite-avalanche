import FiniteAvalanches.Sandpile.Components.ShapeInjection
import FiniteAvalanches.Sandpile.Components.CurrentEdgeInsertion

/-! Forward restriction followed by insertion of one original crossing copy. -/
namespace FiniteAvalanches.Sandpile.Components.CurrentCounting.Forward
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves
open FiniteAvalanches.Trees.Multigraph MeasureTheory
open FiniteAvalanches.Sandpile.Components
open scoped Classical ENNReal
noncomputable section

/-- Both restricted trees, with only the literal complement carrier transported. -/
def shapeTreePair {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (h : CoreField o C.val) :
    (WiredTrees.graph N).ComponentTree (insideSupport C) ×
      (WiredTrees.graph N).ComponentTree (insideSupport C)ᶜ :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.cast
    (congrArg ((WiredTrees.graph N).ComponentTree) (inside_complement C).symm)))
    (ShapeInjection.restrictTrees C h)

theorem shape_tree_pair_injective {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) : Function.Injective (shapeTreePair C) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.cast
    (congrArg ((WiredTrees.graph N).ComponentTree) (inside_complement C).symm))).injective.comp
      (ShapeInjection.restrict_trees_injective C)

/-- Every actual field supplies its whole core support and its forward restricted trees. -/
def forwardForest {N : ℕ} (o : FiniteWired.Active N) (g : Punctured N o) :
    (D : SourceCutSupport (some o) (none : FiniteWired.Vertex N)) ×
      ((WiredTrees.graph N).ComponentTree D.val ×
        (WiredTrees.graph N).ComponentTree D.valᶜ) :=
  Sigma.map (shapeSupportEquiv o) (fun C => shapeTreePair C) (coreFieldPartition o g)

theorem forward_forest_support {N : ℕ} (o : FiniteWired.Active N) (g : Punctured N o) :
    (forwardForest o g).1.val = insideSupport (coreShape g.val) := rfl

theorem forward_forest_injective {N : ℕ} (o : FiniteWired.Active N) :
    Function.Injective (forwardForest o) :=
  ((shapeSupportEquiv o).injective.sigma_map (fun C => shape_tree_pair_injective C)).comp
    (coreFieldPartition o).injective

/-- The same fixed original copy crosses the whole actual source support. -/
def crossingForest {N : ℕ} (o : FiniteWired.Active N) (f : FiniteWired.Edge N)
    (g : {g : Punctured N o //
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f}) :
    (WiredTrees.graph N).FixedEdgeForest (some o) none f :=
  ⟨(forwardForest o g.val).1, ⟨(forwardForest o g.val).2, g.property⟩⟩

/-- Insert only the specified crossing copy into the two actual restricted edge sets. -/
def crossingTree {N : ℕ} (o : FiniteWired.Active N) (f : FiniteWired.Edge N)
    (g : {g : Punctured N o //
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f}) :
    (WiredTrees.graph N).SeparatingTree (some o) none f :=
  (WiredTrees.graph N).insertFixedEdge (some o) none f (crossingForest o f g)

/-- Deleting the inserted copy recovers every vertex of the original core support. -/
theorem crossing_tree_component {N : ℕ} (o : FiniteWired.Active N)
    (f : FiniteWired.Edge N)
    (g : {g : Punctured N o //
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f}) :
    (WiredTrees.graph N).componentAfter (crossingTree o f g).val.val f (some o) =
      insideSupport (coreShape g.val.val) :=
  (WiredTrees.graph N).componentAfter_insertFixedEdge (some o) none f _

/-- Fixed-copy deletion recovers the support and both trees, then the literal field. -/
theorem crossing_tree_injective {N : ℕ} (o : FiniteWired.Active N)
    (f : FiniteWired.Edge N) : Function.Injective (crossingTree o f) := by
  intro g h he
  apply Subtype.ext
  apply forward_forest_injective o
  have hf := (WiredTrees.graph N).insertFixedEdge_injective (some o) none f he
  exact congrArg (fun p : (WiredTrees.graph N).FixedEdgeForest (some o) none f =>
    (⟨p.1, p.2.val⟩ :
      (D : SourceCutSupport (some o) (none : FiniteWired.Vertex N)) ×
        ((WiredTrees.graph N).ComponentTree D.val ×
          (WiredTrees.graph N).ComponentTree D.valᶜ))) hf

/-- Arbitrary support events are preserved by the actual crossing-field injection. -/
def crossingEventMap {N : ℕ} (o : FiniteWired.Active N) (f : FiniteWired.Edge N)
    (A : Set (Set (FiniteWired.Vertex N)))
    (g : {g : Punctured N o //
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
      insideSupport (coreShape g.val) ∈ A}) :
    {t : (WiredTrees.graph N).SpanningTree //
      f ∈ t.val ∧ ¬(WiredTrees.graph N).reaches (t.val.erase f) (some o) none ∧
      (WiredTrees.graph N).componentAfter t.val f (some o) ∈ A} := by
  let t := crossingTree o f ⟨g.val, g.property.1⟩
  refine ⟨t.val, t.property.1, t.property.2, ?_⟩
  rw [crossing_tree_component]
  exact g.property.2

theorem crossing_event_map_injective {N : ℕ} (o : FiniteWired.Active N)
    (f : FiniteWired.Edge N) (A : Set (Set (FiniteWired.Vertex N))) :
    Function.Injective (crossingEventMap o f A) := by
  intro g h he
  apply Subtype.ext
  have hv : (crossingTree o f ⟨g.val, g.property.1⟩).val =
      (crossingTree o f ⟨h.val, h.property.1⟩).val :=
    congrArg (fun t : {t : (WiredTrees.graph N).SpanningTree //
      f ∈ t.val ∧ ¬(WiredTrees.graph N).reaches (t.val.erase f) (some o) none ∧
      (WiredTrees.graph N).componentAfter t.val f (some o) ∈ A} => t.val) he
  have ht : crossingTree o f ⟨g.val, g.property.1⟩ =
      crossingTree o f ⟨h.val, h.property.1⟩ :=
    Subtype.ext hv
  exact congrArg (fun q : {g : Punctured N o //
    (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f} => q.val)
    (crossing_tree_injective o f ht)

/-- Both finite event counts retain the same positive original tree denominator. -/
theorem crossing_core_mass_le_tree_cut {N : ℕ} (o : FiniteWired.Active N)
    (f : FiniteWired.Edge N) (A : Set (Set (FiniteWired.Vertex N))) :
    (puncturedCountingMeasure o).real {g |
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
      insideSupport (coreShape g.val) ∈ A} ≤
    (WiredTrees.law N).real {t |
      f ∈ t.val ∧ ¬(WiredTrees.graph N).reaches (t.val.erase f) (some o) none ∧
      (WiredTrees.graph N).componentAfter t.val f (some o) ∈ A} := by
  have hc := Nat.card_le_card_of_injective (crossingEventMap o f A)
    (crossing_event_map_injective o f A)
  change (puncturedCountingMeasure o _).toReal ≤ _
  rw [punctured_counting_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  rw [card_original_recurrent_eq_treeCount]
  change _ ≤ ((WiredTrees.graph N).treeLaw).real _
  rw [(WiredTrees.graph N).treeLaw_real_eq_counting]
  change _ ≤ (Nat.card _ : ℝ) / Nat.card (WiredTrees.graph N).SpanningTree
  rw [Nat.card_eq_fintype_card (α := (WiredTrees.graph N).SpanningTree)]
  have hτ : (0 : ℝ) < Fintype.card (WiredTrees.graph N).SpanningTree := by
    exact_mod_cast Fintype.card_pos
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) hτ.le

end
end FiniteAvalanches.Sandpile.Components.CurrentCounting.Forward
