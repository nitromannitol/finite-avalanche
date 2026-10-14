import FiniteAvalanches.Trees.CutComponents
import FiniteAvalanches.Paper.Current.Outflow
import FiniteAvalanches.Sandpile.Waves.ReciprocalBound

/-! The original punctured carrier is put in bijection with all source/sink
component-tree pairs. Fixed-copy insertion retains its original normalization. -/
namespace FiniteAvalanches.Sandpile.Components.CurrentCounting
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Waves
open FiniteAvalanches.Trees.Multigraph MeasureTheory
open FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Sandpile.Components.CurrentShapeRestriction
open scoped Classical ENNReal
noncomputable section

/-- Full forest carrier, with disconnected supports retained as empty fibers. -/
def puncturedForestEquiv {N : ℕ} (o : FiniteWired.Active N) :
    Punctured N o ≃ (D : SourceCutSupport (some o) (none : FiniteWired.Vertex N)) ×
      ((WiredTrees.graph N).ComponentTree D.val ×
        (WiredTrees.graph N).ComponentTree D.valᶜ) :=
  (coreFieldPartition o).trans (Equiv.sigmaCongr (shapeSupportEquiv o) fun C =>
    (sourceTreeEquiv C).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.cast
      (congrArg ((WiredTrees.graph N).ComponentTree) (inside_complement C).symm))))

theorem punctured_forest_support {N : ℕ} (o : FiniteWired.Active N) (g : Punctured N o) :
    (puncturedForestEquiv o g).1.val = insideSupport (coreShape g.val) := rfl

private def crossingSigmaEquiv {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : FiniteAvalanches.Trees.Multigraph V E) (o r : V) (f : E) :
    {p : (D : SourceCutSupport o r) × (G.ComponentTree D.val × G.ComponentTree D.valᶜ) //
      G.crosses p.1.val f} ≃ G.FixedEdgeForest o r f where
  toFun p := ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
  invFun p := ⟨⟨p.1, p.2.val⟩, p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A fixed original edge joins exactly the punctured fields whose actual core it crosses. -/
def crossingCoreTreeEquiv {N : ℕ} (o : FiniteWired.Active N) (f : FiniteWired.Edge N) :
    {g : Punctured N o // (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f} ≃
      (WiredTrees.graph N).SeparatingTree (some o) none f :=
  ((puncturedForestEquiv o).subtypeEquiv (fun _ => Iff.rfl)).trans
    ((crossingSigmaEquiv (WiredTrees.graph N) (some o) none f).trans
      ((WiredTrees.graph N).fixedEdgeForestEquiv (some o) none f))

/-- The cut component is the full original core support, not a selected subcomponent. -/
theorem crossing_core_component {N : ℕ} (o : FiniteWired.Active N)
    (f : FiniteWired.Edge N)
    (g : {g : Punctured N o // (WiredTrees.graph N).crosses
      (insideSupport (coreShape g.val)) f}) :
    (WiredTrees.graph N).componentAfter (crossingCoreTreeEquiv o f g).val.val f (some o) =
      insideSupport (coreShape g.val.val) :=
  (WiredTrees.graph N).componentAfter_insertFixedEdge (some o) none f _

/-- Fixed-copy insertion transports every support event; both denominators are tau_N. -/
theorem crossing_core_mass_eq_tree_cut {N : ℕ} (o : FiniteWired.Active N)
    (f : FiniteWired.Edge N) (A : Set (Set (FiniteWired.Vertex N))) :
    (puncturedCountingMeasure o).real {g |
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
      insideSupport (coreShape g.val) ∈ A} =
    (WiredTrees.law N).real {t |
      f ∈ t.val ∧ ¬(WiredTrees.graph N).reaches (t.val.erase f) (some o) none ∧
      (WiredTrees.graph N).componentAfter t.val f (some o) ∈ A} := by
  let e : {g : {g : Punctured N o //
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f} //
      insideSupport (coreShape g.val.val) ∈ A} ≃
    {t : (WiredTrees.graph N).SeparatingTree (some o) none f //
      (WiredTrees.graph N).componentAfter t.val.val f (some o) ∈ A} :=
    (crossingCoreTreeEquiv o f).subtypeEquiv (fun g => by
    rw [crossing_core_component])
  let a : {g : Punctured N o //
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
      insideSupport (coreShape g.val) ∈ A} ≃
    {g : {g : Punctured N o //
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f} //
      insideSupport (coreShape g.val.val) ∈ A} :=
    ⟨fun g => ⟨⟨g.val, g.property.1⟩, g.property.2⟩,
      fun g => ⟨g.val.val, g.val.property, g.property⟩,
      fun _ => rfl, fun _ => rfl⟩
  let b : {t : (WiredTrees.graph N).SpanningTree //
      f ∈ t.val ∧ ¬(WiredTrees.graph N).reaches (t.val.erase f) (some o) none ∧
      (WiredTrees.graph N).componentAfter t.val f (some o) ∈ A} ≃
    {t : (WiredTrees.graph N).SeparatingTree (some o) none f //
      (WiredTrees.graph N).componentAfter t.val.val f (some o) ∈ A} :=
    ⟨fun t => ⟨⟨t.val, t.property.1, t.property.2.1⟩, t.property.2.2⟩,
      fun t => ⟨t.val.val, t.val.property.1, t.val.property.2, t.property⟩,
      fun _ => rfl, fun _ => rfl⟩
  have hc : Nat.card ({g : Punctured N o |
      (WiredTrees.graph N).crosses (insideSupport (coreShape g.val)) f ∧
      insideSupport (coreShape g.val) ∈ A} : Set (Punctured N o)) =
    Nat.card ({t : (WiredTrees.graph N).SpanningTree |
      f ∈ t.val ∧ ¬(WiredTrees.graph N).reaches (t.val.erase f) (some o) none ∧
      (WiredTrees.graph N).componentAfter t.val f (some o) ∈ A} :
        Set (WiredTrees.graph N).SpanningTree) :=
    Nat.card_congr (a.trans (e.trans b.symm))
  change (puncturedCountingMeasure o _).toReal = _
  rw [punctured_counting_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  rw [card_original_recurrent_eq_treeCount]
  change _ = ((WiredTrees.graph N).treeLaw).real _
  rw [(WiredTrees.graph N).treeLaw_real_eq_counting]
  change _ = (Nat.card _ : ℝ) / Nat.card (WiredTrees.graph N).SpanningTree
  rw [hc, Nat.card_eq_fintype_card (α := (WiredTrees.graph N).SpanningTree)]
  rfl

end
end FiniteAvalanches.Sandpile.Components.CurrentCounting
