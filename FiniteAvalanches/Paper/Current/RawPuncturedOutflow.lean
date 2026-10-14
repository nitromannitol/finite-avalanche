import FiniteAvalanches.Paper.Current.RawPuncturedWave
import FiniteAvalanches.Paper.Current.GuardedOutflow
import FiniteAvalanches.Paper.Current.InjectionOutflow

/-! Literal raw recurrent shape restriction/product count and the incoming
fv:outflow bound, by actual carrier and observable transports. -/
namespace FiniteAvalanches.Paper.RawPunctured
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Sandpile.Waves FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Sandpile.SourceCounting MeasureTheory
open TreeMeasurability11.CurrentDomain
open scoped Classical ENNReal
noncomputable section

abbrev ShapeState {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  {η : State o // W η = C.val}

def shapeEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    ShapeState C ≃ CoreField o C.val :=
  Equiv.subtypeEquiv (stateEquiv o) (fun η => by rw [W_eq_core]; rfl)

def shapeFieldEquiv {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    ShapeState C ≃ InnerAllowed o C × OuterAllowed C :=
  (shapeEquiv C).trans (CurrentShapeRestriction.sourceFieldEquiv C)

theorem shape_restriction_inner {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (η : ShapeState C) (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) :
    extension (-1) η.val x.val = (((shapeFieldEquiv C η).1.val x).val : ℤ) := by
  rw [extension_eq_wired]
  exact CurrentShapeRestriction.restriction_inner C (shapeEquiv C η) x

theorem shape_restriction_outer {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (η : ShapeState C) (x : {x : Site2 // x ∈ boxSites N \ C.val}) :
    extension (-1) η.val x.val - (degree C.val x.val : ℤ) =
      (((shapeFieldEquiv C η).2.val x).val : ℤ) := by
  rw [extension_eq_wired]
  exact CurrentShapeRestriction.restriction_outer C (shapeEquiv C η) x

theorem shape_reconstruction_inner {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (r : InnerAllowed o C × OuterAllowed C)
    (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) :
    extension (-1) ((shapeFieldEquiv C).symm r).val x.val = ((r.1.val x).val : ℤ) := by
  rw [extension_eq_wired]
  change wiredHeight (-1) (toOld ((shapeFieldEquiv C).symm r).val).val x.val = _
  have he := congrArg (fun z : CoreField o C.val => z.val.val)
    ((shapeEquiv C).apply_symm_apply (CurrentShapeRestriction.reconstructShape C r))
  change (toOld ((shapeFieldEquiv C).symm r).val).val =
    (CurrentShapeRestriction.reconstructShape C r).val.val at he
  rw [he]
  exact CurrentShapeRestriction.reconstruction_inner C r x

theorem shape_reconstruction_outer {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (r : InnerAllowed o C × OuterAllowed C)
    (x : {x : Site2 // x ∈ boxSites N \ C.val}) :
    extension (-1) ((shapeFieldEquiv C).symm r).val x.val =
      ((r.2.val x).val : ℤ) + (degree C.val x.val : ℤ) := by
  rw [extension_eq_wired]
  change wiredHeight (-1) (toOld ((shapeFieldEquiv C).symm r).val).val x.val = _
  have he := congrArg (fun z : CoreField o C.val => z.val.val)
    ((shapeEquiv C).apply_symm_apply (CurrentShapeRestriction.reconstructShape C r))
  change (toOld ((shapeFieldEquiv C).symm r).val).val =
    (CurrentShapeRestriction.reconstructShape C r).val.val at he
  rw [he]
  exact CurrentShapeRestriction.reconstruction_outer C r x

theorem shape_tree_product {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Nat.card (ShapeState C) = Nat.card (InnerTrees C) * Nat.card (OuterTrees C) := by
  rw [Nat.card_congr (shapeEquiv C), CurrentShapeRestriction.card_source_tree_product C]

def outflowEventEquiv {N : ℕ} {o : FiniteWired.Active N} (S : Finset Site2) :
    {η : State o // S ⊆ W η ∧ ¬S ⊆ W (U η)} ≃
      {g : Punctured N o // S ⊆ core g.val ∧ ¬S ⊆ core (forward g).val} :=
  Equiv.subtypeEquiv (stateEquiv o) (fun η => by
    rw [W_eq_core, W_eq_core, to_old_U]; rfl)

theorem outflow_count_transport {N : ℕ} {o : FiniteWired.Active N} (S : Finset Site2) :
    Nat.card {η : State o // S ⊆ W η ∧ ¬S ⊆ W (U η)} =
      Nat.card {g : Punctured N o // S ⊆ core g.val ∧ ¬S ⊆ core (forward g).val} :=
  Nat.card_congr (outflowEventEquiv S)

/-- Incoming fv:outflow: only the source volume/marks standing binders remain. -/
theorem outflow {N r : ℕ} (hr : 2 ≤ r) (hrN : r ≤ N) :
    (Nat.card {η : State (origin N) // sourceMarks r ⊆ W η ∧
      ¬sourceMarks r ⊆ W (U η)} : ℝ) ≤
      (WiredTrees.treeCount N : ℝ) *
        ∫ t, sourceFiniteReciprocal N (sourceMarks r) (Finset.insert_nonempty _ _)
          (fun _ hx => sourceMarks_inBox hr hrN hx) t ∂WiredTrees.law N := by
  rw [outflow_count_transport]
  exact FiniteAvalanches.Paper.InjectionOutflow.outflow_le_guarded_source_reciprocal hr hrN

instance oldPuncturedNonempty {N : ℕ} (o : FiniteWired.Active N) : Nonempty (Punctured N o) :=
  Nonempty.map (stateEquiv o) inferInstance

theorem punctured_law_transport {N : ℕ} (o : FiniteWired.Active N) :
    Measure.map (stateEquiv o) (RawInteger.gammaIntegerRecurrentLaw (volume o)) =
      FiniteAvalanches.uniformMeasure (Punctured N o) := by
  exact FiniteAvalanches.uniform_measure_map_equiv (stateEquiv o)

end
end FiniteAvalanches.Paper.RawPunctured
