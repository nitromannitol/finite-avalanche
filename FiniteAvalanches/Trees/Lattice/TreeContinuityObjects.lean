import FiniteAvalanches.Trees.Lattice.ConnectingSubtree
import FiniteAvalanches.Sandpile.Components.CutSites
import Mathlib.MeasureTheory.Measure.Restrict

set_option autoImplicit false
open LatticeProb MeasureTheory Filter
open scoped Classical ENNReal

namespace TreeMeasurability11
open FiniteAvalanches.Sandpile FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Trees.Lattice
noncomputable section

/-- The full source carrier: actual connected one-ended selected spanning trees. -/
abbrev EndedTree := {ω : EdgeField // IsTree ω ∧ OneEnded ω}

private theorem ended_support_null :
    (squareLatticeUST : Measure EdgeField) {ω | ¬(IsTree ω ∧ OneEnded ω)} = 0 :=
  ae_iff.mp squareLatticeUST_ae_tree_oneEnded

private theorem ended_support_nullMeasurable :
    NullMeasurableSet {ω : EdgeField | IsTree ω ∧ OneEnded ω}
      (squareLatticeUST : Measure EdgeField) :=
  NullMeasurableSet.of_compl (NullMeasurableSet.of_null ended_support_null)

/-- Pullback of the registered actual law to its full conull source carrier. -/
def endedUST : Measure EndedTree :=
  (squareLatticeUST : Measure EdgeField).comap Subtype.val

theorem endedUST_apply (A : Set EndedTree) (hA : MeasurableSet A) :
    endedUST A = (squareLatticeUST : Measure EdgeField) (Subtype.val '' A) :=
  Measure.comap_apply₀ _ _ Subtype.val_injective
    (fun _ h => MeasureTheory.Measure.MeasurableSet.nullMeasurableSet_subtype_coe ended_support_nullMeasurable h)
    hA.nullMeasurableSet

instance endedUST_probability : IsProbabilityMeasure endedUST where
  measure_univ := by
    rw [endedUST_apply Set.univ MeasurableSet.univ]
    have h : (Subtype.val : EndedTree → EdgeField) '' Set.univ =
        {ω | IsTree ω ∧ OneEnded ω} := by ext ω; simp
    rw [h]
    have hmass := measure_add_measure_compl₀ ended_support_nullMeasurable
    change (squareLatticeUST : Measure EdgeField) {ω | IsTree ω ∧ OneEnded ω} +
      (squareLatticeUST : Measure EdgeField) {ω | ¬(IsTree ω ∧ OneEnded ω)} =
      (squareLatticeUST : Measure EdgeField) Set.univ at hmass
    rw [ended_support_null, add_zero, measure_univ] at hmass
    exact hmass

/-- No UST selection is changed by passing to the source carrier. -/
theorem endedUST_map : endedUST.map (Subtype.val : EndedTree → EdgeField) =
    (squareLatticeUST : Measure EdgeField) := by
  ext A hA
  rw [Measure.map_apply measurable_subtype_coe hA,
    endedUST_apply _ (measurable_subtype_coe hA), Set.image_preimage_eq_inter_range]
  have hr : Set.range (Subtype.val : EndedTree → EdgeField) =
      {ω | IsTree ω ∧ OneEnded ω} := by ext ω; simp
  rw [hr]
  exact measure_inter_conull ended_support_null

/-- Every source is retained; a source outside the volume is not silently dropped. -/
def finiteMarks (N : ℕ) (S : Finset (Site 2)) : Set (FiniteWired.Vertex N) :=
  some '' {x : FiniteWired.Active N | FiniteWired.site x ∈ S}

theorem finiteMarks_nonempty (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (hN : ∀ x ∈ S, FiniteWired.inBox N x) : (finiteMarks N S).Nonempty := by
  obtain ⟨x, hx⟩ := hS
  exact ⟨some (FiniteWired.activeOfSite N x (hN x hx)),
    ⟨FiniteWired.activeOfSite N x (hN x hx), hx, rfl⟩⟩

/-- Actual finite reciprocal, with the specified outside-volume zero extension. -/
def finiteZN (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : (WiredTrees.graph N).SpanningTree) : ℝ :=
  if hN : ∀ x ∈ S, FiniteWired.inBox N x then
    WiredTrees.reciprocal N (finiteMarks N S) (finiteMarks_nonempty N S hS hN) t
  else 0

theorem finiteZN_outside (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (hN : ¬∀ x ∈ S, FiniteWired.inBox N x) (t : (WiredTrees.graph N).SpanningTree) :
    finiteZN N S hS t = 0 := by rw [finiteZN, dif_neg hN]

theorem finiteZN_inside (N : ℕ) (S : Finset (Site 2)) (hS : S.Nonempty)
    (hN : ∀ x ∈ S, FiniteWired.inBox N x) (t : (WiredTrees.graph N).SpanningTree) :
    finiteZN N S hS t =
      if (WiredTrees.graph N).ancestorOf t none (finiteMarks N S)
          (finiteMarks_nonempty N S hS hN) ≠ none then
        (1 : ℝ) / ((WiredTrees.graph N).admissibleEdges
          ((WiredTrees.graph N).descendants t none ((WiredTrees.graph N).ancestorOf t none
            (finiteMarks N S) (finiteMarks_nonempty N S hS hN)))
          ((WiredTrees.graph N).span t (finiteMarks N S))).card
      else 0 := by
  rw [finiteZN, dif_pos hN]
  unfold WiredTrees.reciprocal FiniteAvalanches.Trees.Multigraph.reciprocalWeight
  split <;> rfl

/-- Each original exit copy retains its own original lattice edge before wiring. -/
def originalCopyEdge {N : ℕ} : FiniteWired.Edge N → LatticeEdge
  | .inl e => interiorEdge e
  | .inr e => ⟨s(FiniteWired.site e.val.1,
      FiniteWired.site e.val.1 + FiniteWired.step e.val.2), by
      rcases e.val.2 with ⟨i, b⟩
      cases b
      · exact ⟨i, Or.inr (by simp [FiniteWired.step])⟩
      · exact ⟨i, Or.inl (by simp [FiniteWired.step])⟩⟩

/-- The literal finite path/cut event, including copies crossing the wired boundary. -/
def finiteCutEscape (o : Site 2) (f : LatticeEdge) (M N : ℕ) :
    Set (WiredTrees.graph N).SpanningTree :=
  {t | ∃ a : FiniteWired.Active N, FiniteWired.site a = o ∧
    ∃ e : FiniteWired.Edge N, originalCopyEdge e = f ∧
      e ∈ (WiredTrees.graph N).rootPathCopies t (some a) none ∧
      ¬cutSites a t e ⊆ boxSites M}

/-- Literal positive reciprocal on the full proper source-tree carrier. -/
def infiniteReciprocal (S : Finset (Site 2)) (hS : S.Nonempty) (T : EndedTree) : ℝ :=
  (sourceBoundaryCount T.val T.property.1 T.property.2 S hS : ℝ)⁻¹

/-- Membership in the true infinite oriented ray and escape of the actual cut component. -/
def infiniteCutEscape (o : Site 2) (f : LatticeEdge) (M : ℕ) : Set EndedTree :=
  {T | (∃ n : ℕ, f.val = s((orientedRay T.val T.property.1 T.property.2 o).vertex n,
      (orientedRay T.val T.property.1 T.property.2 o).vertex (n + 1))) ∧
    ¬cutComponent T.val f o ⊆ (boxSites M : Set (Site 2))}

theorem true_span_consumer (T : EndedTree) (S : Finset (Site 2)) (hS : S.Nonempty) :
    (connectingSites T.val T.property.1 T.property.2 S hS : Set (Site 2)) =
      FiniteAvalanches.Trees.RootedPaths.connectingSubtree T.property.1 S ∧
    (vertexPast T.val T.property.1 T.property.2
      (earliestCommonAncestor T.val T.property.1 T.property.2 S hS)).Finite ∧
    1 ≤ sourceBoundaryCount T.val T.property.1 T.property.2 S hS :=
  ⟨connectingSites_eq_span _ _ _ _ _, vertexPast_finite _ _ _ _,
    sourceBoundaryCount_ge_one _ _ _ _ _⟩

theorem outside_zero_box_consumer (t : (WiredTrees.graph 0).SpanningTree) :
    finiteZN 0 {unit (0 : Fin 2)} (Finset.singleton_nonempty _) t = 0 := by
  apply finiteZN_outside
  intro h
  have hx := h (unit (0 : Fin 2)) (Finset.mem_singleton_self _) (0 : Fin 2)
  norm_num [unit] at hx

theorem absent_source_cut_consumer (o : Site 2) (h : ¬FiniteWired.inBox 0 o)
    (f : LatticeEdge) (M : ℕ) : finiteCutEscape o f M 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro t ⟨a, ha, _⟩
  apply h
  rw [← ha]
  exact fun i => (a i).property

theorem exit_copy_identity_consumer {N : ℕ} (e : FiniteWired.ExitEdge N) :
    (originalCopyEdge (Sum.inr e)).val =
      s(FiniteWired.site e.val.1, FiniteWired.site e.val.1 + FiniteWired.step e.val.2) := rfl

theorem original_denominator_consumer (N : ℕ) (t : (WiredTrees.graph N).SpanningTree) :
    WiredTrees.law N {t} = (WiredTrees.treeCount N : ℝ≥0∞)⁻¹ :=
  WiredTrees.law_singleton N t

end
end TreeMeasurability11

