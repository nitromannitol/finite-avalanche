import FiniteAvalanches.Trees.Lattice.ConnectingSubtree
import Mathlib.Probability.Kernel.Basic

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb MeasureTheory ProbabilityTheory FiniteAvalanches.Wilson.Lattice
open scoped Classical ENNReal
noncomputable section

/-- The actual conull tree/end domain; it supplies no additional source premise. -/
abbrev TreeOutcome := {ω : EdgeField // IsTree ω ∧ OneEnded ω}

theorem tree_locus_nullMeasurable :
    NullMeasurableSet {ω : EdgeField | IsTree ω ∧ OneEnded ω}
      (squareLatticeUST : Measure EdgeField) := by
  have hz : (squareLatticeUST : Measure EdgeField)
      {ω | ¬(IsTree ω ∧ OneEnded ω)} = 0 :=
    ae_iff.mp squareLatticeUST_ae_tree_oneEnded
  exact NullMeasurableSet.of_compl (NullMeasurableSet.of_null hz)

private theorem treeOutcome_image_nullMeasurable (A : Set TreeOutcome)
    (hA : MeasurableSet A) : NullMeasurableSet
      (((↑) : TreeOutcome → EdgeField) '' A) (squareLatticeUST : Measure EdgeField) :=
  Measure.MeasurableSet.nullMeasurableSet_subtype_coe tree_locus_nullMeasurable hA

/-- The inherited restriction of the registered UST to its actual conull
tree/end domain. The original law is recovered by forgetting the subtype. -/
def treeOutcomeLaw : Measure TreeOutcome :=
  (squareLatticeUST : Measure EdgeField).comap Subtype.val

instance treeOutcomeLaw_probability : IsProbabilityMeasure treeOutcomeLaw where
  measure_univ := by
    rw [treeOutcomeLaw, Measure.comap_apply₀ ((↑) : TreeOutcome → EdgeField)
      (squareLatticeUST : Measure EdgeField) Subtype.val_injective
      treeOutcome_image_nullMeasurable
      MeasurableSet.univ.nullMeasurableSet]
    simp only [Set.image_univ, Subtype.range_coe_subtype]
    exact (mem_ae_iff_prob_eq_one₀ tree_locus_nullMeasurable).mp
      squareLatticeUST_ae_tree_oneEnded

theorem treeOutcomeLaw_map_coe : treeOutcomeLaw.map Subtype.val =
    (squareLatticeUST : Measure EdgeField) := by
  ext A hA
  rw [Measure.map_apply measurable_subtype_coe hA, treeOutcomeLaw,
    Measure.comap_apply₀ ((↑) : TreeOutcome → EdgeField)
      (squareLatticeUST : Measure EdgeField) Subtype.val_injective
      treeOutcome_image_nullMeasurable
      (hA.preimage measurable_subtype_coe).nullMeasurableSet]
  have himage : ((Subtype.val : TreeOutcome → EdgeField) ''
      (Subtype.val : TreeOutcome → EdgeField) ⁻¹' A) =
      A ∩ {ω : EdgeField | IsTree ω ∧ OneEnded ω} := by
    ext ω
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, t.property⟩
    · rintro ⟨hωA, hω⟩
      exact ⟨⟨ω, hω⟩, hωA, rfl⟩
  rw [himage]
  have h : (squareLatticeUST : Measure EdgeField)
      (A ∩ {ω : EdgeField | IsTree ω ∧ OneEnded ω}) =
      (squareLatticeUST : Measure EdgeField) A := by
    have hrestrict :=  congrArg (fun m : Measure EdgeField => m A)
      (Measure.restrict_eq_self_of_ae_mem squareLatticeUST_ae_tree_oneEnded)
    rw [Measure.restrict_apply₀ hA.nullMeasurableSet] at hrestrict
    exact hrestrict
  exact h

/-- Standard inherited product sigma-algebra: finite vertex-set membership and
every coordinate of the literal parametrized ray. -/
instance connectingPairMeasurableSpace : MeasurableSpace ConnectingPair :=
  MeasurableSpace.comap (fun p : ConnectingPair => (p.sites, p.ray.vertex)) inferInstance

/-- A genuine finite connecting tree together with its outgoing ConnectingPair.
All original unordered edge indicators are retained, with zero outside the
finite vertex support. -/
abbrev BranchObservation := {b : EdgeField × ConnectingPair //
  (∀ e : LatticeEdge, b.1 e = true → ∀ v ∈ e.val, v ∈ b.2.sites) ∧
  ((toGraph b.1).induce (b.2.sites : Set (Site 2))).IsTree}

/-- The actual selected connecting-tree indicators, including absent edges
between its vertices. -/
def connectingBranchField (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : TreeOutcome) : EdgeField :=
  fun e => t.val e && decide (∀ v ∈ e.val,
    v ∈ connectingSites t.val t.property.1 t.property.2 S hS)

theorem connectingBranchField_eq_true_iff (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : TreeOutcome) (e : LatticeEdge) : connectingBranchField S hS t e = true ↔
    t.val e = true ∧ ∀ v ∈ e.val,
      v ∈ connectingSites t.val t.property.1 t.property.2 S hS := by
  simp only [connectingBranchField, Bool.and_eq_true, decide_eq_true_eq]

theorem connectingBranchField_induce (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : TreeOutcome) :
    (toGraph (connectingBranchField S hS t)).induce
      (connectingSites t.val t.property.1 t.property.2 S hS : Set (Site 2)) =
    (toGraph t.val).induce
      (connectingSites t.val t.property.1 t.property.2 S hS : Set (Site 2)) := by
  ext x y
  change (toGraph (connectingBranchField S hS t)).Adj x.val y.val ↔
    (toGraph t.val).Adj x.val y.val
  constructor
  · rintro ⟨h, he⟩
    exact ⟨h, ((connectingBranchField_eq_true_iff S hS t _).mp he).1⟩
  · rintro ⟨h, he⟩
    refine ⟨h, (connectingBranchField_eq_true_iff S hS t _).mpr ⟨he, ?_⟩⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact x.property
    · exact y.property

/-- No connecting pair is supplied as an input: both the true minimal branch
and the outgoing ray are constructed from the same actual UST realization. -/
def sourceObservation (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : TreeOutcome) : BranchObservation :=
  ⟨(connectingBranchField S hS t,
    sourceConnectingPair t.val t.property.1 t.property.2 S hS),
    ⟨fun e he => ((connectingBranchField_eq_true_iff S hS t e).mp he).2, by
      change ((toGraph (connectingBranchField S hS t)).induce
        (connectingSites t.val t.property.1 t.property.2 S hS : Set (Site 2))).IsTree
      rw [connectingBranchField_induce]
      exact connectingSites_isTree t.val t.property.1 t.property.2 S hS⟩⟩

def sourceCount (S : Finset (Site 2)) (hS : S.Nonempty) (t : TreeOutcome) : ℕ :=
  sourceBoundaryCount t.val t.property.1 t.property.2 S hS

/-- The full distribution on all natural counts under the actual nu_(K,gamma+).
It is a projection of the already identified color law, not a replacement law. -/
def branchCountLaw (b : BranchObservation) : Measure ℕ :=
  (wilsonColorLaw b.val.2.roots).map (contacts b.val.2.sites)

instance branchCountLaw_probability (b : BranchObservation) :
    IsProbabilityMeasure (branchCountLaw b) :=
  (wilsonColorLaw b.val.2.roots).isProbabilityMeasure_map
    (continuous_contacts b.val.2.sites).measurable.aemeasurable

theorem branchCountLaw_apply (b : BranchObservation) (D : Set ℕ) :
    branchCountLaw b D = wilsonColorLaw b.val.2.roots
      {σ | contacts b.val.2.sites σ ∈ D} := by
  exact Measure.map_apply (continuous_contacts b.val.2.sites).measurable
    (Set.to_countable D).measurableSet

theorem sourceObservation_singleton (x : Site 2) (t : TreeOutcome) :
    (sourceObservation {x} (Finset.singleton_nonempty x) t).val.2.sites = {x} :=
  connectingSites_singleton t.val t.property.1 t.property.2 x

theorem sourceCount_positive (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : TreeOutcome) : 1 ≤ sourceCount S hS t :=
  sourceBoundaryCount_ge_one t.val t.property.1 t.property.2 S hS

/-- The source branch law exercises every set of natural counts with the actual
minimal K and its genuine outgoing ray; no conditional identity is assumed. -/
theorem actual_source_branch_law_all_counts (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : TreeOutcome) (D : Set ℕ) :
    branchCountLaw (sourceObservation S hS t) D =
      wilsonColorLaw (sourceConnectingPair t.val t.property.1 t.property.2 S hS).roots
        {σ | contacts (connectingSites t.val t.property.1 t.property.2 S hS) σ ∈ D} :=
  branchCountLaw_apply (sourceObservation S hS t) D

theorem actual_source_branch_is_minimal (S : Finset (Site 2)) (hS : S.Nonempty)
    (t : TreeOutcome) :
    ((sourceObservation S hS t).val.2.sites : Set (Site 2)) =
      FiniteAvalanches.Trees.RootedPaths.connectingSubtree t.property.1 S ∧
    (sourceObservation S hS t).val.2.ray.vertex 0 =
      earliestCommonAncestor t.val t.property.1 t.property.2 S hS :=
  ⟨connectingSites_eq_span t.val t.property.1 t.property.2 S hS, rfl⟩

end
end FiniteAvalanches.Trees.Lattice
