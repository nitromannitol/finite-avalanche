import FiniteAvalanches.Wilson.Lattice.ColoredForests
import FiniteAvalanches.Wilson.RootContraction.Equivalence
import FiniteAvalanches.Trees.Existence

/-! Actual uniform original-copy rooted forests in wired boxes, and their full
ambient indicator/color projections. The exterior is the actual one-colored sink.
No infinite measure is selected. The safe quotient input is ordinary proved infrastructure. -/
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- Original roots remain distinct; the wired exterior is an additional one root. -/
def wiredZero (R : RootPair) (N : ℕ) : Set (FiniteWired.Vertex N)
  | none => False
  | some x => FiniteWired.site x ∈ R.zero

def wiredOne (R : RootPair) (N : ℕ) : Set (FiniteWired.Vertex N)
  | none => True
  | some x => FiniteWired.site x ∈ R.one

theorem wired_roots_disjoint (R : RootPair) (N : ℕ) : Disjoint (wiredZero R N) (wiredOne R N) := by
  apply Set.disjoint_left.mpr
  intro v hz ho
  cases v with
  | none => exact hz
  | some x => exact Set.disjoint_left.mp R.disjoint hz ho

def wiredRoots (R : RootPair) (N : ℕ) :
    CopiedNetwork.Roots (V := FiniteWired.Vertex N) :=
  ⟨wiredZero R N ∪ wiredOne R N, ⟨none, Or.inr trivial⟩⟩

abbrev FiniteForest (R : RootPair) (N : ℕ) := (WiredTrees.graph N).RootedForest (wiredRoots R N).val

/-- Existence from an actual connected quotient spanning tree, before any law. -/
theorem finiteForest_nonempty (R : RootPair) (N : ℕ) : Nonempty (FiniteForest R N) := by
  have hc : ∀ x y, (WiredTrees.graph N).reaches Finset.univ x y := by
    intro x y
    exact (WiredTrees.graph N).reaches_mono (Finset.subset_univ _)
      ((WiredTrees.rowTree N).property.2.2.1 x (Set.mem_univ x) y (Set.mem_univ y))
  have hq := FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient.graph_connected (WiredTrees.graph N) (wiredRoots R N) hc
  have hn := (FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient.graph (WiredTrees.graph N) (wiredRoots R N)).nonempty_spanning_tree hq
  obtain ⟨t⟩ := hn
  exact ⟨(FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient.rootContractionEquiv (WiredTrees.graph N) (wiredRoots R N)).symm t⟩

instance finiteForestNonempty (R : RootPair) (N : ℕ) : Nonempty (FiniteForest R N) :=
  finiteForest_nonempty R N

instance finiteForestMeasurableSpace (R : RootPair) (N : ℕ) : MeasurableSpace (FiniteForest R N) := ⊤
instance finiteForestMeasurableSingletonClass (R : RootPair) (N : ℕ) :
    MeasurableSingletonClass (FiniteForest R N) := ⟨fun _ => trivial⟩

def finiteForestCount (R : RootPair) (N : ℕ) : ℕ := Nat.card (FiniteForest R N)

theorem finiteForestCount_pos (R : RootPair) (N : ℕ) : 0 < finiteForestCount R N := by
  exact Nat.card_pos

/-- This uniform law counts original E copies, not endpoint supports or color fields. -/
def finiteUniformLaw (R : RootPair) (N : ℕ) : Measure (FiniteForest R N) :=
  FiniteAvalanches.uniformMeasure (FiniteForest R N)

instance finiteUniformLaw_probability (R : RootPair) (N : ℕ) :
    IsProbabilityMeasure (finiteUniformLaw R N) := inferInstanceAs
      (IsProbabilityMeasure (FiniteAvalanches.uniformMeasure (FiniteForest R N)))

def finiteColors (R : RootPair) (N : ℕ) (F : FiniteForest R N) : FiniteWired.Vertex N → Bool :=
  fun v => decide (∃ r ∈ wiredOne R N, (WiredTrees.graph N).reaches F.val v r)

theorem finiteColors_one (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    {v : FiniteWired.Vertex N} (hv : v ∈ wiredOne R N) : finiteColors R N F v = true := by
  simp only [finiteColors, decide_eq_true_eq]
  exact ⟨v, hv, .refl⟩

theorem finiteColors_zero (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    {v : FiniteWired.Vertex N} (hv : v ∈ wiredZero R N) : finiteColors R N F v = false := by
  have hn : ¬∃ r ∈ wiredOne R N, (WiredTrees.graph N).reaches F.val v r := by
    rintro ⟨r, hr, hvr⟩
    obtain ⟨u, _, _, hu⟩ := F.property.2 v
    have he : v = r := (hu v (Or.inl hv) .refl).trans (hu r (Or.inr hr) hvr).symm
    exact Set.disjoint_left.mp (wired_roots_disjoint R N) hv (he.symm ▸ hr)
  simp [finiteColors, hn]

/-- The literal site projection into the wired graph, including its exterior sink. -/
def wiredSite (N : ℕ) (x : Site 2) : FiniteWired.Vertex N :=
  if h : FiniteWired.inBox N x then some (FiniteWired.activeOfSite N x h) else none

def finiteEdgeField (R : RootPair) (N : ℕ) (F : FiniteForest R N) : EdgeField :=
  fun e => decide (∃ i : FiniteWired.InteriorEdge N, Sum.inl i ∈ F.val ∧ interiorEdge i = e)

def finiteForestField (R : RootPair) (N : ℕ) (F : FiniteForest R N) : ForestField :=
  (finiteEdgeField R N F, fun x => finiteColors R N F (wiredSite N x))

theorem finiteForestField_measurable (R : RootPair) (N : ℕ) :
    Measurable (finiteForestField R N) := measurable_of_finite _

theorem finiteForestField_outside (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    {x : Site 2} (hx : ¬FiniteWired.inBox N x) : (finiteForestField R N F).2 x = true := by
  change finiteColors R N F (wiredSite N x) = true
  rw [wiredSite, dif_neg hx]
  exact finiteColors_one R N F trivial

theorem finiteForestField_internal (R : RootPair) (N : ℕ) (F : FiniteForest R N)
    (i : FiniteWired.InteriorEdge N) :
    (finiteForestField R N F).1 (interiorEdge i) = true ↔ Sum.inl i ∈ F.val := by
  simp only [finiteForestField, finiteEdgeField, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, he⟩
    exact (interiorEdge_injective N he) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

def finiteForestLaw (R : RootPair) (N : ℕ) : Measure ForestField :=
  (finiteUniformLaw R N).map (finiteForestField R N)

instance finiteForestLaw_probability (R : RootPair) (N : ℕ) :
    IsProbabilityMeasure (finiteForestLaw R N) :=
  (finiteUniformLaw R N).isProbabilityMeasure_map (finiteForestField_measurable R N).aemeasurable

def finiteForestProbability (R : RootPair) (N : ℕ) : ProbabilityMeasure ForestField :=
  ⟨finiteForestLaw R N, inferInstance⟩

theorem finiteForestLaw_mass_one (R : RootPair) (N : ℕ) : finiteForestLaw R N Set.univ = 1 := measure_univ

theorem finiteForestLaw_count (R : RootPair) (N : ℕ) (S : Set ForestField) (hS : MeasurableSet S) :
    finiteForestLaw R N S =
      (Nat.card ({F : FiniteForest R N | finiteForestField R N F ∈ S} : Set (FiniteForest R N)) : ℝ≥0∞) /
        finiteForestCount R N := by
  rw [finiteForestLaw, Measure.map_apply (finiteForestField_measurable R N) hS]
  exact FiniteAvalanches.uniformMeasure_apply (FiniteForest R N) _

end
end FiniteAvalanches.Wilson.Lattice
