import FiniteAvalanches.Trees.Lattice.Space
import FiniteAvalanches.Sandpile.TreeLaw
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

                                                                            
                                                                               
                                                                                
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical ENNReal
noncomputable section

                                                                            
def interiorEdge {N : ℕ} (e : FiniteWired.InteriorEdge N) : LatticeEdge :=
  ⟨s(FiniteWired.site e.val.1, FiniteWired.site e.val.2),
    by obtain ⟨i, hi⟩ := e.property; exact ⟨i, Or.inl hi⟩⟩

theorem interiorEdge_injective (N : ℕ) : Function.Injective (@interiorEdge N) := by
  intro e f h
  have hs := Sym2.eq_iff.mp (congrArg Subtype.val h)
  rcases hs with hs | hs
  · exact Subtype.ext (Prod.ext (FiniteWired.site_injective N hs.1)
      (FiniteWired.site_injective N hs.2))
  · obtain ⟨i, hi⟩ := e.property
    obtain ⟨j, hj⟩ := f.property
    rw [hs.1, hs.2] at hi
    have hhi := congrFun hi i
    have hhj := congrFun hj i
    fin_cases i <;> fin_cases j <;> norm_num [unit] at hhi hhj <;> omega

/-- The finite-copy map is partial precisely at the contracted sink exits. -/
def copyEdge {N : ℕ} : FiniteWired.Edge N → Option LatticeEdge
  | .inl e => some (interiorEdge e)
  | .inr _ => none

theorem copyEdge_internal {N : ℕ} (e : FiniteWired.InteriorEdge N) :
    copyEdge (.inl e) = some (interiorEdge e) := rfl

theorem copyEdge_exit {N : ℕ} (e : FiniteWired.ExitEdge N) :
    copyEdge (.inr e) = none := rfl

                                                                              
                                                                                         
def wiredField {N : ℕ} (t : (WiredTrees.graph N).SpanningTree) : EdgeField :=
  fun e => decide (∃ i : FiniteWired.InteriorEdge N,
    Sum.inl i ∈ t.val ∧ interiorEdge i = e)

theorem wiredField_eq_true {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (e : LatticeEdge) : wiredField t e = true ↔
      ∃ i : FiniteWired.InteriorEdge N, Sum.inl i ∈ t.val ∧ interiorEdge i = e := by
  simp only [wiredField, decide_eq_true_eq]

theorem wiredField_internal_iff {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (i : FiniteWired.InteriorEdge N) :
    wiredField t (interiorEdge i) = true ↔ Sum.inl i ∈ t.val := by
  rw [wiredField_eq_true]
  constructor
  · rintro ⟨j, hj, he⟩
    exact (interiorEdge_injective N he) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem wiredField_eq_false_of_no_internal {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (e : LatticeEdge) (he : ∀ i : FiniteWired.InteriorEdge N, interiorEdge i ≠ e) :
    wiredField t e = false := by
  have hn : ¬ ∃ i : FiniteWired.InteriorEdge N,
      Sum.inl i ∈ t.val ∧ interiorEdge i = e := by
    rintro ⟨i, _, hi⟩
    exact he i hi
  simp [wiredField, hn]

theorem wiredField_measurable (N : ℕ) :
    Measurable (@wiredField N) := measurable_of_finite _

/-- Pushforward of the original complete uniform copied-edge wired tree law. -/
def finiteLaw (N : ℕ) : Measure EdgeField :=
  Measure.map (@wiredField N) (WiredTrees.law N)

instance finiteLaw_probability (N : ℕ) : IsProbabilityMeasure (finiteLaw N) :=
  (WiredTrees.law N).isProbabilityMeasure_map (wiredField_measurable N).aemeasurable

theorem finiteLaw_mass_one (N : ℕ) : finiteLaw N Set.univ = 1 := measure_univ

/-- The same actual finite law as a probability-measure element, for weak convergence. -/
def finiteProbability (N : ℕ) : ProbabilityMeasure EdgeField := ⟨finiteLaw N, inferInstance⟩

theorem finiteLaw_apply (N : ℕ) (A : Set EdgeField) (hA : MeasurableSet A) :
    finiteLaw N A = WiredTrees.law N {t | wiredField t ∈ A} :=
  Measure.map_apply (wiredField_measurable N) hA

theorem finiteLaw_cylinder (N : ℕ) (F : Finset LatticeEdge) (p : F → Bool) :
    finiteLaw N (cylinder F p) = WiredTrees.law N {t | F.restrict (wiredField t) = p} :=
  finiteLaw_apply N _ (measurableSet_cylinder F p)

theorem finiteLaw_original_count (N : ℕ) (A : Set EdgeField) (hA : MeasurableSet A) :
    finiteLaw N A =
      (Nat.card ({t : (WiredTrees.graph N).SpanningTree | wiredField t ∈ A} :
        Set (WiredTrees.graph N).SpanningTree) : ℝ≥0∞) / WiredTrees.treeCount N := by
  rw [finiteLaw_apply N A hA]
  change uniformMeasure (WiredTrees.graph N).SpanningTree _ = _
  rw [uniformMeasure_apply]
  simp only [Nat.card_eq_fintype_card, WiredTrees.treeCount]

end
end FiniteAvalanches.Trees.Lattice
