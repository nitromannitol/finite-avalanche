import FiniteAvalanches.Wilson.Lattice.FreeTerminalCoupling
import FiniteAvalanches.Trees.Lattice.WiredLaw

/-! Uniform free-box spanning-tree measures on the full lattice edge field. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

local instance decEqInteriorEdgeFreeBoxLaw (N : ℕ) : DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _
local instance freeBoxSpanningTreeNonempty (N : ℕ) : Nonempty (freeBoxGraph (N + 1)).SpanningTree := freeBox_spanningTree_nonempty N

/-- A free-box tree as an edge field on the full square lattice. -/
def freeBoxField {N : ℕ} (t : (freeBoxGraph (N + 1)).SpanningTree) : EdgeField :=
  fun e => decide (∃ i : FiniteWired.InteriorEdge (N + 1), i ∈ t.val ∧ interiorEdge i = e)

/-- An original interior edge is selected precisely when its copy is in the tree. -/
theorem freeBoxField_interior_iff {N : ℕ} (t : (freeBoxGraph (N + 1)).SpanningTree)
    (i : FiniteWired.InteriorEdge (N + 1)) :
    freeBoxField t (interiorEdge i) = true ↔ i ∈ t.val := by
  simp only [freeBoxField, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, he⟩
    exact (interiorEdge_injective (N + 1) he) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- The finite free-box field map is measurable. -/
theorem measurable_freeBoxField (N : ℕ) : Measurable (@freeBoxField N) := measurable_of_finite _

/-- The uniform free-box spanning-tree law, extended by absent exterior edges. -/
def freeBoxLaw (N : ℕ) : Measure EdgeField :=
  Measure.map (@freeBoxField N) (freeBoxGraph (N + 1)).treeLaw

instance freeBoxLaw_probability (N : ℕ) : IsProbabilityMeasure (freeBoxLaw N) :=
  ((freeBoxGraph (N + 1)).treeLaw).isProbabilityMeasure_map (measurable_freeBoxField N).aemeasurable

/-- The free-box law as a probability measure for weak convergence. -/
def freeBoxProbability (N : ℕ) : ProbabilityMeasure EdgeField := ⟨freeBoxLaw N, inferInstance⟩

/-- A measurable full-field event has the corresponding free-tree probability. -/
theorem freeBoxLaw_apply (N : ℕ) (A : Set EdgeField) (hA : MeasurableSet A) :
    freeBoxLaw N A = (freeBoxGraph (N + 1)).treeLaw {t | freeBoxField t ∈ A} :=
  Measure.map_apply (measurable_freeBoxField N) hA

/-- The terminal origin-rooted incident-stack forest has the free-box field law. -/
theorem variableStackLaw_freeBoxField_event_eq (N : ℕ)
    (k : Cursor (FiniteWired.Active (N + 1))) (A : Set EdgeField) (hA : MeasurableSet A) :
    variableStackLaw (IncidentCopy (freeBoxGraph (N + 1)))
      {σ | ∃ a : GoodIncidentArrows (freeBoxGraph (N + 1)) {wiredOrigin (N + 1)},
        freeBoxField (singletonRootedForestEquiv (freeBoxGraph (N + 1)) (wiredOrigin (N + 1))
          (incidentArrowForest (freeBoxGraph (N + 1)) {wiredOrigin (N + 1)} a)) ∈ A ∧
        σ ∈ terminalOutputEvent {wiredOrigin (N + 1)} (incidentCopyHead (freeBoxGraph (N + 1))) k
          (fun v i σ => σ (v, i)) a} = freeBoxLaw N A := by
  rw [freeBoxLaw_apply N A hA]
  have h := variableStackLaw_freeBoxSpanningTreeEvent_eq N (wiredOrigin (N + 1)) k
    {t | freeBoxField t ∈ A}
  change _ = FiniteAvalanches.uniformMeasure (freeBoxGraph (N + 1)).SpanningTree _
  rw [FiniteAvalanches.uniformMeasure_apply]
  have hS (t : (freeBoxGraph (N + 1)).SpanningTree) :
      ({t | freeBoxField t ∈ A} : Set (freeBoxGraph (N + 1)).SpanningTree) t ↔
        freeBoxField t ∈ A := Iff.rfl
  simpa only [Nat.card_eq_fintype_card, hS] using h

end
end FiniteAvalanches.Wilson.Lattice
