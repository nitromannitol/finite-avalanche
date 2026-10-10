import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoxForestColors
import FiniteAvalanches.Probability.UniformMap

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees MeasureTheory
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

abbrev ReferenceForest (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :=
  (StatementTypes.graph D P marked).RootedForest ({alpha D P, beta D P} : Set (Vertex D P))

theorem primalForest_nonempty (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) : Nonempty (PrimalForest D P) :=
  (finiteForest_nonempty (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N).map
    (forestEquiv D P N hDbox)

def referenceEquiv (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P) :
    FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N ≃ ReferenceForest D P marked :=
  (forestEquiv D P N hDbox).trans (LocalMarkedForest.referencePrimalEquiv D P marked).symm

theorem referenceForest_nonempty (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P) :
    Nonempty (ReferenceForest D P marked) :=
  (finiteForest_nonempty (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N).map
    (referenceEquiv D P N hDbox marked)

def referenceField (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (F : ReferenceForest D P marked) : ColorField :=
  fun x => decide ((StatementTypes.graph D P marked).reaches F.val (project D P x) (beta D P))

theorem reference_field_transport (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N) :
    referenceField D P marked (referenceEquiv D P N hDbox marked F) =
      LocalZeroExterior.field (LocalZeroExterior.domainRoots D P) N F := by
  rw [← field_transport D P N hDbox F]
  funext x
  apply Bool.decide_congr
  have h := LocalMarkedForest.referencePrimalEquiv_reaches D P marked
    ((LocalMarkedForest.referencePrimalEquiv D P marked).symm (forestEquiv D P N hDbox F))
    (project D P x) (beta D P)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem reference_full_denominator (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P) :
    finiteForestCount (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N =
      Nat.card (ReferenceForest D P marked) := Nat.card_congr (referenceEquiv D P N hDbox marked)

/-- Whole source primal uniform color law, with the bijection constructed internally. -/
theorem primal_color_law (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) :
    letI : Nonempty (PrimalForest D P) := primalForest_nonempty D P N hDbox
    (uniformMeasure (PrimalForest D P)).map (primalField D P) =
      wilsonColorLaw (LocalZeroExterior.domainRoots D P) := by
  letI : Nonempty (PrimalForest D P) := primalForest_nonempty D P N hDbox
  have hm := uniform_measure_map_equiv (forestEquiv D P N hDbox)
  rw [← hm, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  have hf : primalField D P ∘ forestEquiv D P N hDbox =
      LocalZeroExterior.field (LocalZeroExterior.domainRoots D P) N := by
    funext F
    exact field_transport D P N hDbox F
  rw [hf]
  exact LocalActualSourceConsumer.domain_color_law D P N hDbox

/-- Whole H0 law, consuming color complementation, actual box contraction, and marked deletion. -/
theorem reference_color_law (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P) :
    letI : Nonempty (ReferenceForest D P marked) := referenceForest_nonempty D P N hDbox marked
    (uniformMeasure (ReferenceForest D P marked)).map (referenceField D P marked) =
      wilsonColorLaw (LocalZeroExterior.domainRoots D P) := by
  letI : Nonempty (ReferenceForest D P marked) := referenceForest_nonempty D P N hDbox marked
  have hm := uniform_measure_map_equiv (referenceEquiv D P N hDbox marked)
  rw [← hm, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  have hf : referenceField D P marked ∘ referenceEquiv D P N hDbox marked =
      LocalZeroExterior.field (LocalZeroExterior.domainRoots D P) N := by
    funext F
    exact reference_field_transport D P N hDbox marked F
  rw [hf]
  exact LocalActualSourceConsumer.domain_color_law D P N hDbox

end
end LocalBoxContraction
