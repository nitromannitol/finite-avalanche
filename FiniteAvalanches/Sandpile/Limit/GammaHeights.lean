import FiniteAvalanches.Sandpile.Recurrence.GammaAccessibility
import FiniteAvalanches.Sandpile.Burning.PastAdapter

/-! The uniform law on allowed fields of a finite volume `Γ` is the image of the uniform
law on allowed height fields of the wired graph of `Γ`, in the conventions of the
burning bijection, with heights read at the corresponding vertices. -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.GammaGraph

open LatticeProb MeasureTheory FiniteAvalanches.External.SandpileLimit
open scoped Classical

noncomputable section

/-- Allowed height fields of the wired graph of `Γ`. -/
abbrev AllowedHeights (Γ : Finset Site2) :=
  {h : Burning.SourceHeights (graph Γ) (none : Vertex Γ) //
    Burning.noForbidden (graph Γ) (Finset.univ.erase none) h}

/-- Raw stable integer fields of `Γ` and of its wired graph. -/
def rawAllowedEquiv (Γ : Finset Site2) :
    RawInteger.AllowedState Γ ≃ RawGraph.AllowedState (graph Γ) (none : Vertex Γ) :=
  Equiv.subtypeEquiv (Equiv.subtypeEquiv (fieldEquiv Γ) stable_iff)
    (fun η => no_fsc_iff η.val)

/-- Allowed height fields of the wired graph of `Γ` and allowed fields of `Γ`. -/
def allowedHeightsEquiv (Γ : Finset Site2) : AllowedHeights Γ ≃ allowedFields Γ :=
  (RawGraph.allowedFieldEquiv (graph Γ) (none : Vertex Γ)).symm.trans
    ((rawAllowedEquiv Γ).symm.trans (RawInteger.allowedFieldEquiv Γ))

theorem allowedHeightsEquiv_value (Γ : Finset Site2) (h : AllowedHeights Γ) (x : Γ) :
    (((allowedHeightsEquiv Γ h).val x.val).val : ℤ) = ((h.val (vertexEquiv Γ x)).val : ℤ) :=
  RawInteger.allowed_embedding_value _ x

theorem allowedHeightsEquiv_value_nat (Γ : Finset Site2) (h : AllowedHeights Γ) (x : Γ) :
    ((allowedHeightsEquiv Γ h).val x.val).val = (h.val (vertexEquiv Γ x)).val := by
  exact_mod_cast allowedHeightsEquiv_value Γ h x

instance allowedHeightsNonempty (Γ : Finset Site2) : Nonempty (AllowedHeights Γ) :=
  Nonempty.map (allowedHeightsEquiv Γ).symm inferInstance

instance allowedHeightsMeasurableSpace (Γ : Finset Site2) :
    MeasurableSpace (AllowedHeights Γ) := ⊤

instance allowedHeightsMeasurableSingletonClass (Γ : Finset Site2) :
    MeasurableSingletonClass (AllowedHeights Γ) := ⟨fun _ => trivial⟩

/-- The finite-volume sandpile law of `Γ` read from allowed height fields. -/
theorem finiteFieldLawOn_eq_map (Γ : Finset Site2) :
    finiteFieldLawOn Γ = Measure.map (fun h => (allowedHeightsEquiv Γ h).val)
      (FiniteAvalanches.uniformMeasure (AllowedHeights Γ)) := by
  have hmap : (fun h : AllowedHeights Γ => (allowedHeightsEquiv Γ h).val) =
      (Subtype.val : allowedFields Γ → StableField) ∘ allowedHeightsEquiv Γ := rfl
  rw [hmap, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    FiniteAvalanches.uniform_measure_map_equiv]
  rfl

end

end FiniteAvalanches.Sandpile.GammaGraph
