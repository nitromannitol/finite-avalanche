import FiniteAvalanches.Sandpile.Recurrence.GammaFields
import FiniteAvalanches.Sandpile.Recurrence.RawGraphAccessibility

/-! All-input accessibility on arbitrary finite Gamma follows from the proved
copied-graph criterion after exact fields, steps and finite words are transported. -/
namespace FiniteAvalanches.Sandpile.GammaGraph
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem raw_grain_transport {Γ : Finset Site2} (η : RawInteger.Field Γ) (o : Γ) :
    fieldEquiv Γ (RawInteger.addGrain η o) =
      RawGraph.addGrain none (fieldEquiv Γ η) (vertexEquiv Γ o) := by
  rw [grain_transport]
  funext v
  simp only [RawGraph.addGrain, Function.update_apply]
  split_ifs <;> rfl

theorem step_forward {Γ : Finset Site2} {η ζ : RawInteger.Field Γ}
    (h : RawInteger.Step Γ η ζ) :
    RawGraph.Step (graph Γ) none (fieldEquiv Γ η) (fieldEquiv Γ ζ) := by
  cases h with
  | grain o =>
    rw [raw_grain_transport]
    exact RawGraph.Step.grain (G := graph Γ) (s := none) _ (vertexEquiv Γ o)
  | fire o hu =>
    rw [topple_transport]
    exact RawGraph.Step.fire (G := graph Γ) (s := none) _ (vertexEquiv Γ o)
      (by rw [degree_four, field_equiv_value]; exact hu)

theorem step_backward {Γ : Finset Site2}
    {θ ψ : RawGraph.Field (none : Vertex Γ)} (h : RawGraph.Step (graph Γ) none θ ψ) :
    RawInteger.Step Γ ((fieldEquiv Γ).symm θ) ((fieldEquiv Γ).symm ψ) := by
  cases h with
  | grain o =>
    obtain ⟨x, rfl⟩ := (vertexEquiv Γ).surjective o
    have he : (fieldEquiv Γ).symm (RawGraph.addGrain none θ (vertexEquiv Γ x)) =
        RawInteger.addGrain ((fieldEquiv Γ).symm θ) x := by
      apply (fieldEquiv Γ).injective
      rw [Equiv.apply_symm_apply, raw_grain_transport, Equiv.apply_symm_apply]
    rw [he]
    exact RawInteger.Step.grain _ x
  | fire o hu =>
    obtain ⟨x, rfl⟩ := (vertexEquiv Γ).surjective o
    have he : (fieldEquiv Γ).symm (RawGraph.topple (graph Γ) none θ (vertexEquiv Γ x)) =
        RawInteger.topple ((fieldEquiv Γ).symm θ) x := by
      apply (fieldEquiv Γ).injective
      rw [Equiv.apply_symm_apply, topple_transport, Equiv.apply_symm_apply]
      rfl
    rw [he]
    apply RawInteger.Step.fire _ x
    rw [degree_four] at hu
    exact hu

theorem reach_forward {Γ : Finset Site2} {η ζ : RawInteger.Field Γ}
    (h : RawInteger.Reach η ζ) : RawGraph.Reach (graph Γ) none (fieldEquiv Γ η) (fieldEquiv Γ ζ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.trans (Relation.ReflTransGen.single (step_forward h))

theorem reach_backward {Γ : Finset Site2}
    {θ ψ : RawGraph.Field (none : Vertex Γ)} (h : RawGraph.Reach (graph Γ) none θ ψ) :
    RawInteger.Reach ((fieldEquiv Γ).symm θ) ((fieldEquiv Γ).symm ψ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.trans (Relation.ReflTransGen.single (step_backward h))

theorem reach_iff {Γ : Finset Site2} (η ζ : RawInteger.Field Γ) : RawInteger.Reach η ζ ↔
    RawGraph.Reach (graph Γ) none (fieldEquiv Γ η) (fieldEquiv Γ ζ) := by
  constructor
  · exact reach_forward
  · intro h
    simpa only [Equiv.symm_apply_apply] using reach_backward h

theorem accessible_iff {Γ : Finset Site2} (η : RawInteger.Field Γ) : RawInteger.Accessible η ↔
    RawGraph.Accessible (graph Γ) none (fieldEquiv Γ η) := by
  constructor
  · intro h θ
    obtain ⟨ζ, rfl⟩ := (fieldEquiv Γ).surjective θ
    exact reach_forward (h ζ)
  · intro h ζ
    exact (reach_iff ζ η).mpr (h (fieldEquiv Γ ζ))

end
end FiniteAvalanches.Sandpile.GammaGraph
namespace FiniteAvalanches.Sandpile.RawInteger
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical

/-- Full source criterion: Gamma can be empty or disconnected and theta is arbitrary Int. -/
theorem no_fsc_iff_accessible {Γ : Finset Site2} (η : Field Γ) : NoFSC η ↔ Accessible η :=
  (GammaGraph.no_fsc_iff η).trans ((RawGraph.no_fsc_iff_accessible (GammaGraph.graph Γ) none
    (GammaGraph.graph_connected Γ) (GammaGraph.fieldEquiv Γ η)).trans
      (GammaGraph.accessible_iff η).symm)

end FiniteAvalanches.Sandpile.RawInteger
