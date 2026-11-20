import FiniteAvalanches.Wilson.Lattice.WiredActiveStackLaw

/-! Coupling active direction stacks with the full wired incident stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Restrict ordinary wired direction stacks to their active vertices. -/
def activeDirectionProjection (B : ℕ)
    (σ : FiniteWired.Vertex B × ℕ → FiniteWired.Direction) :
    FiniteWired.Active B × ℕ → FiniteWired.Direction :=
  fun p => σ (some p.1, p.2)

/-- Extend active stacks by an arbitrary constant stack at the wired vertex. -/
def padActiveDirectionStacks (B : ℕ)
    (σ : FiniteWired.Active B × ℕ → FiniteWired.Direction) :
    FiniteWired.Vertex B × ℕ → FiniteWired.Direction
  | (none, _) => (0, false)
  | (some x, i) => σ (x, i)

/-- Active stacks form the expected independent uniform product law. -/
theorem directionStackLaw_map_activeProjection (B : ℕ) :
    (directionStackLaw (FiniteWired.Vertex B)).map (activeDirectionProjection B) =
      directionStackLaw (FiniteWired.Active B) := by
  let f : FiniteWired.Active B × ℕ → FiniteWired.Vertex B × ℕ :=
    fun p => (some p.1, p.2)
  have hf : Function.Injective f := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have he : (some x, i) = (some y, j) := h
    cases Prod.mk.inj he with
    | intro hxy hij => exact Prod.ext (Option.some.inj hxy) hij
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ => directionLaw) hf

/-- Padding active stacks is measurable. -/
theorem measurable_padActiveDirectionStacks (B : ℕ) :
    Measurable (padActiveDirectionStacks B) := by
  apply measurable_pi_iff.mpr
  rintro ⟨v, i⟩
  cases v with
  | none => exact measurable_const
  | some x => exact measurable_pi_apply (x, i)

/-- Every measurable event insensitive to the sink stack has the same mass
under incident-copy stacks and ordinary direction stacks. -/
theorem variableStackLaw_active_event_eq (B : ℕ)
    (E : Set (FiniteWired.Vertex B × ℕ → FiniteWired.Direction)) (hE : MeasurableSet E)
    (hstable : ∀ σ, padActiveDirectionStacks B (activeDirectionProjection B σ) ∈ E ↔ σ ∈ E) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B))
      {σ | padActiveDirectionStacks B (wiredActiveDirectionStacks B σ) ∈ E} =
      directionStackLaw (FiniteWired.Vertex B) E := by
  let A := (padActiveDirectionStacks B) ⁻¹' E
  have hA : MeasurableSet A := hE.preimage (measurable_padActiveDirectionStacks B)
  have he := congrArg (fun μ : Measure (FiniteWired.Active B × ℕ → FiniteWired.Direction) => μ A)
    (variableStackLaw_map_activeDirections B)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact (measurable_of_finite (wiredActiveCopyEquiv p.1).symm).comp
        (measurable_pi_apply (some p.1, p.2))) hA] at he
  have hd := congrArg (fun μ : Measure (FiniteWired.Active B × ℕ → FiniteWired.Direction) => μ A)
    (directionStackLaw_map_activeProjection B)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact measurable_pi_apply (some p.1, p.2)) hA] at hd
  have hset : (activeDirectionProjection B) ⁻¹' A = E := by
    ext σ
    exact hstable σ
  rw [hset] at hd
  exact he.trans hd.symm

end
end FiniteAvalanches.Wilson.Lattice
