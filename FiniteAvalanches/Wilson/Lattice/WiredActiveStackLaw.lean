import FiniteAvalanches.Wilson.Lattice.WiredSingleRootCyclePopping
import FiniteAvalanches.Wilson.Lattice.WiredStackCopies
import FiniteAvalanches.Probability.UniformMap

/-! Active wired vertices retain ordinary independent direction stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping FiniteAvalanches.Wilson.CopiedNetwork
open scoped Classical

noncomputable section

/-- The four lattice directions are the four original copies incident to an
active wired vertex. -/
def wiredActiveCopyEquiv {B : ℕ} (x : FiniteWired.Active B) :
    FiniteWired.Direction ≃ IncidentCopy (WiredTrees.graph B) (some x) :=
  wiredDirectionIncidentEquiv x

/-- The head of an active incident copy is the corresponding wired lattice step. -/
theorem incidentCopyHead_eq_wiredHead {B : ℕ} (x : FiniteWired.Active B)
    (e : IncidentCopy (WiredTrees.graph B) (some x)) :
    incidentCopyHead (WiredTrees.graph B) (some x) e =
      wiredHead B (some x) ((wiredActiveCopyEquiv x).symm e) := by
  have h := wiredDirectionIncident_other x ((wiredActiveCopyEquiv x).symm e)
  change incidentCopyHead (WiredTrees.graph B) (some x)
    (wiredActiveCopyEquiv x ((wiredActiveCopyEquiv x).symm e)) = _ at h
  simpa only [Equiv.apply_symm_apply] using h

/-- The uniform incident copy at an active vertex gives a uniform lattice direction. -/
theorem uniformIncidentCopy_map_direction {B : ℕ} (x : FiniteWired.Active B) :
    (FiniteAvalanches.uniformMeasure (IncidentCopy (WiredTrees.graph B) (some x))).map
      (wiredActiveCopyEquiv x).symm = directionLaw := by
  exact FiniteAvalanches.uniform_measure_map_equiv (wiredActiveCopyEquiv x).symm

/-- The lattice directions carried by all active-vertex incident stacks. -/
def wiredActiveDirectionStacks (B : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1) :
    FiniteWired.Active B × ℕ → FiniteWired.Direction :=
  fun p => (wiredActiveCopyEquiv p.1).symm (σ (some p.1, p.2))

/-- Projecting the variable incident stacks onto active vertices gives the
product law of independent uniform four-direction stacks. -/
theorem variableStackLaw_map_activeDirections (B : ℕ) :
    (variableStackLaw (IncidentCopy (WiredTrees.graph B))).map (wiredActiveDirectionStacks B) =
      directionStackLaw (FiniteWired.Active B) := by
  let f : FiniteWired.Active B × ℕ → FiniteWired.Vertex B × ℕ :=
    fun p => (some p.1, p.2)
  have hf : Function.Injective f := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have he : (some x, i) = (some y, j) := h
    cases Prod.mk.inj he with
    | intro hxy hij => exact Prod.ext (Option.some.inj hxy) hij
  let P : (p : FiniteWired.Vertex B × ℕ) → Measure (IncidentCopy (WiredTrees.graph B) p.1) :=
    fun p => FiniteAvalanches.uniformMeasure (IncidentCopy (WiredTrees.graph B) p.1)
  have hrestrict := Measure.map_infinitePi_infinitePi_of_inj (P := P) hf
  let g : ((p : FiniteWired.Active B × ℕ) → IncidentCopy (WiredTrees.graph B) (some p.1)) →
      (FiniteWired.Active B × ℕ → FiniteWired.Direction) :=
    fun σ p => (wiredActiveCopyEquiv p.1).symm (σ p)
  have hm : Measurable g := measurable_pi_iff.mpr fun p =>
    (measurable_of_finite (wiredActiveCopyEquiv p.1).symm).comp (measurable_pi_apply p)
  have hproj : Measurable (fun σ : (p : FiniteWired.Vertex B × ℕ) →
      IncidentCopy (WiredTrees.graph B) p.1 => fun p : FiniteWired.Active B × ℕ => σ (f p)) :=
    measurable_pi_iff.mpr fun p => measurable_pi_apply (f p)
  change (Measure.infinitePi P).map (wiredActiveDirectionStacks B) = _
  rw [show wiredActiveDirectionStacks B = g ∘ (fun σ p => σ (f p)) from rfl,
    ← Measure.map_map hm hproj, hrestrict]
  have hg : (Measure.infinitePi (fun p : FiniteWired.Active B × ℕ => P (f p))).map g =
      Measure.infinitePi (fun _ : FiniteWired.Active B × ℕ => directionLaw) := by
    rw [Measure.infinitePi_map_pi (fun p : FiniteWired.Active B × ℕ => P (f p))
      (fun p => measurable_of_finite (wiredActiveCopyEquiv p.1).symm)]
    congr 1
    funext p
    exact uniformIncidentCopy_map_direction p.1
  exact hg

end
end FiniteAvalanches.Wilson.Lattice
