import FiniteAvalanches.Wilson.Lattice.WiredOriginalCopies
import FiniteAvalanches.Wilson.Lattice.DualCylinder

/-! Dual lattice edges crossing the original wired-box copies. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- The dual edge crossing the primal base edge has the corresponding shifted base. -/
theorem crossingEdgeEquiv_symm_baseEdge (p : Site 2 × Fin 2) :
    crossingEdgeEquiv.symm (baseEdge p) =
      baseEdge (p.1 - unit (1 - p.2), 1 - p.2) := by
  change edgeEquiv (dualBaseEquiv.symm (edgeEquiv.symm (baseEdge p))) = _
  rw [show edgeEquiv.symm (baseEdge p) = p from edgeEquiv.symm_apply_apply p]
  rfl

/-- Each wired copy determines the dual lattice edge crossing its original edge. -/
def wiredCopyDualEdge {B : ℕ} (e : FiniteWired.Edge B) : LatticeEdge :=
  crossingEdgeEquiv.symm (wiredCopyLatticeEdge e)

/-- Distinct wired copies have distinct crossing dual lattice edges. -/
theorem wiredCopyDualEdge_injective (B : ℕ) : Function.Injective (@wiredCopyDualEdge B) := by
  intro e f h
  exact wiredCopyLatticeEdge_injective B (crossingEdgeEquiv.symm.injective h)

/-- The dual field selects the edge crossing a wired copy exactly when the
original lattice edge is absent from the primal field. -/
theorem dualField_wiredCopyDualEdge (B : ℕ) (ω : EdgeField) (e : FiniteWired.Edge B) :
    dualField ω (wiredCopyDualEdge e) = !ω (wiredCopyLatticeEdge e) := by
  rw [dualField_apply_crossing]
  simp only [wiredCopyDualEdge, Equiv.apply_symm_apply]

end
end FiniteAvalanches.Wilson.Lattice
