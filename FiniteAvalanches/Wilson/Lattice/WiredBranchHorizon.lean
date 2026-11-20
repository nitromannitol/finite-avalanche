import FiniteAvalanches.Wilson.Lattice.BranchHorizon
import FiniteAvalanches.Wilson.Lattice.WiredStack

/-! Finite branch horizons for almost every wired stack realization. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Every finite set of wired Wilson branch histories fits within some finite
common time horizon for almost every direction stack. -/
theorem wiredStack_ae_finite_branch_horizon (R : RootPair) (B : ℕ)
    (x : ℕ → FiniteWired.Vertex B) (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    ∀ᵐ σ ∂directionStackLaw (FiniteWired.Vertex B), ∃ N,
      ∀ i < n, (boundedBranchHistory (wiredHead B) x (wiredRoots R B).val k N σ (i + 1)).2.1 < N := by
  filter_upwards [wiredStack_ae_terminates R B k] with σ hσ
  obtain ⟨t, hrun, hterminal⟩ := hσ
  obtain ⟨S, l, hexplore, _⟩ := stackExplore_of_terminal (wiredRoots R B).val
    (wiredHead B) (fun v i => σ (v, i)) k t hrun hterminal ((List.range n).map x)
  exact exists_horizon_of_stackExplore (wiredHead B) x (wiredRoots R B).val k n σ S l hexplore

end
end FiniteAvalanches.Wilson.Lattice
