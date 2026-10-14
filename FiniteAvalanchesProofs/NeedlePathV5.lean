import FiniteAvalanches.Needle.Direct.Proof

set_option autoImplicit false
open LatticeProb FiniteAvalanches.Needle
namespace FiniteAvalanchesProofs.NeedlePathV5

theorem needle_path : ∃ C : ℝ, ∀ h : ℕ, 10 ≤ h → ∀ w : Point,
    radius w = 2 * h → ∃ (L : ℕ) (p : InBoxVertices h L),
      Function.Injective p.val ∧ p.val ⟨0, by omega⟩ = w ∧
      p.val ⟨L, by omega⟩ ∈ box 2 h ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩)
        (p.val ⟨t.val + 1, by omega⟩)) ∧
      wiredConductance (2 * h) (zeroVertices h L p) ≤ C * Real.log (h : ℝ) := by
  exact FiniteAvalanches.Needle.source_needle_path

end FiniteAvalanchesProofs.NeedlePathV5
