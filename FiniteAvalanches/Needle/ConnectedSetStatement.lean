import FiniteAvalanches.Needle.ConnectedSetApplication

set_option autoImplicit false
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open scoped Classical
namespace FiniteAvalanchesFrozen.Needle

/-- A connected lattice set joining a square to a prescribed outer boundary point
has conductance bounded by one universal logarithmic constant. -/
theorem connected_set_conductance_v2 : ∃ C : ℝ, 0 < C ∧
    ∀ h : ℕ, 10 ≤ h → ∀ w : Point, radius w = 2 * h →
    ∃ Z : Finset Point, ((lattice 2).induce (Z : Set Point)).Connected ∧
      (Z : Set Point) ⊆ box 2 (2 * h) ∧ box 2 h ⊆ (Z : Set Point) ∧ w ∈ Z ∧
      wiredConductance (2 * h)
        (Finset.univ.filter (fun x : Active (2 * h) => site x ∈ Z)) ≤ C * Real.log h := by
  exact ConnectedSetApplication.source_needle_connected_set

end FiniteAvalanchesFrozen.Needle
