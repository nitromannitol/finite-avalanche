import FiniteAvalanches.Needle.ConnectedSetApplication
import FiniteAvalanchesProofs.Needle107V4

set_option autoImplicit false
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open scoped Classical
namespace FiniteAvalanchesFrozen.Needle107V4

theorem connected_set_conductance_107 :
    ∀ h : ℕ, 10 ≤ h → ∀ w : Point, radius w = 2 * h →
    ∃ Z : Finset Point, ((lattice 2).induce (Z : Set Point)).Connected ∧
      (Z : Set Point) ⊆ box 2 (2 * h) ∧ box 2 h ⊆ (Z : Set Point) ∧ w ∈ Z ∧
      wiredConductance (2 * h)
        (Finset.univ.filter (fun x : Active (2 * h) => site x ∈ Z)) ≤
          107 * Real.log h := by
  exact FiniteAvalanchesProofs.Needle107V4.connected_set_conductance_107

end FiniteAvalanchesFrozen.Needle107V4
