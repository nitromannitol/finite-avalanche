import FiniteAvalanches.Wilson.Lattice.SimpleWalk
import LatticeProb.Walk.Ball
import LatticeProb.Walk.Infinite

set_option autoImplicit false
namespace FiniteAvalanches.External
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open scoped ENNReal

/-- Lawler–Limic, Theorem1, for iid square-lattice SRW and κ=1.
The obstacle hit starts at1; disk exit starts at0; avoidance includes the exit vertex. -/
axiom lawler_limic_beurling_srw_Z2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : Set (Site 2),
        (∀ j : ℕ, ∃ z ∈ A, (j : ℝ) ≤ euclidNorm z ∧ euclidNorm z < (j : ℝ) + 1) →
        ∀ k n : ℕ, 0 < k → k < n →
          pathLaw 2
            {ω | ∃ t : ℕ, 2 * (n : ℝ) ≤ euclidNorm (position 0 ω t) ∧
              ∀ s : ℕ, 1 ≤ s → s ≤ t →
                position 0 ω s ∉ {z | z ∈ A ∧ (k : ℝ) ≤ euclidNorm z ∧ euclidNorm z < n}} ≤
            ENNReal.ofReal (c * Real.sqrt ((k : ℝ) / n))

end FiniteAvalanches.External
