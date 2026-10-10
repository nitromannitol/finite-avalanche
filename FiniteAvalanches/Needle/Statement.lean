import FiniteAvalanches.Needle.Proof

open FiniteAvalanches.Sandpile.FiniteWired

namespace FiniteAvalanches.Needle
open LatticeProb
open scoped BigOperators Classical

/-- The universal constant precedes every scale and boundary point. -/
theorem ct_needle : ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 10 ≤ h → ∀ z : Point,
    radius z = 2*h → ∃ (L : ℕ) (p : InBoxVertices h L),
      Function.Injective p.val ∧ p.val ⟨0, by omega⟩ ∈ box 2 h ∧ p.val ⟨L, by omega⟩ = z ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩) (p.val ⟨t.val+1, by omega⟩)) ∧
      wiredConductance (2*h) (zeroVertices h L p) ≤ C*Real.log (h+2) := by
  refine ⟨3840, by norm_num, ?_⟩
  intro h hh z hz
  obtain ⟨L, p, hi, hb, he, ha, _, hc⟩ := needle h hh z hz
  exact ⟨L, p, hi, hb, he, ha, hc⟩

end FiniteAvalanches.Needle
