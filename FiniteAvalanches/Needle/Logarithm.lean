import FiniteAvalanches.Needle.Statement

open FiniteAvalanches.Sandpile.FiniteWired

namespace FiniteAvalanches.Needle
open LatticeProb
open scoped BigOperators Classical

/-- `h+2 ≤ h^2` for `h ≥ 2`, so `log (h+2) ≤ 2 log h`. -/
theorem log_add_two_le_two_mul_log {h : ℕ} (hh : 2 ≤ h) :
    Real.log ((h:ℝ)+2) ≤ 2*Real.log (h:ℝ) := by
  have hx : (2:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hm : (0:ℝ) ≤ ((h:ℝ)-2)*((h:ℝ)+1) :=
    mul_nonneg (by linarith only [hx]) (by linarith only [hx])
  have hsq : (h:ℝ)+2 ≤ (h:ℝ)^2 := by nlinarith only [hm]
  calc Real.log ((h:ℝ)+2) ≤ Real.log ((h:ℝ)^2) :=
        Real.log_le_log (by linarith only [hx]) hsq
    _ = 2*Real.log (h:ℝ) := by
        rw [Real.log_pow]; norm_num

/-- the `log (h+2)` bound transports to a `log h` bound with constant `2*C`. -/
theorem ct_needle_log_h : ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 10 ≤ h → ∀ z : Point,
    radius z = 2*h → ∃ (L : ℕ) (p : InBoxVertices h L),
      Function.Injective p.val ∧ p.val ⟨0, by omega⟩ ∈ box 2 h ∧ p.val ⟨L, by omega⟩ = z ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩) (p.val ⟨t.val+1, by omega⟩)) ∧
      wiredConductance (2*h) (zeroVertices h L p) ≤ C*Real.log h := by
  obtain ⟨C, hC, H⟩ := ct_needle
  refine ⟨2*C, by linarith, ?_⟩
  intro h hh z hz
  obtain ⟨L, p, hi, hb, he, ha, hc⟩ := H h hh z hz
  refine ⟨L, p, hi, hb, he, ha, ?_⟩
  have hlog := log_add_two_le_two_mul_log (h := h) (by omega)
  calc wiredConductance (2*h) (zeroVertices h L p) ≤ C*Real.log ((h:ℝ)+2) := hc
    _ ≤ C*(2*Real.log (h:ℝ)) := mul_le_mul_of_nonneg_left hlog hC.le
    _ = 2*C*Real.log (h:ℝ) := by ring

end FiniteAvalanches.Needle
