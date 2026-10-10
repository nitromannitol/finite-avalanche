import FiniteAvalanches.Needle.Energy
import FiniteAvalanches.Needle.Conductance

open FiniteAvalanches.Sandpile.FiniteWired

namespace FiniteAvalanches.Needle
open LatticeProb
open scoped BigOperators Classical

theorem harmonic_sum_le_log (h : ℕ) (hh : 10 ≤ h) :
    (∑ s ∈ Finset.Icc 1 (2*h+1), 1/(s:ℝ)) ≤ 4*Real.log (h+2) := by
  have hsum : (∑ s ∈ Finset.Icc 1 (2*h+1), 1/(s:ℝ)) ≤ 1+Real.log (2*h+1) := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      one_div, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      harmonic_le_one_add_log (2*h+1)
  have h2 : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hL : Real.log 2 ≤ Real.log (h+2) :=
    Real.log_le_log (by norm_num) (by linarith only [show (0:ℝ) ≤ h from Nat.cast_nonneg h])
  have hM : Real.log (2*h+1) ≤ Real.log 2+Real.log (h+2) := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (h:ℝ)+2 ≠ 0)]
    apply Real.log_le_log (by positivity)
    linarith only [show (0:ℝ) ≤ h from Nat.cast_nonneg h]
  linarith only [hsum, h2, hL, hM]

/-- The needle trial has logarithmic once-counted Dirichlet energy. -/
theorem trial_energy_le_log (h L : ℕ) (hh : 10 ≤ h) (p : Fin (L+1) → Point) (z : Point)
    (hp : ∀ t, linf z (p t) ≤ 2*h-radius (p t)+1) :
    FiniteAvalanches.Electrical.energy (fun e : Edge (2*h) => (endpoints e).1)
      (fun e => (endpoints e).2) (trial h L p) ≤ 3840*Real.log (h+2) := by
  exact (trial_energy_le_harmonic h L p z hp).trans (by
    have hh := mul_le_mul_of_nonneg_left (harmonic_sum_le_log h hh) (by norm_num : (0:ℝ) ≤ 960)
    nlinarith only [hh])

/-- Uniformly for every boundary point, a literal simple needle has logarithmic conductance. -/
theorem needle (h : ℕ) (hh : 10 ≤ h) (z : Point) (hz : radius z = 2*h) :
    ∃ (L : ℕ) (p : InBoxVertices h L),
      Function.Injective p.val ∧ p.val ⟨0, by omega⟩ ∈ box 2 h ∧ p.val ⟨L, by omega⟩ = z ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩) (p.val ⟨t.val+1, by omega⟩)) ∧
      (∀ t, linf z (p.val t) ≤ 2*h-radius (p.val t)+1) ∧
      wiredConductance (2*h) (zeroVertices h L p) ≤ 3840*Real.log (h+2) := by
  obtain ⟨L, p, hi, hb, he, ha, hr⟩ := exists_radial_path h z hz
  let P : InBoxVertices h L := ⟨p, fun t => (hr t).1⟩
  refine ⟨L, P, hi, hb, he, ha, (fun t => (hr t).2), ?_⟩
  apply (wiredConductance_le_trial (2*h) (zeroVertices h L P) (trial h L p) rfl
    (fun x hx => trial_zero h L p x (Finset.mem_filter.mp hx).2)).trans
  exact trial_energy_le_log h L hh p z (fun t => (hr t).2)

end FiniteAvalanches.Needle
