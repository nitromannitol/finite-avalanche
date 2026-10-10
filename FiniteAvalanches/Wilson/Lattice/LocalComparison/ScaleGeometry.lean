import FiniteAvalanches.Wilson.Lattice.LocalComparison.ContactOrder
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace JointScaleGeometry
open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches (siteRadius siteRadius_le_iff)
open scoped Classical
noncomputable section

theorem siteRadius_triangle (a b c : Site 2) :
    siteRadius a c ≤ siteRadius a b + siteRadius b c := by
  apply (siteRadius_le_iff _ _ _).mpr
  intro i
  have hab := (siteRadius_le_iff a b (siteRadius a b)).mp le_rfl i
  have hbc := (siteRadius_le_iff b c (siteRadius b c)).mp le_rfl i
  have he : c i-a i = (b i-a i)+(c i-b i) := by ring
  rw [he, Nat.cast_add]
  exact (abs_add_le _ _).trans (add_le_add hab hbc)

theorem shifted_contacts_le (K : Finset (Site 2)) (w : Site 2) (r : ℕ)
    (hw : siteRadius 0 w ≤ r) (σ : ColorField) :
    localContacts (K : Set (Site 2)) w (2*r) σ ≤ kContacts K (3*(r : ℝ)) σ := by
  unfold localContacts kContacts
  apply JointContactOrder.contacts_subset
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_coe] at hx
  obtain ⟨hxW, hxK⟩ := hx
  have hwx := (mem_window w x (2*r)).mp hxW
  have hxR : siteRadius 0 x ≤ 3*r := by
    have ht := siteRadius_triangle 0 w x
    omega
  apply Finset.mem_filter.mpr
  refine ⟨hxK, ?_⟩
  exact_mod_cast hxR

/-- One source-sized kappa is selected before both scales and pays the literal 107 budget. -/
theorem exists_uniform_kappa (ε : ℝ) (hε : 0 < ε) :
    ∃ κ : ℕ, 30 ≤ κ ∧ 3424 ≤ ε*(κ : ℝ) ∧
      ∀ h r : ℕ, 10 ≤ h → h^κ ≤ r →
        10^30 ≤ r ∧ 2*h ≤ r ∧
        (κ : ℝ)*Real.log (h : ℝ) ≤ Real.log (r : ℝ) ∧
        107*Real.log (h : ℝ) ≤ (ε/2)*(Real.log (r : ℝ)/16) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (3424/ε)
  let κ := max 30 k
  have hκ : 30 ≤ κ := le_max_left _ _
  have hεk : 3424 ≤ ε*(κ : ℝ) := by
    have hdiv : 3424/ε < (κ : ℝ) := hk.trans_le (Nat.cast_le.mpr (le_max_right _ _))
    have he := (div_lt_iff₀ hε).mp hdiv
    nlinarith only [he]
  refine ⟨κ, hκ, hεk, ?_⟩
  intro h r hh hr
  have hscale : 10^30 ≤ r := by
    calc
      10^30 ≤ h^30 := Nat.pow_le_pow_left hh 30
      _ ≤ h^κ := Nat.pow_le_pow_right (by omega) hκ
      _ ≤ r := hr
  have htwo : 2*h ≤ r := by
    calc
      2*h ≤ h^2 := by nlinarith only [hh]
      _ ≤ h^κ := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ r := hr
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hlog : (κ : ℝ)*Real.log (h : ℝ) ≤ Real.log (r : ℝ) := by
    have hpow : (h : ℝ)^κ ≤ (r : ℝ) := by exact_mod_cast hr
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos hhpos κ) hpow
  have hlogh := Real.log_natCast_nonneg h
  have hpaid := mul_le_mul_of_nonneg_right hεk hlogh
  have hεlog := mul_le_mul_of_nonneg_left hlog hε.le
  refine ⟨hscale, htwo, hlog, ?_⟩
  nlinarith only [hpaid, hεlog]

end
end JointScaleGeometry
