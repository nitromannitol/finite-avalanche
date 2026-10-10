import FiniteAvalanches.Needle.Energy

set_option autoImplicit false
namespace Needle107WindowEnergy
open scoped BigOperators Classical

/-- Injective geometric indexing controls once-counted energy by a finite window. -/
theorem energy_le_card_window {V E K : Type} [Fintype E] [DecidableEq K]
    (a b : E → V) (f : V → ℝ) (key : E → K) (hkey : Function.Injective key)
    (W : Finset K) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ e, (f (a e)-f (b e))^2 ≤ if key e ∈ W then B else 0) :
    FiniteAvalanches.Electrical.energy a b f ≤ (W.card : ℝ)*B := by
  have hcard : (((Finset.univ.image key).filter (fun q => q ∈ W)).card : ℝ) ≤ W.card := by
    exact_mod_cast Finset.card_le_card (show
      (Finset.univ.image key).filter (fun q => q ∈ W) ⊆ W
      from fun q hq => (Finset.mem_filter.mp hq).2)
  unfold FiniteAvalanches.Electrical.energy
  calc
    _ ≤ ∑ e : E, if key e ∈ W then B else 0 := Finset.sum_le_sum fun e _ => h e
    _ = ∑ q ∈ Finset.univ.image key, if q ∈ W then B else 0 :=
      (Finset.sum_image (f := fun q => if q ∈ W then B else 0)
        (fun _ _ _ _ hh => hkey hh)).symm
    _ = ∑ _q ∈ (Finset.univ.image key).filter (fun q => q ∈ W), B :=
      (Finset.sum_filter (s := Finset.univ.image key) (fun q => q ∈ W) (fun _ => B)).symm
    _ = (((Finset.univ.image key).filter (fun q => q ∈ W)).card : ℝ)*B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (W.card : ℝ)*B := mul_le_mul_of_nonneg_right hcard hB

end Needle107WindowEnergy
