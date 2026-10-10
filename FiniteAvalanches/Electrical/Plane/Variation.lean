import FiniteAvalanches.Electrical.Plane.Orbits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Total variation along the actual finite rotation orbit, counting each incidence once. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

theorem orbit_prefix_variation {X : Type*} (f : Equiv.Perm X) (F : X → ℝ) (x : X) (n : ℕ) :
    |F ((f^n) x)-F x| ≤ ∑ k ∈ Finset.range n, |F (f ((f^k) x))-F ((f^k) x)| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,Finset.sum_range_succ]
    have ht : F (f ((f^n) x))-F x =
        (F (f ((f^n) x))-F ((f^n) x))+(F ((f^n) x)-F x) := by ring
    rw [ht]
    exact (abs_add_le _ _).trans (by linarith only [ih])

/-- Any two values on the actual orbit differ by at most its once-counted total variation. -/
theorem orbit_pair_variation {X : Type*} [Fintype X] (f : Equiv.Perm X) (F : X → ℝ)
    (x y : X) (h : f.SameCycle x y) :
    |F y-F x| ≤ ∑ z ∈ cyclePoints f x, |F (f z)-F z| := by
  obtain ⟨n,hn,hy⟩ := (isCycleOn_cyclePoints f x).exists_pow_eq
    ((mem_cyclePoints f x x).mpr (.refl f x)) ((mem_cyclePoints f x y).mpr h)
  have hi : Set.InjOn (fun k : ℕ => (f^k) x) (Finset.range n) := by
    intro i hi j hj hij
    exact orbit_pow_inj f x (lt_trans (Finset.mem_range.mp hi) hn)
      (lt_trans (Finset.mem_range.mp hj) hn) hij
  have hs : (Finset.range n).image (fun k => (f^k) x) ⊆ cyclePoints f x := by
    intro z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    exact (mem_cyclePoints f x _).mpr (by
      simpa only [Equiv.Perm.sameCycle_pow_right] using Equiv.Perm.SameCycle.refl f x)
  calc
    |F y-F x| ≤ ∑ k ∈ Finset.range n, |F (f ((f^k) x))-F ((f^k) x)| := by
      rw [← hy]
      exact orbit_prefix_variation f F x n
    _ = ∑ z ∈ (Finset.range n).image (fun k => (f^k) x), |F (f z)-F z| :=
      (Finset.sum_image (f := fun z => |F (f z)-F z|) hi).symm
    _ ≤ ∑ z ∈ cyclePoints f x, |F (f z)-F z| :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => abs_nonneg _)

end FiniteAvalanches.Electrical.Plane
