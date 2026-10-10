import FiniteAvalanches.Electrical.Energy
import LatticeProb.Network.Basic
import Mathlib.Tactic.Positivity

/-! Aggregating electrical quantities while retaining the original edge-copy index. -/

namespace FiniteAvalanches.Electrical

open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Supporting simple graph of the nonloop edge copies. -/
def supportGraph (a b : E → V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e, (a e = x ∧ b e = y) ∨ (b e = x ∧ a e = y)
  symm := ⟨by
    intro x y h
    obtain ⟨hne, e, he⟩ := h
    exact ⟨Ne.symm hne, e, he.elim (fun h => Or.inr ⟨h.2, h.1⟩)
      (fun h => Or.inl ⟨h.2, h.1⟩)⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- Conductance equal to edge-copy multiplicity, with loops removed. -/
noncomputable def conductance (a b : E → V) (x y : V) : ℝ :=
  if x = y then 0 else ∑ e,
    ((if a e = x ∧ b e = y then 1 else 0) +
     (if b e = x ∧ a e = y then 1 else 0))

omit [Fintype V] in
theorem conductance_nonneg (a b : E → V) (x y : V) : 0 ≤ conductance a b x y := by
  unfold conductance
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun e _ => add_nonneg (by positivity) (by positivity)

omit [Fintype V] in
theorem conductance_symm (a b : E → V) (x y : V) :
    conductance a b x y = conductance a b y x := by
  by_cases hxy : x = y
  · subst y; rfl
  simp only [conductance, if_neg hxy, if_neg (Ne.symm hxy)]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [and_comm]
  ring

omit [Fintype V] in
theorem isCond_conductance (a b : E → V) :
    LatticeProb.Network.IsCond (supportGraph a b) (conductance a b) := by
  refine ⟨conductance_symm a b, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨hne, e, he⟩ := hxy
    rw [conductance, if_neg hne]
    apply Finset.sum_pos'
    · intro e _
      exact add_nonneg (by positivity) (by positivity)
    · refine ⟨e, Finset.mem_univ e, ?_⟩
      rcases he with he | he
      · rw [if_pos he]
        positivity
      · rw [if_pos he]
        positivity
  · intro x y hxy
    by_cases hne : x = y
    · simp only [conductance, if_pos hne]
    · rw [conductance, if_neg hne]
      refine Finset.sum_eq_zero fun e _ => ?_
      have h1 : ¬ (a e = x ∧ b e = y) := fun he => hxy ⟨hne, e, Or.inl he⟩
      have h2 : ¬ (b e = x ∧ a e = y) := fun he => hxy ⟨hne, e, Or.inr he⟩
      simp only [if_neg h1, if_neg h2, add_zero]

omit [Fintype V] in
theorem conductance_mul (a b : E → V) (x y : V) (f : V → ℝ) (hf : f x = 0) :
    conductance a b x y * f y = ∑ e,
      ((if a e = x ∧ b e = y then f y else 0) +
       (if b e = x ∧ a e = y then f y else 0)) := by
  by_cases hxy : x = y
  · subst y
    simp only [conductance, hf, mul_zero, ite_self, add_zero,
      Finset.sum_const_zero]
  · rw [conductance, if_neg hxy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [add_mul, ite_mul, one_mul, zero_mul]

theorem sum_conductance_mul (a b : E → V) (x : V) (f : V → ℝ) (hf : f x = 0) :
    (∑ y, conductance a b x y * f y) = ∑ e,
      ((if a e = x then f (b e) else 0) +
       (if b e = x then f (a e) else 0)) := by
  simp_rw [conductance_mul a b x _ f hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero]

theorem sum_neighbor_conductance_mul (a b : E → V) (x : V) (f : V → ℝ) :
    (∑ y ∈ (supportGraph a b).neighborFinset x, conductance a b x y * f y) =
      ∑ y, conductance a b x y * f y := by
  apply LatticeProb.Network.sum_neighborFinset_eq_sum x Finset.univ
  · intro y hxy
    rw [(isCond_conductance a b).zero_of_not_adj hxy, zero_mul]
  · intro y _ _
    exact Finset.mem_univ y

theorem netLaplacian_eq_neg_laplacian (a b : E → V) (h : V → ℝ) (x : V) :
    LatticeProb.Network.netLaplacian (supportGraph a b) (conductance a b) h x =
      -laplacian a b h x := by
  rw [LatticeProb.Network.netLaplacian, sum_neighbor_conductance_mul,
    sum_conductance_mul a b x (fun y => h y - h x) (sub_self _)]
  unfold laplacian
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

theorem energyOn_eq_two_mul_energy (a b : E → V) (f : V → ℝ) :
    LatticeProb.Network.energyOn (supportGraph a b) (conductance a b) Finset.univ f =
      2 * energy a b f := by
  rw [LatticeProb.Network.energyOn_eq_sum]
  calc
    _ = ∑ x, ∑ e, ((if a e = x then (f x - f (b e)) ^ 2 else 0) +
        (if b e = x then (f x - f (a e)) ^ 2 else 0)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [sum_neighbor_conductance_mul,
        sum_conductance_mul a b x (fun y => (f x - f y) ^ 2) (by simp)]
    _ = 2 * energy a b f := ordered_incidence_energy a b f

end FiniteAvalanches.Electrical
