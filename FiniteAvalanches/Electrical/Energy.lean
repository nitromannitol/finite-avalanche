module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! Finite energy and incidence identities for individually indexed edge copies. -/

namespace FiniteAvalanches.Electrical

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Once-counted unit-conductance energy, retaining every edge copy. -/
noncomputable def energy (a b : E → V) (f : V → ℝ) : ℝ :=
  ∑ e, (f (a e) - f (b e)) ^ 2

/-- The edge energy weighted by the product of the endpoint values of `h`. -/
noncomputable def weightedEnergy (a b : E → V) (h g : V → ℝ) : ℝ :=
  ∑ e, h (a e) * h (b e) * (g (a e) - g (b e)) ^ 2

/-- Positive Laplacian as a literal incidence sum; both incidences of a loop vanish. -/
noncomputable def laplacian (a b : E → V) (h : V → ℝ) (x : V) : ℝ := by
  classical
  exact ∑ e, ((if a e = x then h x - h (b e) else 0) +
    (if b e = x then h x - h (a e) else 0))

theorem edge_ground_identity (hx hy gx gy : ℝ) :
    (hx * gx - hy * gy) ^ 2 = hx * hy * (gx - gy) ^ 2 +
      (hx - hy) * (hx * gx ^ 2 - hy * gy ^ 2) := by
  ring

omit [Fintype V] in
theorem energy_ground_edge_sum (a b : E → V) (h g : V → ℝ) :
    energy a b (fun x => h x * g x) = weightedEnergy a b h g +
      ∑ e, (h (a e) - h (b e)) *
        (h (a e) * g (a e) ^ 2 - h (b e) * g (b e) ^ 2) := by
  unfold energy weightedEnergy
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ =>
    edge_ground_identity (h (a e)) (h (b e)) (g (a e)) (g (b e))

theorem incidence_sum (a b : E → V) (h w : V → ℝ) :
    (∑ x, w x * laplacian a b h x) =
      ∑ e, (h (a e) - h (b e)) * (w (a e) - w (b e)) := by
  classical
  simp only [laplacian, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem ground_identity (a b : E → V) (h g : V → ℝ) :
    energy a b (fun x => h x * g x) = weightedEnergy a b h g +
      ∑ x, h x * g x ^ 2 * laplacian a b h x := by
  rw [incidence_sum a b h (fun x => h x * g x ^ 2)]
  exact energy_ground_edge_sum a b h g

theorem energy_eq_incidence_sum (a b : E → V) (h : V → ℝ) :
    energy a b h = ∑ x, h x * laplacian a b h x := by
  rw [incidence_sum a b h h]
  unfold energy
  exact Finset.sum_congr rfl fun e _ => by ring

/-- Unit boundary values turn energy into the sum of the two boundary fluxes. -/
theorem energy_eq_two_terminal_flux (a b : E → V) (h : V → ℝ)
    (a0 a1 beta : V) (ha : a0 ≠ a1)
    (hh0 : h a0 = 1) (hh1 : h a1 = 1) (hhb : h beta = 0)
    (hharm : ∀ x, x ≠ a0 → x ≠ a1 → x ≠ beta → laplacian a b h x = 0) :
    energy a b h = laplacian a b h a0 + laplacian a b h a1 := by
  classical
  rw [energy_eq_incidence_sum]
  have hpoint (x : V) : h x * laplacian a b h x =
      (if x = a0 then laplacian a b h a0 else 0) +
      (if x = a1 then laplacian a b h a1 else 0) := by
    by_cases hx0 : x = a0
    · subst x
      simp only [hh0, one_mul, ite_true, if_neg ha, add_zero]
    by_cases hx1 : x = a1
    · subst x
      simp only [hh1, one_mul, if_neg hx0, ite_true, zero_add]
    by_cases hxb : x = beta
    · subst x
      simp only [hhb, zero_mul, if_neg hx0, if_neg hx1, add_zero]
    · simp only [hharm x hx0 hx1 hxb, mul_zero, if_neg hx0, if_neg hx1, add_zero]
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [Fintype V] in
theorem energy_add_const (a b : E → V) (f : V → ℝ) (c : ℝ) :
    energy a b (fun x => c + f x) = energy a b f := by
  unfold energy
  exact Finset.sum_congr rfl fun e _ => by ring

omit [Fintype V] in
theorem energy_one_sub (a b : E → V) (f : V → ℝ) :
    energy a b (fun x => 1 - f x) = energy a b f := by
  unfold energy
  exact Finset.sum_congr rfl fun e _ => by ring

omit [Fintype V] in
/-- Transport vertices while retaining the same edge-copy index. -/
theorem energy_pullback {W : Type*} (q : W → V) (a b : E → W) (f : V → ℝ) :
    energy a b (fun x => f (q x)) = energy (fun e => q (a e)) (fun e => q (b e)) f := by
  rfl

omit [Fintype V] in
theorem weightedEnergy_sub_const (a b : E → V) (h f : V → ℝ) (c : ℝ) :
    weightedEnergy a b h (fun x => f x - c) = weightedEnergy a b h f := by
  unfold weightedEnergy
  exact Finset.sum_congr rfl fun e _ => by ring

open scoped Classical in
/-- Counting the two endpoint incidences gives exactly twice the once-counted energy. -/
theorem ordered_incidence_energy (a b : E → V) (f : V → ℝ) :
    (∑ x, ∑ e,
      ((if a e = x then (f x - f (b e)) ^ 2 else 0) +
       (if b e = x then (f x - f (a e)) ^ 2 else 0))) = 2 * energy a b f := by
  classical
  rw [Finset.sum_comm]
  calc
    _ = ∑ e, 2 * (f (a e) - f (b e)) ^ 2 := by
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    _ = 2 * energy a b f := by rw [energy, Finset.mul_sum]

/-- Energy of the ground-state trial function for explicit three-terminal Dirichlet data. -/
theorem ground_trial_energy (a b : E → V) (h f : V → ℝ)
    (a0 a1 beta : V) (ha : a0 ≠ a1)
    (hh0 : h a0 = 1) (hh1 : h a1 = 1) (hhb : h beta = 0)
    (hf0 : f a0 = 0) (hf1 : f a1 = 1)
    (hharm : ∀ x, x ≠ a0 → x ≠ a1 → x ≠ beta → laplacian a b h x = 0) :
    energy a b (fun x => (1 / 2 : ℝ) + h x * (f x - 1 / 2)) =
      (laplacian a b h a0 + laplacian a b h a1) / 4 +
        weightedEnergy a b h f := by
  classical
  rw [energy_add_const, ground_identity, weightedEnergy_sub_const]
  have hpoint (x : V) : h x * (f x - 1 / 2) ^ 2 * laplacian a b h x =
      (if x = a0 then laplacian a b h a0 / 4 else 0) +
      (if x = a1 then laplacian a b h a1 / 4 else 0) := by
    by_cases hx0 : x = a0
    · subst x
      simp only [hh0, hf0, ite_true, if_neg ha]
      ring
    by_cases hx1 : x = a1
    · subst x
      simp only [hh1, hf1, if_neg hx0, ite_true]
      ring
    by_cases hxb : x = beta
    · subst x
      simp only [hhb, zero_mul, if_neg hx0, if_neg hx1, add_zero]
    · simp only [hharm x hx0 hx1 hxb, mul_zero, if_neg hx0, if_neg hx1, add_zero]
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Background-energy form of the trial identity, without any response coefficients. -/
theorem ground_trial_energy_eq_background (a b : E → V) (h f : V → ℝ)
    (a0 a1 beta : V) (ha : a0 ≠ a1)
    (hh0 : h a0 = 1) (hh1 : h a1 = 1) (hhb : h beta = 0)
    (hf0 : f a0 = 0) (hf1 : f a1 = 1)
    (hharm : ∀ x, x ≠ a0 → x ≠ a1 → x ≠ beta → laplacian a b h x = 0) :
    energy a b (fun x => (1 / 2 : ℝ) + h x * (f x - 1 / 2)) =
      energy a b h / 4 + weightedEnergy a b h f := by
  rw [ground_trial_energy a b h f a0 a1 beta ha hh0 hh1 hhb hf0 hf1 hharm,
    energy_eq_two_terminal_flux a b h a0 a1 beta ha hh0 hh1 hhb hharm]

omit [Fintype V] in
theorem laplacian_one_sub (a b : E → V) (phi : V → ℝ) (x : V) :
    laplacian a b (fun y => 1 - phi y) x = -laplacian a b phi x := by
  classical
  unfold laplacian
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

/-- Trial-energy identity in voltage coordinates for explicit Dirichlet data. -/
theorem ground_trial_energy_of_voltage (a b : E → V) (phi f : V → ℝ)
    (a0 a1 beta : V) (ha : a0 ≠ a1)
    (hp0 : phi a0 = 0) (hp1 : phi a1 = 0) (hpb : phi beta = 1)
    (hf0 : f a0 = 0) (hf1 : f a1 = 1)
    (hph : ∀ x, x ≠ a0 → x ≠ a1 → x ≠ beta → laplacian a b phi x = 0) :
    energy a b (fun x => (1 / 2 : ℝ) + (1 - phi x) * (f x - 1 / 2)) =
      energy a b phi / 4 + weightedEnergy a b (fun x => 1 - phi x) f := by
  have hh0 : 1 - phi a0 = 1 := by rw [hp0, sub_zero]
  have hh1 : 1 - phi a1 = 1 := by rw [hp1, sub_zero]
  have hhb : 1 - phi beta = 0 := by rw [hpb, sub_self]
  have hharm (x : V) (hx0 : x ≠ a0) (hx1 : x ≠ a1) (hxb : x ≠ beta) :
      laplacian a b (fun y => 1 - phi y) x = 0 := by
    rw [laplacian_one_sub, hph x hx0 hx1 hxb, neg_zero]
  rw [ground_trial_energy_eq_background a b (fun x => 1 - phi x) f
    a0 a1 beta ha hh0 hh1 hhb hf0 hf1 hharm, energy_one_sub]

end FiniteAvalanches.Electrical


