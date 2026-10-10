import FiniteAvalanches.Electrical.MaximumPrinciple
import FiniteAvalanches.Electrical.Geometry.Charging
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LocalHarnack
open scoped BigOperators Classical

variable {V E : Type*} [Fintype E]

omit [Fintype E] in
/-- A loop copy contributes nothing to the Laplacian at any vertex. -/
theorem laplacian_loop_term (a b : E → V) (phi : V → ℝ) (x : V) (e : E) (he : a e = b e) :
    ((if a e = x then phi x - phi (b e) else 0) +
      (if b e = x then phi x - phi (a e) else 0)) = 0 := by
  rw [← he]
  by_cases h : a e = x
  · simp [h]
  · simp [h]

/-- Harmonicity at `x` gives degree times the value as the sum of copied neighbor values. -/
theorem degree_mul_eq_sum_incident (a b : E → V) (phi : V → ℝ) (x : V)
    (hx : laplacian a b phi x = 0) :
    Geometry.degree a b x * phi x =
      ∑ e, ((if a e = x then phi (b e) else 0) + (if b e = x then phi (a e) else 0)) := by
  have key : Geometry.degree a b x * phi x -
      ∑ e, ((if a e = x then phi (b e) else 0) + (if b e = x then phi (a e) else 0)) =
        laplacian a b phi x := by
    unfold Geometry.degree laplacian
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> ring
  rw [hx] at key
  linarith

/-- For a nonnegative field harmonic at `x` with copy degree at most four, every edge copy
at `x` has other-endpoint value at most `4 * phi x`. Loops and parallel copies are kept. -/
theorem phi_le_four_mul_of_incident (a b : E → V) (phi : V → ℝ) (hphi : ∀ y, 0 ≤ phi y)
    (x : V) (hx : laplacian a b phi x = 0) (hdeg : Geometry.degree a b x ≤ 4) (e : E) :
    (a e = x → phi (b e) ≤ 4 * phi x) ∧ (b e = x → phi (a e) ≤ 4 * phi x) := by
  have hsum := degree_mul_eq_sum_incident a b phi x hx
  have hN : ∀ e' : E, 0 ≤ (if a e' = x then phi (b e') else 0) +
      (if b e' = x then phi (a e') else 0) := by
    intro e'
    have h1 := hphi (a e')
    have h2 := hphi (b e')
    split_ifs <;> linarith
  have hle : (if a e = x then phi (b e) else 0) + (if b e = x then phi (a e) else 0) ≤
      ∑ e', ((if a e' = x then phi (b e') else 0) + (if b e' = x then phi (a e') else 0)) :=
    Finset.single_le_sum (f := fun e' : E => (if a e' = x then phi (b e') else 0) +
      (if b e' = x then phi (a e') else 0)) (fun e' _ => hN e') (Finset.mem_univ e)
  have hbound : ∑ e', ((if a e' = x then phi (b e') else 0) +
      (if b e' = x then phi (a e') else 0)) ≤ 4 * phi x := by
    rw [← hsum]
    exact mul_le_mul_of_nonneg_right hdeg (hphi x)
  constructor
  · intro h
    have h1 : phi (b e) ≤ (if a e = x then phi (b e) else 0) +
        (if b e = x then phi (a e) else 0) := by
      rw [if_pos h]
      split_ifs <;> linarith [hphi (a e)]
    linarith
  · intro h
    have h1 : phi (a e) ≤ (if a e = x then phi (b e) else 0) +
        (if b e = x then phi (a e) else 0) := by
      rw [if_pos h]
      split_ifs <;> linarith [hphi (b e)]
    linarith

/-- Adjacency form of the local bound. -/
theorem phi_le_four_mul_of_adj (a b : E → V) (phi : V → ℝ) (hphi : ∀ y, 0 ≤ phi y)
    (x : V) (hx : laplacian a b phi x = 0) (hdeg : Geometry.degree a b x ≤ 4) {y : V}
    (hxy : (supportGraph a b).Adj x y) : phi y ≤ 4 * phi x := by
  obtain ⟨_, e, he | he⟩ := hxy
  · have h := (phi_le_four_mul_of_incident a b phi hphi x hx hdeg e).1 he.1
    rwa [he.2] at h
  · have h := (phi_le_four_mul_of_incident a b phi hphi x hx hdeg e).2 he.1
    rwa [he.2] at h

/-- A nonnegative harmonic field with zero value at `x` vanishes at every neighbor. -/
theorem phi_eq_zero_of_adj_of_eq_zero (a b : E → V) (phi : V → ℝ) (hphi : ∀ y, 0 ≤ phi y)
    (x : V) (hx : laplacian a b phi x = 0) (hdeg : Geometry.degree a b x ≤ 4) {y : V}
    (hxy : (supportGraph a b).Adj x y) (hz : phi x = 0) : phi y = 0 := by
  have h := phi_le_four_mul_of_adj a b phi hphi x hx hdeg hxy
  rw [hz] at h
  exact le_antisymm (by linarith) (hphi y)

/-- The two-terminal voltage is between its boundary values. -/
theorem voltage_bounds [Fintype V] (a b : E → V) (alpha beta : V) (phi : V → ℝ)
    (hB : ∀ x, ∃ y ∈ ({alpha, beta} : Finset V), (supportGraph a b).Reachable x y)
    (h0 : phi alpha = 0) (h1 : phi beta = 1)
    (hharm : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    ∀ x, 0 ≤ phi x ∧ phi x ≤ 1 := by
  have hmem : ∀ x ∈ ({alpha, beta} : Finset V), x = alpha ∨ x = beta := by
    intro x hx
    simpa using hx
  have hout : ∀ x, x ∉ ({alpha, beta} : Finset V) → laplacian a b phi x = 0 := by
    intro x hx
    have hxa : x ≠ alpha := fun h => hx (by simp [h])
    have hxb : x ≠ beta := fun h => hx (by simp [h])
    exact hharm x hxa hxb
  have hup := le_of_harmonic a b {alpha, beta} hB phi 1
    (fun x hx => by
      rcases hmem x hx with h | h
      · rw [h]; linarith
      · rw [h]; linarith)
    hout
  have hlow := le_of_harmonic a b {alpha, beta} hB ((-1 : ℝ) • phi) 0
    (fun x hx => by
      rcases hmem x hx with h | h
      · rw [h]; simp [h0]
      · rw [h]; norm_num [h1])
    (fun x hx => by rw [laplacian_smul, hout x hx, mul_zero])
  intro x
  refine ⟨?_, hup x⟩
  have h := hlow x
  simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul] at h
  linarith

/-- Incident-copy form of the voltage ratio: for `x ≠ alpha`, free or `x = beta`. -/
theorem phi_le_four_mul_of_incident_voltage [Fintype V] (a b : E → V) (alpha beta : V)
    (phi : V → ℝ)
    (hB : ∀ x, ∃ y ∈ ({alpha, beta} : Finset V), (supportGraph a b).Reachable x y)
    (h0 : phi alpha = 0) (h1 : phi beta = 1)
    (hharm : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → Geometry.degree a b x ≤ 4)
    {x : V} (hx : x ≠ alpha) (e : E) :
    (a e = x → phi (b e) ≤ 4 * phi x) ∧ (b e = x → phi (a e) ≤ 4 * phi x) := by
  have hbd := voltage_bounds a b alpha beta phi hB h0 h1 hharm
  by_cases hxb : x = beta
  · have hphix : phi x = 1 := by rw [hxb]; exact h1
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · linarith [(hbd (b e)).2]
    · linarith [(hbd (a e)).2]
  · exact phi_le_four_mul_of_incident a b phi (fun y => (hbd y).1) x
      (hharm x hx hxb) (hdeg x hx hxb) e

/-- Adjacency form of the voltage ratio; the excluded vertex `alpha` is the only exception. -/
theorem phi_le_four_mul_of_adj_voltage [Fintype V] (a b : E → V) (alpha beta : V)
    (phi : V → ℝ)
    (hB : ∀ x, ∃ y ∈ ({alpha, beta} : Finset V), (supportGraph a b).Reachable x y)
    (h0 : phi alpha = 0) (h1 : phi beta = 1)
    (hharm : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → Geometry.degree a b x ≤ 4)
    {x y : V} (hx : x ≠ alpha) (hxy : (supportGraph a b).Adj x y) : phi y ≤ 4 * phi x := by
  obtain ⟨_, e, he | he⟩ := hxy
  · have h := (phi_le_four_mul_of_incident_voltage a b alpha beta phi hB h0 h1 hharm hdeg
      hx e).1 he.1
    rwa [he.2] at h
  · have h := (phi_le_four_mul_of_incident_voltage a b alpha beta phi hB h0 h1 hharm hdeg
      hx e).2 he.1
    rwa [he.2] at h

/-- Two adjacent steps among vertices other than `alpha` give a mutual factor sixteen. -/
theorem phi_two_step_mutual [Fintype V] (a b : E → V) (alpha beta : V) (phi : V → ℝ)
    (hB : ∀ x, ∃ y ∈ ({alpha, beta} : Finset V), (supportGraph a b).Reachable x y)
    (h0 : phi alpha = 0) (h1 : phi beta = 1)
    (hharm : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → Geometry.degree a b x ≤ 4)
    {x w z : V} (hx : x ≠ alpha) (hw : w ≠ alpha) (hz : z ≠ alpha)
    (hxw : (supportGraph a b).Adj x w) (hwz : (supportGraph a b).Adj w z) :
    phi z ≤ 16 * phi x ∧ phi x ≤ 16 * phi z := by
  have step : ∀ {u v : V}, u ≠ alpha → (supportGraph a b).Adj u v → phi v ≤ 4 * phi u :=
    fun hu huv => phi_le_four_mul_of_adj_voltage a b alpha beta phi hB h0 h1 hharm hdeg hu huv
  have e1 := step hx hxw
  have e2 := step hw hwz
  have e3 := step hz hwz.symm
  have e4 := step hw hxw.symm
  constructor <;> linarith

/-- With positive endpoint values and endpoints that coincide, are adjacent, or are joined
through a vertex other than `alpha`, the ratio lies between `1/16` and `16`. -/
theorem ratio_bounds_of_near [Fintype V] (a b : E → V) (alpha beta : V) (phi : V → ℝ)
    (hB : ∀ x, ∃ y ∈ ({alpha, beta} : Finset V), (supportGraph a b).Reachable x y)
    (h0 : phi alpha = 0) (h1 : phi beta = 1)
    (hharm : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → Geometry.degree a b x ≤ 4)
    {x z : V} (hx : x ≠ alpha) (hz : z ≠ alpha) (hxpos : 0 < phi x) (hzpos : 0 < phi z)
    (hnear : z = x ∨ (supportGraph a b).Adj x z ∨
      ∃ w, w ≠ alpha ∧ (supportGraph a b).Adj x w ∧ (supportGraph a b).Adj w z) :
    1 / 16 ≤ phi z / phi x ∧ phi z / phi x ≤ 16 := by
  have step : ∀ {u v : V}, u ≠ alpha → (supportGraph a b).Adj u v → phi v ≤ 4 * phi u :=
    fun hu huv => phi_le_four_mul_of_adj_voltage a b alpha beta phi hB h0 h1 hharm hdeg hu huv
  have hboth : phi z ≤ 16 * phi x ∧ phi x ≤ 16 * phi z := by
    rcases hnear with hzx | hxz | ⟨w, hw, hxw, hwz⟩
    · rw [hzx]
      constructor <;> linarith
    · have e1 := step hx hxz
      have e2 := step hz hxz.symm
      constructor <;> linarith
    · exact phi_two_step_mutual a b alpha beta phi hB h0 h1 hharm hdeg hx hw hz hxw hwz
  constructor
  · rw [le_div_iff₀ hxpos]
    linarith [hboth.2]
  · rw [div_le_iff₀ hxpos]
    linarith [hboth.1]

#print axioms FiniteAvalanches.Electrical.LocalHarnack.laplacian_loop_term
#print axioms FiniteAvalanches.Electrical.LocalHarnack.degree_mul_eq_sum_incident
#print axioms FiniteAvalanches.Electrical.LocalHarnack.phi_le_four_mul_of_incident
#print axioms FiniteAvalanches.Electrical.LocalHarnack.phi_le_four_mul_of_adj
#print axioms FiniteAvalanches.Electrical.LocalHarnack.phi_eq_zero_of_adj_of_eq_zero
#print axioms FiniteAvalanches.Electrical.LocalHarnack.voltage_bounds
#print axioms FiniteAvalanches.Electrical.LocalHarnack.phi_le_four_mul_of_incident_voltage
#print axioms FiniteAvalanches.Electrical.LocalHarnack.phi_le_four_mul_of_adj_voltage
#print axioms FiniteAvalanches.Electrical.LocalHarnack.phi_two_step_mutual
#print axioms FiniteAvalanches.Electrical.LocalHarnack.ratio_bounds_of_near

end FiniteAvalanches.Electrical.LocalHarnack
