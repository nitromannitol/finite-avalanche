module

public import FiniteAvalanches.Electrical.Geometry.Oscillation

/-! Dirichlet charging on literal finite edge copies, including parallel copies. -/

@[expose] public section

namespace FiniteAvalanches.Electrical.Geometry

open scoped BigOperators Classical

noncomputable def selectedCharge {V E : Type*} (q : V → Option E) (B : E → ℝ) (v : V) : ℝ :=
  (q v).elim 0 B

noncomputable def degree {V E : Type*} [Fintype E] (a b : E → V) (v : V) : ℝ :=
  ∑ e, ((if a e = v then 1 else 0) + (if b e = v then 1 else 0))

theorem sum_degree_mul {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (A : V → ℝ) :
    (∑ v, degree a b v * A v) = ∑ e, (A (a e)+A (b e)) := by
  simp only [degree, Finset.sum_mul, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.sum_comm] <;> simp

theorem sum_selectedCharge_le {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (q : V → Option E) (B : E → ℝ)
    (hB : ∀ e, 0 ≤ B e) (hq : ∀ v e, q v = some e → v = a e ∨ v = b e) :
    (∑ v, selectedCharge q B v) ≤ 2*∑ e, B e := by
  have h : ∀ v, selectedCharge q B v ≤
      ∑ e, ((if a e = v then B e else 0)+(if b e = v then B e else 0)) := by
    intro v
    have hn : ∀ e, 0 ≤ (if a e = v then B e else 0)+(if b e = v then B e else 0) := by
      intro e
      exact add_nonneg (by split <;> simp_all) (by split <;> simp_all)
    cases heq : q v with
    | none => simpa [selectedCharge, heq] using Finset.sum_nonneg (fun e _ => hn e)
    | some e =>
      have hsingle := Finset.single_le_sum (s := Finset.univ) (fun e _ => hn e) (Finset.mem_univ e)
      have hi := hq v e heq
      have hle : B e ≤ (if a e = v then B e else 0)+(if b e = v then B e else 0) := by
        rcases hi with rfl | rfl
        · simp only [ite_true]; split <;> linarith [hB e]
        · simp only [ite_true]; split <;> linarith [hB e]
      simpa [selectedCharge, heq] using hle.trans hsingle
  calc
    _ ≤ ∑ v, ∑ e, ((if a e = v then B e else 0)+(if b e = v then B e else 0)) :=
      Finset.sum_le_sum (fun v _ => h v)
    _ = 2*∑ e, B e := by rw [Finset.sum_comm]; simp [Finset.sum_add_distrib, two_mul]

theorem sum_endpoint_charge_le {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (q : V → Option E) (B : E → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hB : ∀ e, 0 ≤ B e) (hq : ∀ v e, q v = some e → v = a e ∨ v = b e)
    (hdeg : ∀ v, q v ≠ none → degree a b v ≤ d) :
    (∑ e, (selectedCharge q B (a e)+selectedCharge q B (b e))) ≤ 2*d*∑ e, B e := by
  have hn : ∀ v, 0 ≤ selectedCharge q B v := by
    intro v; unfold selectedCharge; cases q v <;> simp_all
  calc
    _ = ∑ v, degree a b v * selectedCharge q B v := (sum_degree_mul a b _).symm
    _ ≤ ∑ v, d*selectedCharge q B v := by
      apply Finset.sum_le_sum
      intro v _
      by_cases h : q v = none
      · simp [selectedCharge, h]
      · exact mul_le_mul_of_nonneg_right (hdeg v h) (hn v)
    _ = d*∑ v, selectedCharge q B v := (Finset.mul_sum ..).symm
    _ ≤ d*(2*∑ e, B e) := mul_le_mul_of_nonneg_left (sum_selectedCharge_le a b q B hB hq) hd
    _ = _ := by ring

/-- The three actual comparison increments obey the elementary square bound. -/
theorem sum_three_sq_le (u v w : ℝ) :
    (u+v+w)^2 ≤ 3*(u^2+v^2+w^2) := by
  nlinarith [sq_nonneg (u-v), sq_nonneg (u-w), sq_nonneg (v-w)]

/-- Pointwise geometric input to the charging rule. No summed energy estimate is a premise. -/
theorem angular_comparison_sq_le {V E : Type*} (Q : E → Square) (q : V → Option E)
    (epsilon y0 lambda : ℝ) (he : 0 < epsilon) (hl : 1 ≤ lambda)
    (f : V → ℝ) (p : V → ℝ × ℝ) (v w : V) (e : E) (z t : ℝ × ℝ)
    (hz : z ∈ ((Q e).dilate lambda (by linarith)).carrier)
    (ht : t ∈ ((Q e).dilate lambda (by linarith)).carrier)
    (hv : match q v with
      | none => f v = angular epsilon y0 z
      | some i => f v = angular epsilon y0 (p v) ∧
        p v ∈ ((Q i).dilate lambda (by linarith)).carrier ∧
        z ∈ ((Q i).dilate lambda (by linarith)).carrier)
    (hw : match q w with
      | none => f w = angular epsilon y0 t
      | some i => f w = angular epsilon y0 (p w) ∧
        p w ∈ ((Q i).dilate lambda (by linarith)).carrier ∧
        t ∈ ((Q i).dilate lambda (by linarith)).carrier) :
    (f v-f w)^2 ≤ 3*(((Q e).angularOsc epsilon y0 lambda hl he)^2 +
      selectedCharge q (fun i => ((Q i).angularOsc epsilon y0 lambda hl he)^2) v +
      selectedCharge q (fun i => ((Q i).angularOsc epsilon y0 lambda hl he)^2) w) := by
  have osc {i : E} {z t : ℝ × ℝ}
      (hz : z ∈ ((Q i).dilate lambda (by linarith)).carrier)
      (ht : t ∈ ((Q i).dilate lambda (by linarith)).carrier) :
      (angular epsilon y0 z-angular epsilon y0 t)^2 ≤ ((Q i).angularOsc epsilon y0 lambda hl he)^2 := by
    have h := abs_sub_le_oscillation hz ht ⟨1,fun z _ w _ => angular_sub_le_one epsilon y0 he z w⟩
    have hn := ((Q i).angularOsc_bounds epsilon y0 lambda he hl).1
    have hh := (sq_le_sq₀ (abs_nonneg _) hn).mpr h
    simpa only [sq_abs] using hh
  have hv' : (f v-angular epsilon y0 z)^2 ≤
      selectedCharge q (fun i => ((Q i).angularOsc epsilon y0 lambda hl he)^2) v := by
    cases hq : q v with
    | none => simp [hq] at hv; simp [selectedCharge, hq, hv]
    | some i => simp only [hq] at hv; simpa [selectedCharge,hq,hv.1] using osc hv.2.1 hv.2.2
  have hw' : (angular epsilon y0 t-f w)^2 ≤
      selectedCharge q (fun i => ((Q i).angularOsc epsilon y0 lambda hl he)^2) w := by
    cases hq : q w with
    | none => simp [hq] at hw; simp [selectedCharge, hq, hw]
    | some i => simp only [hq] at hw; simpa [selectedCharge,hq,hw.1] using osc hw.2.2 hw.2.1
  have hm := osc hz ht
  have h3 := sum_three_sq_le (f v-angular epsilon y0 z)
    (angular epsilon y0 z-angular epsilon y0 t) (angular epsilon y0 t-f w)
  have heq : f v-angular epsilon y0 z+(angular epsilon y0 z-angular epsilon y0 t)+
      (angular epsilon y0 t-f w) = f v-f w := by ring
  rw [heq] at h3
  linarith only [h3, hv', hw', hm]

/-- Literal endpoint comparison data, with no selected square at a terminal or zero-current vertex. -/
def endpointFits {V E : Type*} (Q : E → Square) (q : V → Option E)
    (epsilon y0 lambda : ℝ) (hl : 1 ≤ lambda) (f : V → ℝ) (p : V → ℝ × ℝ)
    (v : V) (z : ℝ × ℝ) : Prop :=
  match q v with
  | none => f v = angular epsilon y0 z
  | some i => f v = angular epsilon y0 (p v) ∧
    p v ∈ ((Q i).dilate lambda (by linarith)).carrier ∧
    z ∈ ((Q i).dilate lambda (by linarith)).carrier

/-- Once-per-copy weighted Dirichlet charging, with an actual finite exceptional set. -/
theorem dirichlet_charging_le {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (Q : E → Square) (q : V → Option E)
    (epsilon y0 lambda d : ℝ) (he : 0 < epsilon) (hl : 1 ≤ lambda) (hd : 0 ≤ d)
    (f weight : V → ℝ) (p : V → ℝ × ℝ) (z t : E → ℝ × ℝ) (bad : Finset E)
    (hf : ∀ e ∈ bad, 0 ≤ f (a e) ∧ f (a e) ≤ 1 ∧ 0 ≤ f (b e) ∧ f (b e) ≤ 1)
    (hw : ∀ v, 0 ≤ weight v ∧ weight v ≤ 1)
    (hq : ∀ v e, q v = some e → v = a e ∨ v = b e)
    (hdeg : ∀ v, q v ≠ none → degree a b v ≤ d)
    (hz : ∀ e, e ∉ bad → weight (a e)*weight (b e) ≠ 0 →
      z e ∈ ((Q e).dilate lambda (by linarith)).carrier ∧
      t e ∈ ((Q e).dilate lambda (by linarith)).carrier)
    (ha : ∀ e, e ∉ bad → weight (a e)*weight (b e) ≠ 0 →
      endpointFits Q q epsilon y0 lambda hl f p (a e) (z e))
    (hb : ∀ e, e ∉ bad → weight (a e)*weight (b e) ≠ 0 →
      endpointFits Q q epsilon y0 lambda hl f p (b e) (t e)) :
    (∑ e, weight (a e)*weight (b e)*(f (a e)-f (b e))^2) ≤
      (bad.card : ℝ) + 3*(1+2*d)*∑ e, ((Q e).angularOsc epsilon y0 lambda hl he)^2 := by
  let B := fun e => ((Q e).angularOsc epsilon y0 lambda hl he)^2
  have hB : ∀ e, 0 ≤ B e := fun e => sq_nonneg _
  have hA : ∀ v, 0 ≤ selectedCharge q B v := by
    intro v; unfold selectedCharge; cases q v <;> simp_all
  have hterm : ∀ e, weight (a e)*weight (b e)*(f (a e)-f (b e))^2 ≤
      (if e ∈ bad then 1 else 0) + 3*(B e+selectedCharge q B (a e)+selectedCharge q B (b e)) := by
    intro e
    have hweight1 : weight (a e)*weight (b e) ≤ 1 := by
      nlinarith [(hw (a e)).1, (hw (a e)).2, (hw (b e)).1, (hw (b e)).2]
    have henergy : weight (a e)*weight (b e)*(f (a e)-f (b e))^2 ≤ (f (a e)-f (b e))^2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight1 (sq_nonneg _)
    have hn : 0 ≤ 3*(B e+selectedCharge q B (a e)+selectedCharge q B (b e)) :=
      mul_nonneg (by norm_num) (add_nonneg (add_nonneg (hB e) (hA (a e))) (hA (b e)))
    by_cases heBad : e ∈ bad
    · have hdiff : (f (a e)-f (b e))^2 ≤ 1 := by
        have h := hf e heBad
        nlinarith [h.1,h.2.1,h.2.2.1,h.2.2.2]
      simp only [if_pos heBad]
      linarith only [henergy, hdiff, hn]
    · simp only [if_neg heBad, zero_add]
      by_cases hzero : weight (a e)*weight (b e) = 0
      · simpa only [hzero, zero_mul] using hn
      · exact henergy.trans (angular_comparison_sq_le Q q epsilon y0 lambda he hl f p
          (a e) (b e) e (z e) (t e) (hz e heBad hzero).1 (hz e heBad hzero).2
          (ha e heBad hzero) (hb e heBad hzero))
  have hend := sum_endpoint_charge_le a b q B d hd hB hq hdeg
  calc
    _ ≤ ∑ e, ((if e ∈ bad then 1 else 0) + 3*(B e+selectedCharge q B (a e)+selectedCharge q B (b e))) :=
      Finset.sum_le_sum (fun e _ => hterm e)
    _ = (bad.card : ℝ) + 3*((∑ e, B e) + ∑ e, (selectedCharge q B (a e)+selectedCharge q B (b e))) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      have heq : (∑ e : E, if e ∈ bad then (1:ℝ) else 0) = (bad.card : ℝ) := by simp
      rw [heq]
      ring
    _ ≤ (bad.card : ℝ) + 3*((∑ e, B e) + 2*d*∑ e, B e) := by linarith only [hend]
    _ = _ := by dsimp [B]; ring

end FiniteAvalanches.Electrical.Geometry
