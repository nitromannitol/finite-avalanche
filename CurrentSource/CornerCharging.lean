import FiniteAvalanches.Electrical.Geometry.Charging

/-! Charging neighboring copied squares while excluding the copy being compared. -/

namespace FiniteAvalanches.Electrical.Geometry
open scoped BigOperators Classical
noncomputable section

/-- The total square budget at an eligible endpoint, with each incidence counted. -/
def incidentCharge {V E : Type} [Fintype E] (a b : E → V) (regular : V → Prop)
    (B : E → ℝ) (x : V) : ℝ :=
  ∑ q, ((if a q = x then if regular x then B q else 0 else 0) +
    (if b q = x then if regular x then B q else 0 else 0))

/-- The endpoint budget using only other original copied edges. -/
def otherIncidentCharge {V E : Type} [Fintype E] (a b : E → V) (regular : V → Prop)
    (B : E → ℝ) (x : V) (e : E) : ℝ :=
  ∑ q ∈ Finset.univ.erase e,
    ((if a q = x then if regular x then B q else 0 else 0) +
      (if b q = x then if regular x then B q else 0 else 0))

theorem incidentCharge_nonneg {V E : Type} [Fintype E] (a b : E → V)
    (regular : V → Prop) (B : E → ℝ) (hB : ∀ e, 0 ≤ B e) (x : V) :
    0 ≤ incidentCharge a b regular B x := by
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> linarith only [hB q]

theorem otherIncidentCharge_nonneg {V E : Type} [Fintype E] (a b : E → V)
    (regular : V → Prop) (B : E → ℝ) (hB : ∀ e, 0 ≤ B e) (x : V) (e : E) :
    0 ≤ otherIncidentCharge a b regular B x e := by
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> linarith only [hB q]

theorem le_otherIncidentCharge {V E : Type} [Fintype E] (a b : E → V)
    (regular : V → Prop) (B : E → ℝ) (hB : ∀ e, 0 ≤ B e)
    (x : V) (e q : E) (hqe : q ≠ e) (hx : regular x)
    (hqx : a q = x ∨ b q = x) :
    B q ≤ otherIncidentCharge a b regular B x e := by
  have hsingle := Finset.single_le_sum (s := Finset.univ.erase e)
    (fun i _ => show 0 ≤
      (if a i = x then if regular x then B i else 0 else 0) +
      (if b i = x then if regular x then B i else 0 else 0) from by
        split_ifs <;> linarith only [hB i])
    (Finset.mem_erase.mpr ⟨hqe, Finset.mem_univ q⟩)
  apply le_trans ?_ hsingle
  rcases hqx with hq | hq
  · simp only [hq, if_true, if_pos hx]
    split_ifs <;> linarith only [hB q]
  · simp only [hq, if_true, if_pos hx]
    split_ifs <;> linarith only [hB q]

/-- The whole incident budget equals the sum of its original endpoint contributions. -/
theorem sum_incidentCharge {V E : Type} [Fintype V] [Fintype E]
    (a b : E → V) (regular : V → Prop) (B : E → ℝ) :
    (∑ x, incidentCharge a b regular B x) =
      ∑ e, ((if regular (a e) then B e else 0) + (if regular (b e) then B e else 0)) := by
  unfold incidentCharge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Excluding the edge itself leaves three possible charges at each degree-four endpoint. -/
theorem sum_otherIncidentCharge_le_six {V E : Type} [Fintype V] [Fintype E]
    (a b : E → V) (regular : V → Prop) (B : E → ℝ)
    (hloopless : ∀ e, a e ≠ b e) (hB : ∀ e, 0 ≤ B e)
    (hdegree : ∀ x, regular x → degree a b x ≤ 4) :
    (∑ e, (otherIncidentCharge a b regular B (a e) e +
      otherIncidentCharge a b regular B (b e) e)) ≤ 6 * ∑ e, B e := by
  let T := ∑ e, ((if regular (a e) then B e else 0) +
    (if regular (b e) then B e else 0))
  have hremove (e : E) (x : V) (hx : x = a e ∨ x = b e) :
      otherIncidentCharge a b regular B x e + (if regular x then B e else 0) =
        incidentCharge a b regular B x := by
    have hs := Finset.sum_erase_add (s := Finset.univ)
      (fun q => (if a q = x then if regular x then B q else 0 else 0) +
        (if b q = x then if regular x then B q else 0 else 0)) (Finset.mem_univ e)
    rcases hx with rfl | rfl
    · simpa only [incidentCharge, otherIncidentCharge, if_true,
        if_neg (Ne.symm (hloopless e)), add_zero] using hs
    · simpa only [incidentCharge, otherIncidentCharge, if_true,
        if_neg (hloopless e), zero_add] using hs
  have htotal : (∑ e, (otherIncidentCharge a b regular B (a e) e +
      otherIncidentCharge a b regular B (b e) e)) + T =
      ∑ e, (incidentCharge a b regular B (a e) + incidentCharge a b regular B (b e)) := by
    dsimp only [T]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    calc
      _ = (otherIncidentCharge a b regular B (a e) e + (if regular (a e) then B e else 0)) +
        (otherIncidentCharge a b regular B (b e) e + (if regular (b e) then B e else 0)) := by ring
      _ = _ := by rw [hremove e (a e) (Or.inl rfl), hremove e (b e) (Or.inr rfl)]
  have hall : (∑ e, (incidentCharge a b regular B (a e) + incidentCharge a b regular B (b e))) ≤ 4 * T := by
    rw [← sum_degree_mul]
    calc
      _ ≤ ∑ x, 4 * incidentCharge a b regular B x := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : regular x
        · exact mul_le_mul_of_nonneg_right (hdegree x hx)
            (incidentCharge_nonneg a b regular B hB x)
        · simp only [incidentCharge, if_neg hx, ite_self, add_zero, Finset.sum_const_zero,
            mul_zero, le_refl]
      _ = _ := by rw [← Finset.mul_sum, sum_incidentCharge]
  have hT : T ≤ 2 * ∑ e, B e := by
    calc
      _ ≤ ∑ e, (B e + B e) := by
        apply Finset.sum_le_sum
        intro e _
        split_ifs <;> linarith only [hB e]
      _ = _ := by simp only [Finset.sum_add_distrib, two_mul]
  rw [← htotal] at hall
  linarith only [hall, hT]

end
end FiniteAvalanches.Electrical.Geometry
