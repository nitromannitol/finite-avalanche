import FiniteAvalanches.Walk.BarlowMasson.Annulus

/-!
# Leaving a disk away from a set behind its centre

Let `u` be a unit vector and let `α` be a set of sites lying, apart from `z`, in the open
half-plane `{w : ⟨w - z, u⟩ < 0}`. For the simple random walk on `ℤ²` started at `z`, conditioned
to leave the disk of radius `R` around `z` before a positive-time visit to `α`, the first site
outside the disk lies in the cone `{4 ⟨w - z, u⟩ > |w - z|}` with probability at least `1 / 17`.

This replaces the conditioned exit estimate of Masson (2009), Proposition 3.5, in the setting of
Barlow and Masson (2011), Lemma 2.4, where `α` is the part of a loop-erased walk before its first
exit `z` from a disk centred at its start. The proof uses the function
`h = X + (X² - Y²) / 2` of the coordinates `X`, `Y` of `(w - z) / R` along `u` and across `u`. It
is a polynomial of degree two with vanishing Laplacian, hence exactly harmonic for the walk. It
is nonpositive on the half-plane near `z`, at most `3` on the exit layer and at most `-3 / 16`
on the exit layer outside the cone, and the maximum principle compares it with the escape
probabilities.

## Main statements

* `coneHarmonic_mean`: the function `h` is discrete harmonic.
* `escape_le_cone_escape`: the escape probability is at most `17` times the probability of
  escaping through the cone.
-/

noncomputable section

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory FiniteAvalanches.Walk.Beurling

/-- The coordinate of `w - z` along `(u₁, u₂)`. -/
def coordAlong (z : Site 2) (u₁ u₂ : ℝ) (w : Site 2) : ℝ :=
  u₁ * (((w 0 : ℤ) : ℝ) - ((z 0 : ℤ) : ℝ)) + u₂ * (((w 1 : ℤ) : ℝ) - ((z 1 : ℤ) : ℝ))

/-- The coordinate of `w - z` across `(u₁, u₂)`. -/
def coordAcross (z : Site 2) (u₁ u₂ : ℝ) (w : Site 2) : ℝ :=
  -u₂ * (((w 0 : ℤ) : ℝ) - ((z 0 : ℤ) : ℝ)) + u₁ * (((w 1 : ℤ) : ℝ) - ((z 1 : ℤ) : ℝ))

/-- The harmonic polynomial `X + (X² - Y²) / 2` of the rescaled coordinates. -/
def coneHarmonic (z : Site 2) (u₁ u₂ R : ℝ) (w : Site 2) : ℝ :=
  coordAlong z u₁ u₂ w / R +
    ((coordAlong z u₁ u₂ w / R) ^ 2 - (coordAcross z u₁ u₂ w / R) ^ 2) / 2

theorem coneHarmonic_self (z : Site 2) (u₁ u₂ R : ℝ) : coneHarmonic z u₁ u₂ R z = 0 := by
  simp [coneHarmonic, coordAlong, coordAcross]

/-- A sum over the four directions, evaluated at their coordinates. -/
theorem sum_dir_coords (g : ℤ → ℤ → ℝ) :
    ∑ a : Dir 2, g (dirVec a 0) (dirVec a 1) = g 1 0 + g (-1) 0 + g 0 1 + g 0 (-1) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool]
  simp [dirVec]
  ring

theorem coordAlong_add_dirVec (z : Site 2) (u₁ u₂ : ℝ) (w : Site 2) (a : Dir 2) :
    coordAlong z u₁ u₂ (w + dirVec a) = coordAlong z u₁ u₂ w +
      (u₁ * ((dirVec a 0 : ℤ) : ℝ) + u₂ * ((dirVec a 1 : ℤ) : ℝ)) := by
  simp only [coordAlong, Pi.add_apply, Int.cast_add]
  ring

theorem coordAcross_add_dirVec (z : Site 2) (u₁ u₂ : ℝ) (w : Site 2) (a : Dir 2) :
    coordAcross z u₁ u₂ (w + dirVec a) = coordAcross z u₁ u₂ w +
      (-u₂ * ((dirVec a 0 : ℤ) : ℝ) + u₁ * ((dirVec a 1 : ℤ) : ℝ)) := by
  simp only [coordAcross, Pi.add_apply, Int.cast_add]
  ring

private def coneTerm (X Y u₁ u₂ R : ℝ) (p q : ℤ) : ℝ :=
  (X + (u₁ * (p : ℝ) + u₂ * (q : ℝ))) / R +
    (((X + (u₁ * (p : ℝ) + u₂ * (q : ℝ))) / R) ^ 2 -
      ((Y + (-u₂ * (p : ℝ) + u₁ * (q : ℝ))) / R) ^ 2) / 2

/-- The polynomial `coneHarmonic` is discrete harmonic everywhere. -/
theorem coneHarmonic_mean (z : Site 2) (u₁ u₂ R : ℝ) (w : Site 2) :
    (∑ a : Dir 2, coneHarmonic z u₁ u₂ R (w + dirVec a)) / 4 = coneHarmonic z u₁ u₂ R w := by
  have h : ∀ a : Dir 2, coneHarmonic z u₁ u₂ R (w + dirVec a) =
      coneTerm (coordAlong z u₁ u₂ w) (coordAcross z u₁ u₂ w) u₁ u₂ R (dirVec a 0) (dirVec a 1) := by
    intro a
    simp only [coneHarmonic, coordAlong_add_dirVec, coordAcross_add_dirVec, coneTerm]
  rw [Finset.sum_congr rfl fun a _ => h a, sum_dir_coords]
  simp only [coneTerm, coneHarmonic]
  push_cast
  ring

theorem euclidNorm_sub_sq (w z : Site 2) :
    euclidNorm (w - z) ^ 2 = (((w 0 : ℤ) : ℝ) - ((z 0 : ℤ) : ℝ)) ^ 2 +
      (((w 1 : ℤ) : ℝ) - ((z 1 : ℤ) : ℝ)) ^ 2 := by
  rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two]
  simp only [Pi.sub_apply, Int.cast_sub]

theorem coord_sq_add (z : Site 2) {u₁ u₂ : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 = 1) (w : Site 2) :
    coordAlong z u₁ u₂ w ^ 2 + coordAcross z u₁ u₂ w ^ 2 = euclidNorm (w - z) ^ 2 := by
  rw [euclidNorm_sub_sq, coordAlong, coordAcross]
  linear_combination ((((w 0 : ℤ) : ℝ) - ((z 0 : ℤ) : ℝ)) ^ 2 +
    (((w 1 : ℤ) : ℝ) - ((z 1 : ℤ) : ℝ)) ^ 2) * hu

theorem abs_coordAlong_le (z : Site 2) {u₁ u₂ : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 = 1) (w : Site 2) :
    |coordAlong z u₁ u₂ w| ≤ euclidNorm (w - z) := by
  apply abs_le_of_sq_le_sq _ (euclidNorm_nonneg _)
  rw [← coord_sq_add z hu w]
  nlinarith [sq_nonneg (coordAcross z u₁ u₂ w)]

private theorem coneHarmonic_eq (z : Site 2) {u₁ u₂ R : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 = 1)
    (hR : 0 < R) (w : Site 2) :
    coneHarmonic z u₁ u₂ R w = coordAlong z u₁ u₂ w / R +
      (2 * coordAlong z u₁ u₂ w ^ 2 - euclidNorm (w - z) ^ 2) / (2 * R ^ 2) := by
  have h := coord_sq_add z hu w
  rw [coneHarmonic]
  field_simp
  rw [← h]
  ring

/-- Near `z`, the polynomial is nonpositive where the coordinate along `u` is nonpositive. -/
theorem coneHarmonic_nonpos (z : Site 2) {u₁ u₂ R : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 = 1) (hR : 3 ≤ R)
    {w : Site 2} (hw : euclidNorm (w - z) < R + 1) (hc : coordAlong z u₁ u₂ w ≤ 0) :
    coneHarmonic z u₁ u₂ R w ≤ 0 := by
  have hR0 : 0 < R := by linarith
  have habs := abs_coordAlong_le z hu w
  have hlow : -(R + 1) < coordAlong z u₁ u₂ w := by
    have := neg_abs_le (coordAlong z u₁ u₂ w)
    linarith
  rw [coneHarmonic]
  set X := coordAlong z u₁ u₂ w / R
  have hX : X ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hR0.le
  have hX2 : -2 ≤ X := by
    rw [le_div_iff₀ hR0]
    nlinarith
  nlinarith [sq_nonneg (coordAcross z u₁ u₂ w / R)]

/-- On the exit layer the polynomial is at most `3`. -/
theorem coneHarmonic_le_three (z : Site 2) {u₁ u₂ R : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 = 1)
    (hR : 3 ≤ R) {w : Site 2} (hw : euclidNorm (w - z) < R + 1) :
    coneHarmonic z u₁ u₂ R w ≤ 3 := by
  have hR0 : 0 < R := by linarith
  rw [coneHarmonic_eq z hu hR0]
  have habs := abs_coordAlong_le z hu w
  have hc := le_abs_self (coordAlong z u₁ u₂ w)
  have hn := euclidNorm_nonneg (w - z)
  have h1 : coordAlong z u₁ u₂ w / R ≤ (R + 1) / R := div_le_div_of_nonneg_right (by linarith) hR0.le
  have h2 : (2 * coordAlong z u₁ u₂ w ^ 2 - euclidNorm (w - z) ^ 2) / (2 * R ^ 2) ≤
      (R + 1) ^ 2 / (2 * R ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hsq : coordAlong z u₁ u₂ w ^ 2 ≤ euclidNorm (w - z) ^ 2 := by
      rw [← coord_sq_add z hu w]
      nlinarith [sq_nonneg (coordAcross z u₁ u₂ w)]
    nlinarith
  have h3 : (R + 1) / R ≤ 4 / 3 := by rw [div_le_iff₀ hR0]; linarith
  have h4 : (R + 1) ^ 2 / (2 * R ^ 2) ≤ 8 / 9 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- On the exit layer outside the cone the polynomial is at most `-3 / 16`. -/
theorem coneHarmonic_le_neg (z : Site 2) {u₁ u₂ R : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 = 1)
    (hR : 3 ≤ R) {w : Site 2} (hw1 : R ≤ euclidNorm (w - z)) (hw2 : euclidNorm (w - z) < R + 1)
    (hc : 4 * coordAlong z u₁ u₂ w ≤ euclidNorm (w - z)) :
    coneHarmonic z u₁ u₂ R w ≤ -3 / 16 := by
  have hR0 : 0 < R := by linarith
  rw [coneHarmonic_eq z hu hR0]
  set c := coordAlong z u₁ u₂ w
  set ρ := euclidNorm (w - z)
  have habs : |c| ≤ ρ := abs_coordAlong_le z hu w
  have hlow : -ρ ≤ c := (neg_abs_le c).trans' (by linarith)
  have hprod : 0 ≤ (c + ρ) * (ρ - 4 * c) := mul_nonneg (by linarith) (by linarith)
  have hρ43 : 3 * ρ ≤ 4 * R := by linarith
  have key : 2 * R * c + 2 * c ^ 2 - ρ ^ 2 + 3 / 8 * R ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ρ / 4 - c) (by linarith : (0 : ℝ) ≤ 2 * R - 3 * ρ / 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ ρ - R) (by linarith : (0 : ℝ) ≤ ρ + 3 * R / 7)]
  have h2 := mul_nonpos_of_nonneg_of_nonpos hR0.le key
  rw [div_add_div _ _ hR0.ne' (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [h2]

/-- **The escape through the cone.** If `α` lies, apart from `z`, in the open half-plane
`{⟨w - z, u⟩ < 0}`, the walk from `z` leaves the disk of radius `R ≥ 3` around `z` before a
positive-time visit to `α` with probability at most `17` times the probability that it does so
through the cone `{4 ⟨w - z, u⟩ > |w - z|}`. -/
theorem escape_le_cone_escape {z : Site 2} {u₁ u₂ R : ℝ} (hu : u₁ ^ 2 + u₂ ^ 2 = 1)
    (hR : 3 ≤ R) {α : Set (Site 2)} (hα : ∀ w ∈ α, w ≠ z → coordAlong z u₁ u₂ w < 0) :
    prob (reachesAfter {w | R ≤ euclidNorm (w - z)} α z) ≤
      17 * prob (reachesAfter
        {w | R ≤ euclidNorm (w - z) ∧ euclidNorm (w - z) < 4 * coordAlong z u₁ u₂ w}
        (α ∪ {w | R ≤ euclidNorm (w - z) ∧ 4 * coordAlong z u₁ u₂ w ≤ euclidNorm (w - z)}) z) := by
  classical
  have hR0 : 0 < R := by linarith
  set Out : Set (Site 2) := {w | R ≤ euclidNorm (w - z)} with hOut
  set Cone : Set (Site 2) :=
    {w | R ≤ euclidNorm (w - z) ∧ euclidNorm (w - z) < 4 * coordAlong z u₁ u₂ w} with hCone
  set Non : Set (Site 2) :=
    {w | R ≤ euclidNorm (w - z) ∧ 4 * coordAlong z u₁ u₂ w ≤ euclidNorm (w - z)} with hNon
  set h := coneHarmonic z u₁ u₂ R
  set U := fun w => prob (reaches Cone (α ∪ Non) w)
  set V := fun w => prob (reaches Out α w)
  set φ := fun w => h w - 3 * U w + 3 / 16 * (V w - U w)
  set Λ : Finset (Site 2) := ((ballFinset 2 R).image (fun x => z + x)).filter
    (fun w => euclidNorm (w - z) < R ∧ w ∉ α) with hΛ
  have hmemΛ : ∀ w, w ∈ Λ ↔ euclidNorm (w - z) < R ∧ w ∉ α := by
    intro w
    rw [hΛ, Finset.mem_filter, Finset.mem_image]
    constructor
    · exact fun h => h.2
    · intro hw
      refine ⟨⟨w - z, mem_ballFinset_iff.2 hw.1.le, by abel⟩, hw⟩
  have hα_le : ∀ w ∈ α, euclidNorm (w - z) < R + 1 → φ w ≤ 0 := by
    intro w hw hwR
    have hU : U w = 0 := by
      simp only [U]
      rw [reaches_eq_empty (Or.inl hw), prob, measure_empty, ENNReal.toReal_zero]
    have hV : V w = 0 := by
      simp only [V]
      rw [reaches_eq_empty hw, prob, measure_empty, ENNReal.toReal_zero]
    simp only [φ, hU, hV]
    by_cases hwz : w = z
    · rw [hwz]
      simp [h, coneHarmonic_self]
    · have := coneHarmonic_nonpos z hu hR hwR (hα w hw hwz).le
      simp only [h]
      linarith
  have hΛ_le : ∀ w ∈ Λ, φ w ≤ 0 := by
    refine le_of_mean Λ φ 0 (fun w hw => ?_) (fun w hw a ha => ?_)
    · obtain ⟨hwR, hwα⟩ := (hmemΛ w).1 hw
      have hwOut : w ∉ Out := by simp only [hOut, Set.mem_setOf_eq, not_le]; exact hwR
      have hwCone : w ∉ Cone := fun hc => hwOut hc.1
      have hwB : w ∉ α ∪ Non := by
        rintro (h' | h')
        · exact hwα h'
        · exact hwOut h'.1
      have hu := prob_reaches_step hwCone hwB
      have hv := prob_reaches_step hwOut hwα
      have hh := coneHarmonic_mean z u₁ u₂ R w
      simp only [φ, U, V, h] at hu hv hh ⊢
      rw [hu, hv, ← hh]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    · obtain ⟨hwR, _⟩ := (hmemΛ w).1 hw
      have hw1 : euclidNorm (w + dirVec a - z) < R + 1 := by
        have := euclidNorm_add_dirVec_le (w - z) a
        rw [sub_add_eq_add_sub] at this
        linarith
      by_cases hα' : w + dirVec a ∈ α
      · exact hα_le _ hα' hw1
      · have hR' : R ≤ euclidNorm (w + dirVec a - z) := by
          by_contra hlt
          exact ha ((hmemΛ _).2 ⟨not_le.1 hlt, hα'⟩)
        have hV : V (w + dirVec a) = 1 := by
          simp only [V]
          rw [reaches_eq_univ (show w + dirVec a ∈ Out from hR') hα', prob_univ]
        by_cases hcone : euclidNorm (w + dirVec a - z) < 4 * coordAlong z u₁ u₂ (w + dirVec a)
        · have hU : U (w + dirVec a) = 1 := by
            simp only [U]
            rw [reaches_eq_univ (show w + dirVec a ∈ Cone from ⟨hR', hcone⟩), prob_univ]
            rintro (h' | h')
            · exact hα' h'
            · exact absurd h'.2 (not_le.2 hcone)
          have := coneHarmonic_le_three z hu hR hw1
          simp only [φ, hU, hV, h]
          linarith
        · have hU : U (w + dirVec a) = 0 := by
            simp only [U]
            rw [reaches_eq_empty (Or.inr ⟨hR', not_lt.1 hcone⟩), prob, measure_empty,
              ENNReal.toReal_zero]
          have := coneHarmonic_le_neg z hu hR hR' hw1 (not_lt.1 hcone)
          simp only [φ, hU, hV, h]
          linarith
  have hdisk : ∀ w, euclidNorm (w - z) < R → φ w ≤ 0 := by
    intro w hw
    by_cases hwα : w ∈ α
    · exact hα_le w hwα (by linarith)
    · exact hΛ_le w ((hmemΛ w).2 ⟨hw, hwα⟩)
  have hz : ∑ a : Dir 2, φ (z + dirVec a) ≤ 0 :=
    Finset.sum_nonpos fun a _ => hdisk _ (by
      rw [add_sub_cancel_left, euclidNorm_dirVec]
      linarith)
  have hU := prob_reachesAfter Cone (α ∪ Non) z
  have hV := prob_reachesAfter Out α z
  have hh := coneHarmonic_mean z u₁ u₂ R z
  rw [coneHarmonic_self] at hh
  simp only [φ, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hz
  simp only [U, V, h] at hz
  have e1 : ∑ a : Dir 2, coneHarmonic z u₁ u₂ R (z + dirVec a) = 0 := by linarith
  have e2 : ∑ a : Dir 2, prob (reaches Cone (α ∪ Non) (z + dirVec a)) =
      4 * prob (reachesAfter Cone (α ∪ Non) z) := by rw [hU]; ring
  have e3 : ∑ a : Dir 2, prob (reaches Out α (z + dirVec a)) =
      4 * prob (reachesAfter Out α z) := by rw [hV]; ring
  rw [e1, e2, e3] at hz
  linarith

end FiniteAvalanches.Walk.BarlowMasson
