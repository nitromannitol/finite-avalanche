import FiniteAvalanches.Support.Schoenflies.GeneralCrosscut
import FiniteAvalanches.Support.Schoenflies.JordanClosed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Complementary regions of round circles and their homeomorphic images

A plane homeomorphism carries the bounded and unbounded complementary regions
of a set onto those of its image. A round circle is a Jordan curve whose
bounded region is the open disk; its horizontal diameter is a polygonal
crosscut cutting it into an upper and a lower semicircle.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Bornology Metric Schoenflies unitInterval

noncomputable section

/-- A plane homeomorphism carries bounded sets to bounded sets. -/
theorem isBounded_image_of_homeomorph (h : Plane ≃ₜ Plane) {s : Set Plane}
    (hs : IsBounded s) : IsBounded (h '' s) :=
  (hs.isCompact_closure.image h.continuous).isBounded.subset (image_mono subset_closure)

/-- A plane homeomorphism carries complementary components to complementary components. -/
theorem homeomorph_image_connectedComponentIn_compl (h : Plane ≃ₜ Plane) (C : Set Plane) {x : Plane}
    (hx : x ∉ C) : h '' connectedComponentIn Cᶜ x = connectedComponentIn (h '' C)ᶜ (h x) := by
  rw [h.image_connectedComponentIn (show x ∈ Cᶜ from hx), image_compl_eq h.bijective]

private theorem notMem_image_of_notMem (h : Plane ≃ₜ Plane) {C : Set Plane} {x : Plane}
    (hx : x ∉ C) : h x ∉ h '' C := by
  rintro ⟨y, hy, hyx⟩
  exact hx (h.injective hyx ▸ hy)

private theorem image_symm_image (h : Plane ≃ₜ Plane) (s : Set Plane) :
    h.symm '' (h '' s) = s := by
  rw [h.image_symm, h.preimage_image]

/-- The image of the bounded region lies in the bounded region of the image. -/
theorem homeomorph_image_inside_subset (h : Plane ≃ₜ Plane) (C : Set Plane) :
    h '' inside C ⊆ inside (h '' C) := by
  rintro _ ⟨x, ⟨hxC, hb⟩, rfl⟩
  refine ⟨notMem_image_of_notMem h hxC, ?_⟩
  rw [← homeomorph_image_connectedComponentIn_compl h C hxC]
  exact isBounded_image_of_homeomorph h hb

/-- A plane homeomorphism carries the bounded region onto the bounded region of the image. -/
theorem homeomorph_image_inside (h : Plane ≃ₜ Plane) (C : Set Plane) :
    h '' inside C = inside (h '' C) := by
  refine (homeomorph_image_inside_subset h C).antisymm fun y hy => ?_
  have hm := homeomorph_image_inside_subset h.symm (h '' C) ⟨y, hy, rfl⟩
  rw [image_symm_image] at hm
  exact ⟨_, hm, h.apply_symm_apply y⟩

/-- The image of the unbounded region lies in the unbounded region of the image. -/
theorem homeomorph_image_outside_subset (h : Plane ≃ₜ Plane) (C : Set Plane) :
    h '' outside C ⊆ outside (h '' C) := by
  rintro _ ⟨x, ⟨hxC, hb⟩, rfl⟩
  refine ⟨notMem_image_of_notMem h hxC, fun hb' => hb ?_⟩
  rw [← homeomorph_image_connectedComponentIn_compl h C hxC] at hb'
  have hm := isBounded_image_of_homeomorph h.symm hb'
  rwa [image_symm_image] at hm

/-- A plane homeomorphism carries the unbounded region onto the unbounded region of the image. -/
theorem homeomorph_image_outside (h : Plane ≃ₜ Plane) (C : Set Plane) :
    h '' outside C = outside (h '' C) := by
  refine (homeomorph_image_outside_subset h C).antisymm fun y hy => ?_
  have hm := homeomorph_image_outside_subset h.symm (h '' C) ⟨y, hy, rfl⟩
  rw [image_symm_image] at hm
  exact ⟨_, hm, h.apply_symm_apply y⟩

/-- A plane homeomorphism carries Jordan curves to Jordan curves. -/
theorem isJordanCurve_homeomorph_image (h : Plane ≃ₜ Plane) {C : Set Plane} (hC : IsJordanCurve C) :
    IsJordanCurve (h '' C) := by
  obtain ⟨f, hf, rfl⟩ := hC
  refine ⟨h ∘ f, ⟨h.continuous.comp_continuousOn hf.continuousOn, ?_,
    h.injective.comp_injOn hf.injOn⟩, image_comp _ _ _⟩
  simp only [Function.comp_apply, hf.closes]

/-- Euclidean norm in coordinates. -/
theorem norm_planeMk (a b : ℝ) : ‖Plane.mk a b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

/-- Every plane point is given by its two coordinates. -/
private theorem planeMk_coords (x : Plane) : x = Plane.mk (x 0) (x 1) := by
  ext i
  fin_cases i <;> rfl

/-- The upper semicircle of radius `r` about `c`, from its left to its right point. -/
def upperSemicircle (c : Plane) (r θ : ℝ) : Plane :=
  c + r • Plane.mk (-Real.cos (Real.pi * θ)) (Real.sin (Real.pi * θ))

/-- The lower semicircle of radius `r` about `c`, from its left to its right point. -/
def lowerSemicircle (c : Plane) (r θ : ℝ) : Plane :=
  c + r • Plane.mk (-Real.cos (Real.pi * θ)) (-Real.sin (Real.pi * θ))

/-- The left point of the circle of radius `r` about `c`. -/
def circleLeft (c : Plane) (r : ℝ) : Plane := c + r • Plane.mk (-1) 0

/-- The right point of the circle of radius `r` about `c`. -/
def circleRight (c : Plane) (r : ℝ) : Plane := c + r • Plane.mk 1 0

variable {c : Plane} {r : ℝ}

theorem continuous_upperSemicircle (c : Plane) (r : ℝ) : Continuous (upperSemicircle c r) := by
  unfold upperSemicircle
  fun_prop

theorem continuous_lowerSemicircle (c : Plane) (r : ℝ) : Continuous (lowerSemicircle c r) := by
  unfold lowerSemicircle
  fun_prop

theorem upperSemicircle_zero (c : Plane) (r : ℝ) : upperSemicircle c r 0 = circleLeft c r := by
  simp [upperSemicircle, circleLeft]

theorem upperSemicircle_one (c : Plane) (r : ℝ) : upperSemicircle c r 1 = circleRight c r := by
  simp [upperSemicircle, circleRight]

theorem lowerSemicircle_zero (c : Plane) (r : ℝ) : lowerSemicircle c r 0 = circleLeft c r := by
  simp [lowerSemicircle, circleLeft]

theorem lowerSemicircle_one (c : Plane) (r : ℝ) : lowerSemicircle c r 1 = circleRight c r := by
  simp [lowerSemicircle, circleRight]

private theorem norm_trig (a : ℝ) (s : ℝ) (hs : s = Real.sin a ∨ s = -Real.sin a) :
    ‖Plane.mk (-Real.cos a) s‖ = 1 := by
  rw [norm_planeMk]
  have : (-Real.cos a) ^ 2 + s ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> nlinarith [Real.sin_sq_add_cos_sq a]
  rw [this, Real.sqrt_one]

theorem upperSemicircle_mem_sphere (hr : 0 < r) (θ : ℝ) :
    upperSemicircle c r θ ∈ sphere c r := by
  rw [mem_sphere, dist_eq_norm, upperSemicircle, add_sub_cancel_left, norm_smul,
    norm_trig _ _ (Or.inl rfl), Real.norm_eq_abs, abs_of_pos hr, mul_one]

theorem lowerSemicircle_mem_sphere (hr : 0 < r) (θ : ℝ) :
    lowerSemicircle c r θ ∈ sphere c r := by
  rw [mem_sphere, dist_eq_norm, lowerSemicircle, add_sub_cancel_left, norm_smul,
    norm_trig _ _ (Or.inr rfl), Real.norm_eq_abs, abs_of_pos hr, mul_one]

private theorem cos_eq_of_first_coord (hr : 0 < r) {a b s t : ℝ}
    (h : c + r • Plane.mk (-Real.cos a) s = c + r • Plane.mk (-Real.cos b) t) :
    Real.cos a = Real.cos b := by
  have h0 := congrArg (fun z : Plane => z 0) h
  simp at h0
  rcases h0 with h0 | h0
  · linarith
  · exact absurd h0 hr.ne'

private theorem second_coord (hr : 0 < r) {a b s t : ℝ}
    (h : c + r • Plane.mk (-Real.cos a) s = c + r • Plane.mk (-Real.cos b) t) : s = t := by
  have h1 := congrArg (fun z : Plane => z 1) h
  simp at h1
  rcases h1 with h1 | h1
  · exact h1
  · exact absurd h1 hr.ne'

private theorem eq_of_cos_eq {θ θ' : ℝ} (hθ : θ ∈ I) (hθ' : θ' ∈ I)
    (h : Real.cos (Real.pi * θ) = Real.cos (Real.pi * θ')) : θ = θ' := by
  have hm (t : ℝ) (ht : t ∈ I) : Real.pi * t ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le ht.1, by nlinarith [Real.pi_pos, ht.2]⟩
  have := Real.injOn_cos (hm θ hθ) (hm θ' hθ') h
  exact mul_left_cancel₀ Real.pi_pos.ne' this

theorem injOn_upperSemicircle (hr : 0 < r) : InjOn (upperSemicircle c r) I :=
  fun _ hθ _ hθ' h => eq_of_cos_eq hθ hθ' (cos_eq_of_first_coord hr h)

theorem injOn_lowerSemicircle (hr : 0 < r) : InjOn (lowerSemicircle c r) I :=
  fun _ hθ _ hθ' h => eq_of_cos_eq hθ hθ' (cos_eq_of_first_coord hr h)

/-- The upper semicircle is an arc from the left to the right point. -/
theorem isArcBetween_upperSemicircle (hr : 0 < r) :
    IsArcBetween (upperSemicircle c r '' I) (circleLeft c r) (circleRight c r) :=
  ⟨_, (continuous_upperSemicircle c r).continuousOn, injOn_upperSemicircle hr, rfl,
    upperSemicircle_zero c r, upperSemicircle_one c r⟩

/-- The lower semicircle is an arc from the left to the right point. -/
theorem isArcBetween_lowerSemicircle (hr : 0 < r) :
    IsArcBetween (lowerSemicircle c r '' I) (circleLeft c r) (circleRight c r) :=
  ⟨_, (continuous_lowerSemicircle c r).continuousOn, injOn_lowerSemicircle hr, rfl,
    lowerSemicircle_zero c r, lowerSemicircle_one c r⟩

/-- The two semicircles meet only at the left and right points. -/
theorem upperSemicircle_inter_lowerSemicircle (hr : 0 < r) :
    upperSemicircle c r '' I ∩ lowerSemicircle c r '' I = {circleLeft c r, circleRight c r} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨θ, hθ, rfl⟩, ⟨θ', hθ', h⟩⟩
    have hcos := cos_eq_of_first_coord hr h
    have heq := eq_of_cos_eq hθ' hθ hcos
    subst heq
    have hsin := second_coord hr h
    have hs0 : Real.sin (Real.pi * θ') = 0 := by linarith
    rcases eq_or_lt_of_le hθ'.1 with h0 | h0
    · left
      rw [← h0, upperSemicircle_zero]
    rcases eq_or_lt_of_le hθ'.2 with h1 | h1
    · right
      rw [h1, upperSemicircle_one]
      rfl
    · exact absurd hs0 (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0)
        (by nlinarith [Real.pi_pos])).ne'
  · rintro _ (rfl | h)
    · exact ⟨⟨0, zero_mem_I, upperSemicircle_zero c r⟩, ⟨0, zero_mem_I, lowerSemicircle_zero c r⟩⟩
    · rw [mem_singleton_iff] at h
      subst h
      exact ⟨⟨1, one_mem_I, upperSemicircle_one c r⟩, ⟨1, one_mem_I, lowerSemicircle_one c r⟩⟩

/-- The two semicircles cover the circle. -/
theorem upperSemicircle_union_lowerSemicircle (hr : 0 < r) :
    upperSemicircle c r '' I ∪ lowerSemicircle c r '' I = sphere c r := by
  apply Subset.antisymm
  · rintro _ (⟨θ, -, rfl⟩ | ⟨θ, -, rfl⟩)
    · exact upperSemicircle_mem_sphere hr θ
    · exact lowerSemicircle_mem_sphere hr θ
  intro x hx
  rw [mem_sphere, dist_eq_norm, planeMk_coords (x - c), norm_planeMk] at hx
  set u := (x - c) 0
  set v := (x - c) 1
  have huv : u ^ 2 + v ^ 2 = r ^ 2 := by
    have h2 : (Real.sqrt (u ^ 2 + v ^ 2)) ^ 2 = r ^ 2 := by rw [hx]
    rwa [Real.sq_sqrt (by positivity)] at h2
  set a := -u / r
  have ha2 : a ^ 2 ≤ 1 := by
    rw [div_pow, neg_sq, div_le_one (by positivity)]
    nlinarith [sq_nonneg v]
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
  have ha1' : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  set θ := Real.arccos a / Real.pi
  have hθ : θ ∈ I := ⟨div_nonneg (Real.arccos_nonneg a) Real.pi_pos.le,
    (div_le_one Real.pi_pos).2 (Real.arccos_le_pi a)⟩
  have hπθ : Real.pi * θ = Real.arccos a := by
    simp only [θ]
    field_simp
  have hcos : Real.cos (Real.pi * θ) = a := by rw [hπθ, Real.cos_arccos ha1 ha1']
  have hsin : r * Real.sin (Real.pi * θ) = |v| := by
    rw [hπθ, Real.sin_arccos]
    have h1 : 1 - a ^ 2 = (v / r) ^ 2 := by
      simp only [a]
      field_simp
      linarith
    rw [h1, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hr]
    field_simp
  have hx0 : x = c + Plane.mk u v := by
    rw [← planeMk_coords (x - c)]
    abel
  have hru : r * -a = u := by
    simp only [a]
    field_simp
  rcases le_or_gt 0 v with hv | hv
  · left
    refine ⟨θ, hθ, ?_⟩
    rw [hx0, upperSemicircle, hcos]
    congr 1
    ext i
    fin_cases i
    · simp [hru]
    · simp [hsin, abs_of_nonneg hv]
  · right
    refine ⟨θ, hθ, ?_⟩
    rw [hx0, lowerSemicircle, hcos]
    congr 1
    ext i
    fin_cases i
    · simp [hru]
    · change r * -Real.sin (Real.pi * θ) = v
      rw [mul_neg, hsin, abs_of_neg hv, neg_neg]

/-- A round circle is a Jordan curve. -/
theorem isJordanCurve_sphere (hr : 0 < r) : IsJordanCurve (sphere c r) := by
  rw [← upperSemicircle_union_lowerSemicircle hr]
  refine IsJordanCurve.of_two_arcs (isArcBetween_upperSemicircle hr)
    (isArcBetween_lowerSemicircle hr).reverse fun z hz hz' => ?_
  have hz2 : z ∈ upperSemicircle c r '' I ∩ lowerSemicircle c r '' I := ⟨hz, hz'⟩
  rw [upperSemicircle_inter_lowerSemicircle hr] at hz2
  exact hz2

/-- The bounded region of a round circle is the open disk. -/
theorem inside_sphere (hr : 0 < r) : inside (sphere c r) = ball c r := by
  have hS := jordan_curve_theorem (isJordanCurve_sphere (c := c) hr)
  have hcS : c ∉ sphere c r := by
    rw [mem_sphere, dist_self]
    exact hr.ne
  have hsub : connectedComponentIn (sphere c r)ᶜ c ⊆ ball c r := by
    refine (isPreconnected_connectedComponentIn).subset_left_of_subset_union
      (v := (closedBall c r)ᶜ) isOpen_ball isClosed_closedBall.isOpen_compl ?_ ?_
      ⟨c, mem_connectedComponentIn hcS, mem_ball_self hr⟩
    · exact disjoint_compl_right.mono_left ball_subset_closedBall
    · intro z hz
      have hz' : dist z c ≠ r := connectedComponentIn_subset _ _ hz
      rcases lt_or_gt_of_ne hz' with h | h
      · exact Or.inl h
      · exact Or.inr fun h' => (not_le.2 h) h'
  have hball : ball c r ⊆ connectedComponentIn (sphere c r)ᶜ c :=
    (convex_ball c r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr)
      fun z hz hz' => (ne_of_lt hz) hz'
  have hc : c ∈ inside (sphere c r) := ⟨hcS, isBounded_ball.subset hsub⟩
  rw [← hS.connectedComponentIn_eq_inside hc]
  exact hsub.antisymm hball

theorem circleLeft_ne_circleRight (hr : 0 < r) : circleLeft c r ≠ circleRight c r := by
  intro h
  have h0 := congrArg (fun z : Plane => z 0) h
  simp [circleLeft, circleRight] at h0
  linarith

theorem circleLeft_mem_sphere (hr : 0 < r) : circleLeft c r ∈ sphere c r :=
  upperSemicircle_zero c r ▸ upperSemicircle_mem_sphere hr 0

theorem circleRight_mem_sphere (hr : 0 < r) : circleRight c r ∈ sphere c r :=
  upperSemicircle_one c r ▸ upperSemicircle_mem_sphere hr 1

/-- The open horizontal diameter lies in the open disk. -/
theorem diameter_sdiff_subset_ball (hr : 0 < r) :
    segment ℝ (circleLeft c r) (circleRight c r) \ {circleLeft c r, circleRight c r} ⊆
      ball c r := by
  rintro _ ⟨hz, hne⟩
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hne (by simp)
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have heq : circleLeft c r + t • (circleRight c r - circleLeft c r) - c =
      Plane.mk ((2 * t - 1) * r) 0 := by
    ext i
    fin_cases i
    · simp [circleLeft, circleRight]
      ring
    · simp [circleLeft, circleRight]
  rw [mem_ball, dist_eq_norm, heq, norm_planeMk]
  have hlt : |2 * t - 1| < 1 := by
    rw [abs_lt]
    constructor
    · linarith [lt_of_le_of_ne ht.1 (Ne.symm ht0)]
    · linarith [lt_of_le_of_ne ht.2 ht1]
  rw [show ((2 * t - 1) * r) ^ 2 + (0 : ℝ) ^ 2 = ((2 * t - 1) * r) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos hr]
  nlinarith [abs_nonneg (2 * t - 1)]

/-- The horizontal diameter is a polygonal crosscut of the circle. -/
theorem isCrosscut_diameter (hr : 0 < r) :
    IsCrosscut (sphere c r) (segment ℝ (circleLeft c r) (circleRight c r))
      (circleLeft c r) (circleRight c r) where
  curve := isJordanCurve_sphere hr
  arc := isArcBetween_segment (circleLeft_ne_circleRight hr)
  polygonal := isPolygonal_segment _ _
  left_mem := circleLeft_mem_sphere hr
  right_mem := circleRight_mem_sphere hr
  sdiff_subset := (inside_sphere hr).symm ▸ diameter_sdiff_subset_ball hr

/-- The semicircles form the cut pair of the horizontal diameter. -/
theorem isCutPair_semicircles (hr : 0 < r) :
    IsCutPair (sphere c r) (circleLeft c r) (circleRight c r)
      (upperSemicircle c r '' I) (lowerSemicircle c r '' I) where
  fst := isArcBetween_upperSemicircle hr
  snd := isArcBetween_lowerSemicircle hr
  union_eq := upperSemicircle_union_lowerSemicircle hr
  inter_eq := upperSemicircle_inter_lowerSemicircle hr

/-- The horizontal diameter has arc collars in the open disk. -/
theorem hasArcCollars_diameter (hr : 0 < r) :
    HasArcCollars (inside (sphere c r)) (segment ℝ (circleLeft c r) (circleRight c r)) := by
  rw [inside_sphere hr]
  refine hasArcCollars_segment (circleLeft_ne_circleRight hr) isOpen_ball ?_ ?_
    (diameter_sdiff_subset_ball hr)
  · exact fun h => (ne_of_lt (mem_ball.1 h)) (circleLeft_mem_sphere hr)
  · exact fun h => (ne_of_lt (mem_ball.1 h)) (circleRight_mem_sphere hr)

end
end FiniteAvalanches.Electrical.StatementGeometry
