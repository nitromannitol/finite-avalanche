import FiniteAvalanches.Support.Plane.OuterRedrawing.LocalSides
import FiniteAvalanches.Support.Plane.JordanRounding

/-!
# The boundary of the square as a Jordan curve

Two simple arcs with common ends and no other common point form a Jordan curve,
and a plane homeomorphism carries any such pair of arcs onto any other, matching
the parameters; it carries the unbounded region onto the unbounded region. The
boundary of the square `[-1, 1]²` is the union of its top edge and of the path
along its three other sides, and its unbounded region is the complement of the
closed square. The inversion `w ↦ ‖w‖⁻² w` in the sup norm fixes the boundary of
the square and carries its exterior into its punctured interior.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology Schoenflies unitInterval

noncomputable section

/-- Two simple arcs of the drawing plane with common ends and no other common point. -/
structure ArcPair (f g : ℝ → ℝ × ℝ) : Prop where
  continuousOn_left : ContinuousOn f I
  injOn_left : InjOn f I
  continuousOn_right : ContinuousOn g I
  injOn_right : InjOn g I
  start : g 0 = f 0
  finish : g 1 = f 1
  meet : f '' I ∩ g '' I ⊆ {f 0, f 1}

namespace ArcPair

variable {f g : ℝ → ℝ × ℝ}

theorem isLoop (h : ArcPair f g) :
    IsLoop (concatenate (euclideanPlaneHomeomorph ∘ f)
        fun t => (euclideanPlaneHomeomorph ∘ g) (1 - t)) ∧
      (concatenate (euclideanPlaneHomeomorph ∘ f)
          fun t => (euclideanPlaneHomeomorph ∘ g) (1 - t)) '' I =
        euclideanPlaneHomeomorph '' (f '' I ∪ g '' I) := by
  let H := euclideanPlaneHomeomorph
  have hmeet : (H ∘ f) '' I ∩ (H ∘ g) '' I ⊆ {(H ∘ f) 0, (H ∘ f) 1} := by
    rintro z ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
    have hmem : f s ∈ f '' I ∩ g '' I := ⟨⟨s, hs, rfl⟩, ⟨t, ht, H.injective hts⟩⟩
    rcases h.meet hmem with h0 | h1
    · left
      change H (f s) = H (f 0)
      rw [h0]
    · right
      change H (f s) = H (f 1)
      rw [mem_singleton_iff.mp h1]
  obtain ⟨hL, hI⟩ := isLoop_concatenate_rev (H.continuous.comp_continuousOn h.continuousOn_left)
    (H.injective.comp_injOn h.injOn_left) (H.continuous.comp_continuousOn h.continuousOn_right)
    (H.injective.comp_injOn h.injOn_right) (congrArg H h.start) (congrArg H h.finish) hmeet
  refine ⟨hL, ?_⟩
  rw [hI, image_union, image_comp, image_comp]

theorem isJordanCurve (h : ArcPair f g) :
    IsJordanCurve (euclideanPlaneHomeomorph '' (f '' I ∪ g '' I)) :=
  ⟨_, h.isLoop.1, h.isLoop.2⟩

/-- A plane homeomorphism carrying one pair of arcs onto another, matching the
parameters, and the unbounded region onto the unbounded region. -/
theorem exists_homeomorph {f₁ g₁ f₂ g₂ : ℝ → ℝ × ℝ} (h₁ : ArcPair f₁ g₁) (h₂ : ArcPair f₂ g₂) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (∀ s ∈ I, F (f₁ s) = f₂ s) ∧ (∀ s ∈ I, F (g₁ s) = g₂ s) ∧
      ∀ w, euclideanPlaneHomeomorph w ∈ outside (euclideanPlaneHomeomorph '' (f₁ '' I ∪ g₁ '' I)) →
        euclideanPlaneHomeomorph (F w) ∈
          outside (euclideanPlaneHomeomorph '' (f₂ '' I ∪ g₂ '' I)) := by
  let H := euclideanPlaneHomeomorph
  obtain ⟨hL₁, hI₁⟩ := h₁.isLoop
  obtain ⟨hL₂, hI₂⟩ := h₂.isLoop
  obtain ⟨F', hF'⟩ := hL₁.exists_plane_homeomorph hL₂
  obtain ⟨hf, hg⟩ := concatenate_rev_parts F' hF' (congrArg H h₁.finish) (congrArg H h₂.finish)
  have hconj : ∀ w, H.symm (F' (H w)) = (H.trans (F'.trans H.symm)) w := fun w => rfl
  refine ⟨H.trans (F'.trans H.symm), fun s hs => ?_, fun s hs => ?_, fun w hw => ?_⟩
  · rw [← hconj]
    change H.symm (F' ((H ∘ f₁) s)) = f₂ s
    rw [hf s hs]
    exact H.symm_apply_apply _
  · rw [← hconj]
    change H.symm (F' ((H ∘ g₁) s)) = g₂ s
    rw [hg s hs]
    exact H.symm_apply_apply _
  · rw [← hconj, H.apply_symm_apply, ← hI₂, ← image_image_of_param hF', hI₁,
      ← homeomorph_image_outside]
    exact mem_image_of_mem _ hw

end ArcPair

/-- The top edge of the square, from left to right. -/
def topEdge (s : ℝ) : ℝ × ℝ := (-1 + 2 * s, 1)

/-- The other three sides of the square, from the top left to the top right corner. -/
def lowerSides (s : ℝ) : ℝ × ℝ :=
  (-1 + 2 * min 1 (max 0 (3 * s - 1)), max (max (1 - 6 * s) (6 * s - 5)) (-1))

theorem lowerSides_left {s : ℝ} (hs : s ≤ 1 / 3) : lowerSides s = (-1, 1 - 6 * s) := by
  simp only [lowerSides, Prod.mk.injEq]
  constructor
  · rw [max_eq_left (by linarith), min_eq_right (by norm_num)]
    ring
  · rw [max_eq_left (le_max_of_le_left (by linarith)), max_eq_left (by linarith)]

theorem lowerSides_bottom {s : ℝ} (hs1 : 1 / 3 ≤ s) (hs2 : s ≤ 2 / 3) :
    lowerSides s = (-1 + 6 * (s - 1 / 3), -1) := by
  simp only [lowerSides, Prod.mk.injEq]
  constructor
  · rw [max_eq_right (by linarith), min_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by apply max_le <;> linarith)]

theorem lowerSides_right {s : ℝ} (hs : 2 / 3 ≤ s) : lowerSides s = (1, 6 * s - 5) := by
  simp only [lowerSides, Prod.mk.injEq]
  constructor
  · rw [max_eq_right (by linarith), min_eq_left (by linarith)]
    ring
  · rw [max_eq_left (le_max_of_le_right (by linarith)), max_eq_right (by linarith)]

theorem continuous_topEdge : Continuous topEdge := by
  unfold topEdge
  fun_prop

theorem continuous_lowerSides : Continuous lowerSides := by
  unfold lowerSides
  fun_prop

theorem injective_topEdge : Function.Injective topEdge := by
  intro s t h
  simp only [topEdge, Prod.mk.injEq] at h
  linarith [h.1]

theorem injOn_lowerSides : InjOn lowerSides I := by
  intro s hs t ht h
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  rcases le_total s (1 / 3) with hs3 | hs3 <;> rcases le_total t (1 / 3) with ht3 | ht3
  · rw [lowerSides_left hs3, lowerSides_left ht3, Prod.mk.injEq] at h
    linarith [h.2]
  · rcases le_total t (2 / 3) with ht6 | ht6
    · rw [lowerSides_left hs3, lowerSides_bottom ht3 ht6, Prod.mk.injEq] at h
      linarith [h.1, h.2]
    · rw [lowerSides_left hs3, lowerSides_right ht6, Prod.mk.injEq] at h
      linarith [h.1]
  · rcases le_total s (2 / 3) with hs6 | hs6
    · rw [lowerSides_bottom hs3 hs6, lowerSides_left ht3, Prod.mk.injEq] at h
      linarith [h.1, h.2]
    · rw [lowerSides_right hs6, lowerSides_left ht3, Prod.mk.injEq] at h
      linarith [h.1]
  · rcases le_total s (2 / 3) with hs6 | hs6 <;> rcases le_total t (2 / 3) with ht6 | ht6
    · rw [lowerSides_bottom hs3 hs6, lowerSides_bottom ht3 ht6, Prod.mk.injEq] at h
      linarith [h.1]
    · rw [lowerSides_bottom hs3 hs6, lowerSides_right ht6, Prod.mk.injEq] at h
      linarith [h.1, h.2]
    · rw [lowerSides_right hs6, lowerSides_bottom ht3 ht6, Prod.mk.injEq] at h
      linarith [h.1, h.2]
    · rw [lowerSides_right hs6, lowerSides_right ht6, Prod.mk.injEq] at h
      linarith [h.2]

theorem lowerSides_zero : lowerSides 0 = topEdge 0 := by
  rw [lowerSides_left (by norm_num)]
  simp [topEdge]

theorem lowerSides_one : lowerSides 1 = topEdge 1 := by
  rw [lowerSides_right (by norm_num)]
  simp only [topEdge, Prod.mk.injEq]
  constructor <;> norm_num

theorem arcPair_square : ArcPair topEdge lowerSides where
  continuousOn_left := continuous_topEdge.continuousOn
  injOn_left := injective_topEdge.injOn
  continuousOn_right := continuous_lowerSides.continuousOn
  injOn_right := injOn_lowerSides
  start := lowerSides_zero
  finish := lowerSides_one
  meet := by
    rintro z ⟨⟨s, -, rfl⟩, ⟨t, ⟨ht0, ht1⟩, hts⟩⟩
    rcases le_total t (1 / 3) with ht3 | ht3
    · rw [lowerSides_left ht3] at hts
      simp only [topEdge, Prod.mk.injEq] at hts
      have ht : t = 0 := by linarith [hts.2]
      have hs : s = 0 := by linarith [hts.1]
      left
      rw [hs]
    rcases le_total t (2 / 3) with ht6 | ht6
    · rw [lowerSides_bottom ht3 ht6] at hts
      simp only [topEdge, Prod.mk.injEq] at hts
      linarith [hts.2]
    · rw [lowerSides_right ht6] at hts
      simp only [topEdge, Prod.mk.injEq] at hts
      have hs : s = 1 := by linarith [hts.1]
      right
      rw [hs, mem_singleton_iff]

/-- The boundary of the square `[-1, 1]²`. -/
def squareBoundary : Set (ℝ × ℝ) := topEdge '' I ∪ lowerSides '' I

theorem norm_eq_one_of_mem_squareBoundary {z : ℝ × ℝ} (hz : z ∈ squareBoundary) : ‖z‖ = 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases hz with ⟨s, ⟨hs0, hs1⟩, rfl⟩ | ⟨t, ⟨ht0, ht1⟩, rfl⟩
  · simp only [topEdge, abs_one]
    exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
  · rcases le_total t (1 / 3) with ht3 | ht3
    · rw [lowerSides_left ht3]
      simp only [abs_neg, abs_one]
      exact max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)
    rcases le_total t (2 / 3) with ht6 | ht6
    · rw [lowerSides_bottom ht3 ht6]
      simp only [abs_neg, abs_one]
      exact max_eq_right (abs_le.mpr ⟨by linarith, by linarith⟩)
    · rw [lowerSides_right ht6]
      simp only [abs_one]
      exact max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem mem_squareBoundary_of_norm_eq_one {z : ℝ × ℝ} (hz : ‖z‖ = 1) : z ∈ squareBoundary := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hz
  have h1 : |z.1| ≤ 1 := hz ▸ le_max_left _ _
  have h2 : |z.2| ≤ 1 := hz ▸ le_max_right _ _
  rw [abs_le] at h1 h2
  rcases max_choice |z.1| |z.2| with hm | hm <;> rw [hm] at hz
  · rcases abs_eq (zero_le_one' ℝ) |>.mp hz with hx | hx
    · right
      refine ⟨2 / 3 + (z.2 + 1) / 6, ⟨by linarith, by linarith⟩, ?_⟩
      rw [lowerSides_right (by linarith)]
      ext
      · exact hx.symm
      · change 6 * (2 / 3 + (z.2 + 1) / 6) - 5 = z.2
        ring
    · right
      refine ⟨(1 - z.2) / 6, ⟨by linarith, by linarith⟩, ?_⟩
      rw [lowerSides_left (by linarith)]
      ext
      · exact hx.symm
      · change 1 - 6 * ((1 - z.2) / 6) = z.2
        ring
  · rcases abs_eq (zero_le_one' ℝ) |>.mp hz with hy | hy
    · left
      refine ⟨(z.1 + 1) / 2, ⟨by linarith, by linarith⟩, ?_⟩
      ext
      · change -1 + 2 * ((z.1 + 1) / 2) = z.1
        ring
      · exact hy.symm
    · right
      refine ⟨1 / 3 + (z.1 + 1) / 6, ⟨by linarith, by linarith⟩, ?_⟩
      rw [lowerSides_bottom (by linarith) (by linarith)]
      ext
      · change -1 + 6 * (1 / 3 + (z.1 + 1) / 6 - 1 / 3) = z.1
        ring
      · exact hy.symm

theorem isJordanCurve_squareBoundary :
    IsJordanCurve (euclideanPlaneHomeomorph '' squareBoundary) :=
  arcPair_square.isJordanCurve

/-- The unbounded region of the boundary of the square lies outside the closed square. -/
theorem one_lt_norm_of_mem_outside {w : ℝ × ℝ}
    (hw : euclideanPlaneHomeomorph w ∈ outside (euclideanPlaneHomeomorph '' squareBoundary)) :
    1 < ‖w‖ := by
  let H := euclideanPlaneHomeomorph
  have hC := isJordanCurve_squareBoundary
  have hS := jordan_curve_theorem hC
  have hnotC : ∀ z, z ∈ inside (H '' squareBoundary) ∪ outside (H '' squareBoundary) →
      ‖H.symm z‖ ≠ 1 := by
    intro z hz hn
    rw [inside_union_outside] at hz
    apply hz
    rw [← H.apply_symm_apply z]
    exact mem_image_of_mem _ (mem_squareBoundary_of_norm_eq_one hn)
  have hfar : ∀ v : ℝ × ℝ, 1 < ‖v‖ → H v ∈ outside (H '' squareBoundary) := by
    intro v hv
    let K := (fun t : ℝ => t • v) '' Ici 1
    have hK : IsPreconnected K := isPreconnected_Ici.image _ (by fun_prop)
    have hnorm : ∀ z ∈ K, 1 < ‖z‖ := by
      rintro _ ⟨t, ht, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [mem_Ici.mp ht] : (0 : ℝ) < t)]
      nlinarith [mem_Ici.mp ht]
    have hKC : Disjoint K squareBoundary := by
      rw [Set.disjoint_left]
      intro z hz hzC
      have := hnorm z hz
      rw [norm_eq_one_of_mem_squareBoundary hzC] at this
      exact lt_irrefl _ this
    have hKb : ¬ IsBounded K := by
      intro hb
      obtain ⟨R, hR⟩ := hb.subset_closedBall 0
      have hv0 : 0 < ‖v‖ := by linarith
      have hdiv : 0 ≤ max R 1 / ‖v‖ :=
        div_nonneg (zero_le_one.trans (le_max_right R 1)) hv0.le
      have hmem : (max R 1 / ‖v‖ + 1) • v ∈ K :=
        ⟨max R 1 / ‖v‖ + 1, mem_Ici.mpr (by linarith), rfl⟩
      have := hR hmem
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)] at this
      have he : (max R 1 / ‖v‖ + 1) * ‖v‖ = max R 1 + ‖v‖ := by field_simp
      rw [he] at this
      linarith [le_max_left R 1]
    exact image_subset_outside_of_unbounded hC hK hKC hKb
      ⟨v, ⟨1, mem_Ici.mpr le_rfl, one_smul _ _⟩, rfl⟩
  have hball : H '' ball (0 : ℝ × ℝ) 1 ⊆ inside (H '' squareBoundary) := by
    have hdisj : Disjoint (H '' ball (0 : ℝ × ℝ) 1) (H '' squareBoundary) := by
      rw [Set.disjoint_left]
      rintro _ ⟨v, hv, rfl⟩ ⟨u, hu, huv⟩
      rw [H.injective huv] at hu
      rw [mem_ball, dist_zero_right] at hv
      rw [norm_eq_one_of_mem_squareBoundary hu] at hv
      exact lt_irrefl _ hv
    rcases preconnected_subset_inside_or_outside hS
      ((convex_ball (0 : ℝ × ℝ) 1).isPreconnected.image _ H.continuous.continuousOn) hdisj with
      h | h
    · exact h
    · exfalso
      obtain ⟨z, hz⟩ := hS.isConnected_inside.nonempty
      rcases lt_trichotomy ‖H.symm z‖ 1 with hlt | heq | hgt
      · have hzo : z ∈ outside (H '' squareBoundary) := by
          have := h ⟨H.symm z, by rwa [mem_ball, dist_zero_right], H.apply_symm_apply z⟩
          exact this
        exact disjoint_inside_outside.ne_of_mem hz hzo rfl
      · exact hnotC z (Or.inl hz) heq
      · have hzo := hfar _ hgt
        rw [H.apply_symm_apply] at hzo
        exact disjoint_inside_outside.ne_of_mem hz hzo rfl
  rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
  · exfalso
    have := hball ⟨w, by rwa [mem_ball, dist_zero_right], rfl⟩
    exact disjoint_inside_outside.ne_of_mem this hw rfl
  · exfalso
    exact hnotC _ (Or.inr hw) (by rwa [H.symm_apply_apply])
  · exact hgt

/-- The inversion in the boundary of the square. -/
def squareInversion (w : ℝ × ℝ) : ℝ × ℝ := (‖w‖ ^ 2)⁻¹ • w

theorem norm_squareInversion (w : ℝ × ℝ) : ‖squareInversion w‖ = ‖w‖⁻¹ := by
  rw [squareInversion, norm_smul, norm_inv, norm_pow, Real.norm_eq_abs, abs_norm]
  rcases eq_or_ne ‖w‖ 0 with h0 | h0
  · rw [h0]
    simp
  · field_simp

theorem squareInversion_squareInversion (w : ℝ × ℝ) : squareInversion (squareInversion w) = w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [squareInversion]
  · have h0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    rw [squareInversion, norm_squareInversion, squareInversion, smul_smul, inv_pow, inv_inv]
    rw [mul_inv_cancel₀ (pow_ne_zero 2 h0), one_smul]

theorem squareInversion_injective : Function.Injective squareInversion :=
  Function.LeftInverse.injective squareInversion_squareInversion

theorem continuousAt_squareInversion {w : ℝ × ℝ} (hw : w ≠ 0) :
    ContinuousAt squareInversion w := by
  have h0 : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  unfold squareInversion
  exact ((continuous_norm.pow 2).continuousAt.inv₀ h0).smul continuousAt_id

theorem squareInversion_of_norm_eq_one {w : ℝ × ℝ} (hw : ‖w‖ = 1) : squareInversion w = w := by
  rw [squareInversion, hw]
  simp

theorem squareInversion_ne_zero {w : ℝ × ℝ} (hw : w ≠ 0) : squareInversion w ≠ 0 := by
  intro h
  apply hw
  rw [← squareInversion_squareInversion w, h]
  simp [squareInversion]

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
