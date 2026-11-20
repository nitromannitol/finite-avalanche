import FiniteAvalanches.Support.Plane.RoundCircleRegions
import FiniteAvalanches.Support.Plane.HomeomorphCoverGluing
import FiniteAvalanches.Support.Schoenflies.JordanSchoenflies
import FiniteAvalanches.Support.Plane.JordanLoopExtension

/-!
# Rounding a Jordan curve around a horizontal segment

Let a Jordan curve enclose the horizontal unit segment. The horizontal rays from
the ends of the segment first meet the curve at two points, and the segment
between these points is a polygonal crosscut. Cutting the curve and a round
circle with the same diameter along this crosscut, the parametrized
Jordan–Schönflies theorem on the two halves and on the whole curve gives three
plane homeomorphisms agreeing on the common boundaries. Glued along the closed
pieces, they form a plane homeomorphism fixing the crosscut and carrying the
curve onto the circle.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Bornology Metric Schoenflies unitInterval

noncomputable section

variable {C P A₁ A₂ : Set Plane} {p q : Plane}

/-- The closed pieces cut out by a crosscut cover the plane and meet only along
the crosscut or along the arcs of the curve. -/
theorem crosscut_closed_pieces (hcross : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    (∀ x, x ∈ closure (outside C) ∨ x ∈ closure (inside (A₁ ∪ P)) ∨
      x ∈ closure (inside (A₂ ∪ P))) ∧
    closure (inside (A₁ ∪ P)) ∩ closure (inside (A₂ ∪ P)) ⊆ P ∧
    closure (inside (A₁ ∪ P)) ∩ closure (outside C) ⊆ A₁ ∧
    closure (inside (A₂ ∪ P)) ∩ closure (outside C) ⊆ A₂ := by
  have hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S :=
    fun S hS => jordan_curve_theorem hS
  have hC : IsSeparating C := jordan_curve_theorem hcross.curve
  have hJ₁ := hcross.isSeparating_union hjordan hcut
  have hJ₂ := hcross.isSeparating_union hjordan hcut.symm
  obtain ⟨hdiff, hdisj, -⟩ := general_crosscut hjordan hcross hcut hcollars
  have hcl₁ : closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) :=
    (IsRegionOf.inside _).closure_eq hJ₁
  have hcl₂ : closure (inside (A₂ ∪ P)) = inside (A₂ ∪ P) ∪ (A₂ ∪ P) :=
    (IsRegionOf.inside _).closure_eq hJ₂
  have hcl₀ : closure (outside C) = outside C ∪ C := (IsRegionOf.outside _).closure_eq hC
  have hin₁ : inside (A₁ ∪ P) ⊆ inside C \ P := hdiff ▸ subset_union_left
  have hin₂ : inside (A₂ ∪ P) ⊆ inside C \ P := hdiff ▸ subset_union_right
  have hA₁ : A₁ ⊆ C := hcut.fst_subset
  have hA₂ : A₂ ⊆ C := hcut.snd_subset
  have hpP : p ∈ P := hcross.arc.left_mem
  have hqP : q ∈ P := hcross.arc.right_mem
  have hA₁₂ : A₁ ∩ A₂ ⊆ P := by
    rw [hcut.inter_eq]
    rintro _ (rfl | h)
    · exact hpP
    · exact (mem_singleton_iff.1 h) ▸ hqP
  have hPC₁ : P ∩ C ⊆ A₁ := hcross.inter_subset_arc hcut
  have hPC₂ : P ∩ C ⊆ A₂ := hcross.inter_subset_arc hcut.symm
  have hPout : Disjoint P (outside C) := hcross.disjoint_outside
  have hinC : ∀ {x}, x ∈ inside C → x ∉ C := fun hx => hx.1
  have hinout : ∀ {x}, x ∈ inside C → x ∉ outside C :=
    fun hx hx' => disjoint_inside_outside.ne_of_mem hx hx' rfl
  refine ⟨fun x => ?_, ?_, ?_, ?_⟩
  · by_cases hxC : x ∈ C
    · exact Or.inl (hcl₀ ▸ Or.inr hxC)
    have hx : x ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hxC
    rcases hx with hx | hx
    · by_cases hxP : x ∈ P
      · exact Or.inr (Or.inl (hcl₁ ▸ Or.inr (Or.inr hxP)))
      · have : x ∈ inside C \ P := ⟨hx, hxP⟩
        rw [hdiff] at this
        rcases this with h | h
        · exact Or.inr (Or.inl (subset_closure h))
        · exact Or.inr (Or.inr (subset_closure h))
    · exact Or.inl (subset_closure hx)
  · rw [hcl₁, hcl₂]
    rintro x ⟨h₁ | h₁ | h₁, h₂ | h₂ | h₂⟩
    · exact (hdisj.ne_of_mem h₁ h₂ rfl).elim
    · exact absurd (hA₂ h₂) (hinC (hin₁ h₁).1)
    · exact absurd h₂ (hin₁ h₁).2
    · exact absurd (hA₁ h₁) (hinC (hin₂ h₂).1)
    · exact hA₁₂ ⟨h₁, h₂⟩
    · exact h₂
    · exact absurd h₁ (hin₂ h₂).2
    all_goals exact h₁
  · rw [hcl₁, hcl₀]
    rintro x ⟨h₁ | h₁ | h₁, h₀ | h₀⟩
    · exact absurd h₀ (hinout (hin₁ h₁).1)
    · exact absurd h₀ (hinC (hin₁ h₁).1)
    · exact h₁
    · exact h₁
    · exact (hPout.ne_of_mem h₁ h₀ rfl).elim
    · exact hPC₁ ⟨h₁, h₀⟩
  · rw [hcl₂, hcl₀]
    rintro x ⟨h₂ | h₂ | h₂, h₀ | h₀⟩
    · exact absurd h₀ (hinout (hin₂ h₂).1)
    · exact absurd h₀ (hinC (hin₂ h₂).1)
    · exact h₂
    · exact h₂
    · exact (hPout.ne_of_mem h₂ h₀ rfl).elim
    · exact hPC₂ ⟨h₂, h₀⟩

private theorem one_sub_mem_I {t : ℝ} (ht : t ∈ I) : 1 - t ∈ I :=
  ⟨by linarith [ht.2], by linarith [ht.1]⟩

private theorem image_rev (g : ℝ → Plane) : (fun t => g (1 - t)) '' I = g '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, one_sub_mem_I ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, one_sub_mem_I ht, by simp only [sub_sub_cancel]⟩

/-- Two arcs with common ends, the second one traversed backwards, form a loop
whose image is their union. -/
theorem isLoop_concatenate_rev {f g : ℝ → Plane}
    (hfc : ContinuousOn f I) (hfi : InjOn f I) (hgc : ContinuousOn g I) (hgi : InjOn g I)
    (h0 : g 0 = f 0) (h1 : g 1 = f 1) (hmeet : f '' I ∩ g '' I ⊆ {f 0, f 1}) :
    IsLoop (concatenate f fun t => g (1 - t)) ∧
      (concatenate f fun t => g (1 - t)) '' I = f '' I ∪ g '' I := by
  have hgc' : ContinuousOn (fun t => g (1 - t)) I :=
    hgc.comp (continuousOn_const.sub continuousOn_id) fun t ht => one_sub_mem_I ht
  have hgi' : InjOn (fun t => g (1 - t)) I := fun s hs t ht h => by
    have := hgi (one_sub_mem_I hs) (one_sub_mem_I ht) h
    linarith
  have hmid : f 1 = (fun t => g (1 - t)) 0 := by simp [h1]
  have hclose : (fun t => g (1 - t)) 1 = f 0 := by simp [h0]
  refine ⟨IsLoop.concatenate hfc hfi hgc' hgi' hmid hclose fun z hz hz' => ?_, ?_⟩
  · rw [image_rev] at hz'
    exact hmeet ⟨hz, hz'⟩
  · rw [image_concatenate hmid, image_rev]

/-- A homeomorphism matching two such loops matches both of their arcs. -/
theorem concatenate_rev_parts {f g f' g' : ℝ → Plane} (F : Plane ≃ₜ Plane)
    (hF : ∀ t ∈ I, F (concatenate f (fun t => g (1 - t)) t) =
      concatenate f' (fun t => g' (1 - t)) t)
    (h1 : g 1 = f 1) (h1' : g' 1 = f' 1) :
    (∀ s ∈ I, F (f s) = f' s) ∧ (∀ s ∈ I, F (g s) = g' s) := by
  have hfirst : ∀ s ∈ I, F (f s) = f' s := by
    intro s hs
    have ht : s / 2 ∈ I := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hle : s / 2 ≤ 1 / 2 := by linarith [hs.2]
    have h := hF _ ht
    have e : 2 * (s / 2) = s := by ring
    rwa [concatenate_of_le hle, concatenate_of_le hle, e] at h
  refine ⟨hfirst, fun s hs => ?_⟩
  rcases eq_or_lt_of_le hs.2 with rfl | hlt
  · rw [h1, h1']
    exact hfirst 1 one_mem_I
  · have ht : 1 - s / 2 ∈ I := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hle : ¬(1 - s / 2 ≤ 1 / 2) := by linarith
    have h := hF _ ht
    rw [concatenate_of_not_le hle, concatenate_of_not_le hle] at h
    have e : 1 - (2 * (1 - s / 2) - 1) = s := by ring
    simpa only [e] using h

/-- The image of a parametrized arc under a homeomorphism matching parameters. -/
theorem image_image_of_param {F : Plane ≃ₜ Plane} {f f' : ℝ → Plane}
    (h : ∀ s ∈ I, F (f s) = f' s) : F '' (f '' I) = f' '' I := by
  rw [image_image]
  exact image_congr h

/-- The horizontal segment between two horizontal points. -/
theorem segment_horizontal (x y : ℝ) :
    segment ℝ (Plane.mk x 0) (Plane.mk y 0) = (fun t => Plane.mk t 0) '' segment ℝ x y := by
  rw [segment_eq_image', segment_eq_image', image_image]
  congr 1
  funext θ
  ext i
  fin_cases i <;> simp

theorem mk_horizontal_injective : Function.Injective fun t : ℝ => Plane.mk t 0 := by
  intro s t h
  have := congrArg (fun z : Plane => z 0) h
  simpa using this

theorem norm_mk_horizontal (t : ℝ) : ‖Plane.mk t 0‖ = |t| := by
  rw [norm_mk]
  simp [Real.sqrt_sq_eq_abs]

/-- A segment from the bounded to the unbounded region first meets the curve at a
point before which it stays in the bounded region. -/
theorem exists_first_hit {K : Set Plane} (hS : IsSeparating K) {u v : Plane}
    (hu : u ∈ inside K) (hv : v ∈ outside K) :
    ∃ k ∈ segment ℝ u v, k ∈ K ∧ segment ℝ u k \ {k} ⊆ inside K := by
  have hmeet : (segment ℝ u v ∩ K).Nonempty := by
    by_contra h
    have hsub : segment ℝ u v ⊆ Kᶜ := fun z hz hzK => h ⟨z, hz, hzK⟩
    have hcomp := (convex_segment u v).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ u v) hsub
    rw [hS.connectedComponentIn_eq_inside hu] at hcomp
    exact disjoint_inside_outside.ne_of_mem (hcomp (right_mem_segment ℝ u v)) hv rfl
  have hcov : segment ℝ u v ⊆ Kᶜ ∪ K := fun z _ => by
    by_cases hz : z ∈ K
    · exact Or.inr hz
    · exact Or.inl hz
  obtain ⟨k, ⟨hk, hkK⟩, -, hsub⟩ :=
    exists_first_meeting_segment hS.isClosed disjoint_compl_left hu.1 hcov hmeet
  rw [hS.connectedComponentIn_eq_inside hu] at hsub
  exact ⟨k, hk, hkK, hsub⟩

private theorem circleLeft_horizontal (m r : ℝ) :
    circleLeft (Plane.mk m 0) r = Plane.mk (m - r) 0 := by
  ext i
  fin_cases i
  · simp [circleLeft, sub_eq_add_neg]
  · simp [circleLeft]

private theorem circleRight_horizontal (m r : ℝ) :
    circleRight (Plane.mk m 0) r = Plane.mk (m + r) 0 := by
  ext i
  fin_cases i <;> simp [circleRight]

/-- A Jordan curve enclosing the horizontal unit segment is carried onto a round
circle by a plane homeomorphism fixing that segment pointwise. -/
theorem exists_rounding_homeomorph {K : Set Plane} (hK : IsJordanCurve K)
    (hσ : ∀ t ∈ I, Plane.mk t 0 ∈ inside K) :
    ∃ Θ : Plane ≃ₜ Plane, ∃ c : Plane, ∃ r : ℝ, 0 < r ∧
      (∀ t ∈ I, Θ (Plane.mk t 0) = Plane.mk t 0) ∧ Θ '' K = sphere c r := by
  have hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S :=
    fun S hS => jordan_curve_theorem hS
  have hS := jordan_curve_theorem hK
  obtain ⟨R, hR, hout⟩ := exists_radius_compl_closedBall_subset_outside hS 0
  have hfar : ∀ t : ℝ, R < |t| → Plane.mk t 0 ∈ outside K := fun t ht => hout (by
    rw [mem_compl_iff, mem_closedBall, dist_zero_right, norm_mk_horizontal]
    exact not_le.2 ht)
  have hL : R < |-(R + 1)| := by
    rw [abs_neg, abs_of_pos (by linarith)]
    linarith
  have hRt : R < |R + 2| := by
    rw [abs_of_pos (by linarith)]
    linarith
  obtain ⟨k₁, hk₁seg, hk₁K, hk₁in⟩ := exists_first_hit hS (hσ 0 zero_mem_I) (hfar _ hL)
  obtain ⟨k₂, hk₂seg, hk₂K, hk₂in⟩ := exists_first_hit hS (hσ 1 one_mem_I) (hfar _ hRt)
  rw [segment_horizontal, segment_eq_uIcc] at hk₁seg hk₂seg
  obtain ⟨a₁, ha₁, hk₁eq⟩ := hk₁seg
  obtain ⟨a₂, ha₂, hk₂eq⟩ := hk₂seg
  simp only at hk₁eq hk₂eq
  subst hk₁eq hk₂eq
  have hnotK : ∀ t ∈ I, Plane.mk t 0 ∉ K := fun t ht => (hσ t ht).1
  have ha₁0 : a₁ < 0 := by
    rcases mem_uIcc.1 ha₁ with h | h
    · linarith [h.1, h.2]
    · rcases eq_or_lt_of_le h.2 with h' | h'
      · rw [h'] at hk₁K
        exact absurd hk₁K (hnotK 0 zero_mem_I)
      · exact h'
  have ha₂1 : 1 < a₂ := by
    rcases mem_uIcc.1 ha₂ with h | h
    · rcases eq_or_lt_of_le h.1 with h' | h'
      · rw [← h'] at hk₂K
        exact absurd hk₂K (hnotK 1 one_mem_I)
      · exact h'
    · linarith [h.1, h.2]
  have hleftin : ∀ t, a₁ < t → t ≤ 0 → Plane.mk t 0 ∈ inside K := by
    intro t h1 h2
    refine hk₁in ⟨?_, fun h => (ne_of_gt h1) (mk_horizontal_injective h)⟩
    rw [segment_horizontal, segment_eq_uIcc]
    exact ⟨t, mem_uIcc.2 (Or.inr ⟨h1.le, h2⟩), rfl⟩
  have hrightin : ∀ t, 1 ≤ t → t < a₂ → Plane.mk t 0 ∈ inside K := by
    intro t h1 h2
    refine hk₂in ⟨?_, fun h => (ne_of_lt h2) (mk_horizontal_injective h)⟩
    rw [segment_horizontal, segment_eq_uIcc]
    exact ⟨t, mem_uIcc.2 (Or.inl ⟨h1, h2.le⟩), rfl⟩
  have hmid : ∀ t, a₁ < t → t < a₂ → Plane.mk t 0 ∈ inside K := by
    intro t h1 h2
    by_cases h0 : t ≤ 0
    · exact hleftin t h1 h0
    by_cases h1' : 1 ≤ t
    · exact hrightin t h1' h2
    exact hσ t ⟨by linarith, by linarith⟩
  set k₁ := Plane.mk a₁ 0 with hk₁
  set k₂ := Plane.mk a₂ 0 with hk₂
  set P := segment ℝ k₁ k₂ with hPdef
  have hne : k₁ ≠ k₂ := fun h => by
    have := mk_horizontal_injective h
    linarith
  have hPIcc : P = (fun t => Plane.mk t 0) '' Icc a₁ a₂ := by
    rw [hPdef, hk₁, hk₂, segment_horizontal, segment_eq_Icc (by linarith)]
  have hsdiff : P \ {k₁, k₂} ⊆ inside K := by
    rintro z ⟨hz, hzne⟩
    rw [hPIcc] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have ht1 : t ≠ a₁ := by
      rintro rfl
      exact hzne (Or.inl rfl)
    have ht2 : t ≠ a₂ := by
      rintro rfl
      exact hzne (Or.inr rfl)
    exact hmid t (lt_of_le_of_ne ht.1 (Ne.symm ht1)) (lt_of_le_of_ne ht.2 ht2)
  have hcross : IsCrosscut K P k₁ k₂ :=
    { curve := hK
      arc := isArcBetween_segment hne
      polygonal := isPolygonal_segment _ _
      left_mem := hk₁K
      right_mem := hk₂K
      sdiff_subset := hsdiff }
  have hcollars : HasArcCollars (inside K) P :=
    hasArcCollars_segment hne hS.isOpen_inside (fun h => h.1 hk₁K) (fun h => h.1 hk₂K) hsdiff
  obtain ⟨K₁, K₂, hcut⟩ := exists_isCutPair hK hk₁K hk₂K hne
  obtain ⟨c, hc⟩ : ∃ c : Plane, c = Plane.mk ((a₁ + a₂) / 2) 0 := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (a₂ - a₁) / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hrdef]
    linarith
  have hleft : circleLeft c r = k₁ := by
    rw [hc, hrdef, circleLeft_horizontal, hk₁]
    congr 1
    ring
  have hright : circleRight c r = k₂ := by
    rw [hc, hrdef, circleRight_horizontal, hk₂]
    congr 1
    ring
  have hcross' := isCrosscut_diameter (c := c) hr
  have hcut' := isCutPair_semicircles (c := c) hr
  have hcollars' := hasArcCollars_diameter (c := c) hr
  rw [hleft, hright] at hcross' hcut' hcollars'
  obtain ⟨hcov, h12, h10, h20⟩ := crosscut_closed_pieces hcross hcut hcollars
  obtain ⟨hcov', h12', h10', h20'⟩ := crosscut_closed_pieces hcross' hcut' hcollars'
  have hJ₁ := hcross.isSeparating_union hjordan hcut
  obtain ⟨κ₁, hκ₁c, hκ₁i, hκ₁im, hκ₁0, hκ₁1⟩ := hcut.fst
  obtain ⟨κ₂, hκ₂c, hκ₂i, hκ₂im, hκ₂0, hκ₂1⟩ := hcut.snd
  subst hκ₁im hκ₂im
  let π : ℝ → Plane := fun s => k₁ + s • (k₂ - k₁)
  have hπim : π '' I = P := (segment_eq_image' ℝ k₁ k₂).symm
  have hπc : ContinuousOn π I := (by fun_prop : Continuous π).continuousOn
  have hπi : InjOn π I := fun s _ t _ h =>
    smul_left_injective ℝ (sub_ne_zero.2 hne.symm) (add_left_cancel h)
  have hπ0 : π 0 = k₁ := by simp [π]
  have hπ1 : π 1 = k₂ := by simp [π]
  let γ₁ := upperSemicircle c r
  let γ₂ := lowerSemicircle c r
  have hγ₁0 : γ₁ 0 = k₁ := (upperSemicircle_zero c r).trans hleft
  have hγ₁1 : γ₁ 1 = k₂ := (upperSemicircle_one c r).trans hright
  have hγ₂0 : γ₂ 0 = k₁ := (lowerSemicircle_zero c r).trans hleft
  have hγ₂1 : γ₂ 1 = k₂ := (lowerSemicircle_one c r).trans hright
  have hγ₁c : ContinuousOn γ₁ I := (continuous_upperSemicircle c r).continuousOn
  have hγ₂c : ContinuousOn γ₂ I := (continuous_lowerSemicircle c r).continuousOn
  have hγ₁i : InjOn γ₁ I := injOn_upperSemicircle hr
  have hγ₂i : InjOn γ₂ I := injOn_lowerSemicircle hr
  have hPK : P ∩ K = {k₁, k₂} := hcross.inter_eq
  have hPS : P ∩ sphere c r = {k₁, k₂} := hcross'.inter_eq
  have hL₀ := isLoop_concatenate_rev hκ₁c hκ₁i hκ₂c hκ₂i (hκ₂0.trans hκ₁0.symm)
    (hκ₂1.trans hκ₁1.symm) (by rw [hκ₁0, hκ₁1, hcut.inter_eq])
  have hM₀ := isLoop_concatenate_rev hγ₁c hγ₁i hγ₂c hγ₂i (hγ₂0.trans hγ₁0.symm)
    (hγ₂1.trans hγ₁1.symm) (by rw [hγ₁0, hγ₁1, hcut'.inter_eq])
  have hL₁ := isLoop_concatenate_rev hπc hπi hκ₁c hκ₁i (hκ₁0.trans hπ0.symm)
    (hκ₁1.trans hπ1.symm) (by
      rw [hπim, hπ0, hπ1, ← hPK]
      exact inter_subset_inter_right _ hcut.fst_subset)
  have hM₁ := isLoop_concatenate_rev hπc hπi hγ₁c hγ₁i (hγ₁0.trans hπ0.symm)
    (hγ₁1.trans hπ1.symm) (by
      rw [hπim, hπ0, hπ1, ← hPS]
      exact inter_subset_inter_right _ hcut'.fst_subset)
  have hL₂ := isLoop_concatenate_rev hπc hπi hκ₂c hκ₂i (hκ₂0.trans hπ0.symm)
    (hκ₂1.trans hπ1.symm) (by
      rw [hπim, hπ0, hπ1, ← hPK]
      exact inter_subset_inter_right _ hcut.snd_subset)
  have hM₂ := isLoop_concatenate_rev hπc hπi hγ₂c hγ₂i (hγ₂0.trans hπ0.symm)
    (hγ₂1.trans hπ1.symm) (by
      rw [hπim, hπ0, hπ1, ← hPS]
      exact inter_subset_inter_right _ hcut'.snd_subset)
  obtain ⟨Θ₀, hΘ₀⟩ := IsLoop.exists_plane_homeomorph hL₀.1 hM₀.1
  obtain ⟨Θ₁, hΘ₁⟩ := IsLoop.exists_plane_homeomorph hL₁.1 hM₁.1
  obtain ⟨Θ₂, hΘ₂⟩ := IsLoop.exists_plane_homeomorph hL₂.1 hM₂.1
  obtain ⟨hΘ₀a, hΘ₀b⟩ := concatenate_rev_parts Θ₀ hΘ₀ (hκ₂1.trans hκ₁1.symm)
    (hγ₂1.trans hγ₁1.symm)
  obtain ⟨hΘ₁a, hΘ₁b⟩ := concatenate_rev_parts Θ₁ hΘ₁ (hκ₁1.trans hπ1.symm)
    (hγ₁1.trans hπ1.symm)
  obtain ⟨hΘ₂a, hΘ₂b⟩ := concatenate_rev_parts Θ₂ hΘ₂ (hκ₂1.trans hπ1.symm)
    (hγ₂1.trans hπ1.symm)
  have him₀ : Θ₀ '' K = sphere c r := by
    rw [← hcut.union_eq, image_union, image_image_of_param hΘ₀a, image_image_of_param hΘ₀b,
      ← hcut'.union_eq]
  have him₁ : Θ₁ '' (κ₁ '' I ∪ P) = γ₁ '' I ∪ P := by
    rw [image_union, image_image_of_param hΘ₁b, ← hπim, image_image_of_param hΘ₁a]
  have him₂ : Θ₂ '' (κ₂ '' I ∪ P) = γ₂ '' I ∪ P := by
    rw [image_union, image_image_of_param hΘ₂b, ← hπim, image_image_of_param hΘ₂a]
  have hinv {F : Plane ≃ₜ Plane} {f f' : ℝ → Plane} (h : ∀ s ∈ I, F (f s) = f' s) :
      ∀ s ∈ I, F.symm (f' s) = f s := fun s hs => F.symm_apply_eq.2 (h s hs).symm
  obtain ⟨Θ, hΘ0, hΘ1, -⟩ := exists_homeomorph_glue_three
    (closure (outside K)) (closure (inside (κ₁ '' I ∪ P))) (closure (inside (κ₂ '' I ∪ P)))
    (closure (outside (sphere c r))) (closure (inside (γ₁ '' I ∪ P)))
    (closure (inside (γ₂ '' I ∪ P)))
    isClosed_closure isClosed_closure isClosed_closure isClosed_closure isClosed_closure
    isClosed_closure hcov hcov' Θ₀ Θ₁ Θ₂
    (by rw [Θ₀.image_closure, image_outside, him₀])
    (by rw [Θ₁.image_closure, image_inside, him₁])
    (by rw [Θ₂.image_closure, image_inside, him₂])
    (fun x hx => by
      obtain ⟨s, hs, rfl⟩ := h10 ⟨hx.2, hx.1⟩
      rw [hΘ₀a s hs, hΘ₁b s hs])
    (fun x hx => by
      obtain ⟨s, hs, rfl⟩ := h20 ⟨hx.2, hx.1⟩
      rw [hΘ₀b s hs, hΘ₂b s hs])
    (fun x hx => by
      have hxP := h12 hx
      rw [← hπim] at hxP
      obtain ⟨s, hs, rfl⟩ := hxP
      rw [hΘ₁a s hs, hΘ₂a s hs])
    (fun y hy => by
      obtain ⟨s, hs, rfl⟩ := h10' ⟨hy.2, hy.1⟩
      rw [hinv hΘ₀a s hs, hinv hΘ₁b s hs])
    (fun y hy => by
      obtain ⟨s, hs, rfl⟩ := h20' ⟨hy.2, hy.1⟩
      rw [hinv hΘ₀b s hs, hinv hΘ₂b s hs])
    (fun y hy => by
      have hyP : y ∈ P := h12' hy
      rw [← hπim] at hyP
      obtain ⟨s, hs, rfl⟩ := hyP
      rw [hinv hΘ₁a s hs, hinv hΘ₂a s hs])
  refine ⟨Θ, c, r, hr, fun t ht => ?_, ?_⟩
  · have hP : Plane.mk t 0 ∈ P := by
      rw [hPIcc]
      exact ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    have hS1 : Plane.mk t 0 ∈ closure (inside (κ₁ '' I ∪ P)) :=
      (IsRegionOf.inside _).subset_closure hJ₁ (Or.inr hP)
    rw [hΘ1 _ hS1]
    rw [← hπim] at hP
    obtain ⟨s, hs, hst⟩ := hP
    rw [← hst]
    exact hΘ₁a s hs
  · rw [← him₀]
    exact image_congr fun x hx => hΘ0 x ((IsRegionOf.outside K).subset_closure hS hx)

end
end FiniteAvalanches.Electrical.StatementGeometry
