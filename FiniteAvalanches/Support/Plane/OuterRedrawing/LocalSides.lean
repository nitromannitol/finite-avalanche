import FiniteAvalanches.Support.Plane.TwoArcJordan
import FiniteAvalanches.Support.Schoenflies.JordanClosed

/-!
# Local sides of a Jordan curve

The two complementary regions of a plane Jordan curve both accumulate at every
point of the curve. Consequently, near a point where the curve is a horizontal
segment, the open half-disks above and below the curve lie in different
complementary regions: no connected set avoiding the curve meets both of them.
An unbounded connected set avoiding a Jordan curve lies in its unbounded region.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric Bornology Schoenflies
open scoped Topology

noncomputable section

/-- A homeomorphism between proper metric spaces carries bounded sets to bounded sets. -/
theorem isBounded_image_of_homeomorph' {X Y : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [PseudoMetricSpace Y] (h : X ≃ₜ Y) {s : Set X} (hs : IsBounded s) : IsBounded (h '' s) :=
  (hs.isCompact_closure.image h.continuous).isBounded.subset (image_mono subset_closure)

/-- A preconnected set avoiding a Jordan curve lies in one of its two regions. -/
theorem preconnected_subset_inside_or_outside {C K : Set Schoenflies.Plane}
    (hC : IsSeparating C) (hK : IsPreconnected K) (hKC : Disjoint K C) :
    K ⊆ inside C ∨ K ⊆ outside C := by
  have hcover : K ⊆ inside C ∪ outside C := by
    rw [inside_union_outside]
    exact fun z hz hzC => hKC.ne_of_mem hz hzC rfl
  by_cases hin : (K ∩ inside C).Nonempty
  · exact Or.inl (hK.subset_left_of_subset_union hC.isOpen_inside hC.isOpen_outside
      disjoint_inside_outside hcover hin)
  · right
    intro z hz
    rcases hcover hz with h | h
    · exact (hin ⟨z, hz, h⟩).elim
    · exact h

/-- Near a point of a Jordan curve, two preconnected sets covering a neighborhood
off the curve cannot both meet one connected set avoiding the curve. -/
theorem not_preconnected_meets_two_sides {C A B K : Set Schoenflies.Plane}
    (hC : IsSeparating C) {z : Schoenflies.Plane} (hz : z ∈ C) {N : Set Schoenflies.Plane}
    (hN : N ∈ 𝓝 z) (hcover : N \ C ⊆ A ∪ B) (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAC : Disjoint A C) (hBC : Disjoint B C) (hK : IsPreconnected K) (hKC : Disjoint K C)
    (hKA : (K ∩ A).Nonempty) (hKB : (K ∩ B).Nonempty) : False := by
  obtain ⟨a, haK, haA⟩ := hKA
  obtain ⟨b, hbK, hbB⟩ := hKB
  have hside : ∀ {Ω Ω' : Set Schoenflies.Plane}, Disjoint Ω Ω' → frontier Ω' = C →
      Ω' ⊆ Cᶜ → K ⊆ Ω → A ⊆ Ω ∨ A ⊆ Ω' → B ⊆ Ω ∨ B ⊆ Ω' → False := by
    intro Ω Ω' hdisj hfront hΩ'C hKΩ hA' hB'
    have hAΩ : A ⊆ Ω := hA'.resolve_right fun h => hdisj.ne_of_mem (hKΩ haK) (h haA) rfl
    have hBΩ : B ⊆ Ω := hB'.resolve_right fun h => hdisj.ne_of_mem (hKΩ hbK) (h hbB) rfl
    have hzcl : z ∈ closure Ω' := by
      rw [← hfront] at hz
      exact frontier_subset_closure hz
    obtain ⟨w, hwN, hwΩ'⟩ := mem_closure_iff_nhds.mp hzcl N hN
    rcases hcover ⟨hwN, hΩ'C hwΩ'⟩ with h | h
    · exact hdisj.ne_of_mem (hAΩ h) hwΩ' rfl
    · exact hdisj.ne_of_mem (hBΩ h) hwΩ' rfl
  have hAin := preconnected_subset_inside_or_outside hC hA hAC
  have hBin := preconnected_subset_inside_or_outside hC hB hBC
  rcases preconnected_subset_inside_or_outside hC hK hKC with hKi | hKo
  · exact hside disjoint_inside_outside hC.frontier_outside outside_subset_compl hKi hAin hBin
  · exact hside disjoint_inside_outside.symm hC.frontier_inside inside_subset_compl hKo
      hAin.symm hBin.symm

/-- In product coordinates, near a point where a Jordan curve is the horizontal
line, no preconnected set avoiding the curve meets both open half-balls. -/
theorem not_preconnected_meets_upper_lower {C K : Set (ℝ × ℝ)}
    (hC : IsJordanCurve (euclideanPlaneHomeomorph '' C)) {q : ℝ × ℝ} {r : ℝ} (hr : 0 < r)
    (hloc : ∀ w ∈ ball q r, w ∈ C ↔ w.2 = q.2)
    (hK : IsPreconnected K) (hKC : Disjoint K C)
    (hup : (K ∩ (ball q r ∩ {w | q.2 < w.2})).Nonempty)
    (hdown : (K ∩ (ball q r ∩ {w | w.2 < q.2})).Nonempty) : False := by
  let H := euclideanPlaneHomeomorph
  have hS := jordan_curve_theorem hC
  have hqC : q ∈ C := (hloc q (mem_ball_self hr)).2 rfl
  have hupc : IsPreconnected (ball q r ∩ {w : ℝ × ℝ | q.2 < w.2}) :=
    ((convex_ball q r).inter (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear q.2)).isPreconnected
  have hdownc : IsPreconnected (ball q r ∩ {w : ℝ × ℝ | w.2 < q.2}) :=
    ((convex_ball q r).inter (convex_halfSpace_lt (LinearMap.snd ℝ ℝ ℝ).isLinear q.2)).isPreconnected
  have hdisj : ∀ {X : Set (ℝ × ℝ)}, Disjoint X C → Disjoint (H '' X) (H '' C) := by
    intro X hX
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact hX.ne_of_mem hx (H.injective hxy ▸ hy) rfl
  have hupC : Disjoint (ball q r ∩ {w : ℝ × ℝ | q.2 < w.2}) C := by
    rw [Set.disjoint_left]
    rintro w ⟨hw, hw2⟩ hwC
    exact (ne_of_gt hw2) ((hloc w hw).1 hwC)
  have hdownC : Disjoint (ball q r ∩ {w : ℝ × ℝ | w.2 < q.2}) C := by
    rw [Set.disjoint_left]
    rintro w ⟨hw, hw2⟩ hwC
    exact (ne_of_lt hw2) ((hloc w hw).1 hwC)
  refine not_preconnected_meets_two_sides hS (z := H q) ⟨q, hqC, rfl⟩
    (N := H '' ball q r) (A := H '' (ball q r ∩ {w | q.2 < w.2}))
    (B := H '' (ball q r ∩ {w | w.2 < q.2})) (K := H '' K) ?_ ?_
    (hupc.image _ H.continuous.continuousOn) (hdownc.image _ H.continuous.continuousOn)
    (hdisj hupC) (hdisj hdownC) (hK.image _ H.continuous.continuousOn) (hdisj hKC) ?_ ?_
  · exact (H.isOpenMap _ isOpen_ball).mem_nhds ⟨q, mem_ball_self hr, rfl⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hxC⟩
    have hxC' : x ∉ C := fun h => hxC ⟨x, h, rfl⟩
    have hne : x.2 ≠ q.2 := fun h => hxC' ((hloc x hx).2 h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨x, ⟨hx, h⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨hx, h⟩, rfl⟩
  · obtain ⟨w, hwK, hw⟩ := hup
    exact ⟨H w, ⟨w, hwK, rfl⟩, ⟨w, hw, rfl⟩⟩
  · obtain ⟨w, hwK, hw⟩ := hdown
    exact ⟨H w, ⟨w, hwK, rfl⟩, ⟨w, hw, rfl⟩⟩

/-- An unbounded preconnected set avoiding a Jordan curve lies in its unbounded region. -/
theorem image_subset_outside_of_unbounded {C K : Set (ℝ × ℝ)}
    (hC : IsJordanCurve (euclideanPlaneHomeomorph '' C)) (hK : IsPreconnected K)
    (hKC : Disjoint K C) (hKb : ¬ IsBounded K) :
    euclideanPlaneHomeomorph '' K ⊆ outside (euclideanPlaneHomeomorph '' C) := by
  let H := euclideanPlaneHomeomorph
  have hS := jordan_curve_theorem hC
  have hdisj : Disjoint (H '' K) (H '' C) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact hKC.ne_of_mem hx (H.injective hxy ▸ hy) rfl
  rcases preconnected_subset_inside_or_outside hS (hK.image _ H.continuous.continuousOn)
    hdisj with h | h
  · exfalso
    apply hKb
    have hb := isBounded_image_of_homeomorph' H.symm (hS.isBounded_inside.subset h)
    rwa [H.image_symm, H.preimage_image] at hb
  · exact h

/-- A point in the closure of an unbounded preconnected set avoiding a Jordan
curve, and not on the curve, lies in its unbounded region. -/
theorem mem_outside_of_mem_closure_unbounded {C K : Set (ℝ × ℝ)}
    (hC : IsJordanCurve (euclideanPlaneHomeomorph '' C)) (hK : IsPreconnected K)
    (hKC : Disjoint K C) (hKb : ¬ IsBounded K) {z : ℝ × ℝ} (hz : z ∈ closure K)
    (hzC : z ∉ C) : euclideanPlaneHomeomorph z ∈ outside (euclideanPlaneHomeomorph '' C) := by
  let H := euclideanPlaneHomeomorph
  have hS := jordan_curve_theorem hC
  have hsub := image_subset_outside_of_unbounded hC hK hKC hKb
  have hcl : H z ∈ closure (outside (H '' C)) :=
    closure_mono hsub (by rw [← H.image_closure]; exact ⟨z, hz, rfl⟩)
  rw [(IsRegionOf.outside _).closure_eq hS] at hcl
  rcases hcl with h | h
  · exact h
  · exact absurd (by obtain ⟨y, hy, hyz⟩ := h; exact H.injective hyz ▸ hy) hzC

/-- A Jordan curve straight near `q` cannot have one connected set touching both
sides at `q`, when that set is assembled from a connected set `U`, an arc-free
piece `Λ` in the closure of `U`, and a connected set `L` accumulating on `Λ`. -/
theorem jordan_core_contradiction {C U Λ L : Set (ℝ × ℝ)}
    (hC : IsJordanCurve (euclideanPlaneHomeomorph '' C)) (hU : IsPreconnected U)
    (hUC : Disjoint U C) (hΛne : Λ.Nonempty) (hΛU : Λ ⊆ closure U) (hΛC : Disjoint Λ C)
    (hL : IsPreconnected L) (hΛL : Λ ⊆ closure L) (hLC : Disjoint L C)
    {q : ℝ × ℝ} {r : ℝ} (hr : 0 < r) (hloc : ∀ w ∈ ball q r, w ∈ C ↔ w.2 = q.2)
    (hsides : ((U ∩ (ball q r ∩ {w | q.2 < w.2})).Nonempty ∧
        (L ∩ (ball q r ∩ {w | w.2 < q.2})).Nonempty) ∨
      ((U ∩ (ball q r ∩ {w | w.2 < q.2})).Nonempty ∧
        (L ∩ (ball q r ∩ {w | q.2 < w.2})).Nonempty)) : False := by
  have hUΛ : IsPreconnected (U ∪ Λ) :=
    hU.subset_closure subset_union_left (union_subset subset_closure hΛU)
  have hLΛ : IsPreconnected (L ∪ Λ) :=
    hL.subset_closure subset_union_left (union_subset subset_closure hΛL)
  obtain ⟨x, hx⟩ := hΛne
  have hK : IsPreconnected ((U ∪ Λ) ∪ (L ∪ Λ)) :=
    hUΛ.union x (Or.inr hx) (Or.inr hx) hLΛ
  have hKC : Disjoint ((U ∪ Λ) ∪ (L ∪ Λ)) C :=
    ((hUC.union_left hΛC).union_left (hLC.union_left hΛC))
  rcases hsides with ⟨⟨u, huU, hu⟩, ⟨l, hlL, hl⟩⟩ | ⟨⟨u, huU, hu⟩, ⟨l, hlL, hl⟩⟩
  · exact not_preconnected_meets_upper_lower hC hr hloc hK hKC
      ⟨u, Or.inl (Or.inl huU), hu⟩ ⟨l, Or.inr (Or.inl hlL), hl⟩
  · exact not_preconnected_meets_upper_lower hC hr hloc hK hKC
      ⟨l, Or.inr (Or.inl hlL), hl⟩ ⟨u, Or.inl (Or.inl huU), hu⟩

end
end FiniteAvalanches.Electrical.StatementGeometry
