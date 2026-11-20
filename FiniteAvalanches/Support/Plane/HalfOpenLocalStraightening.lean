import FiniteAvalanches.Support.Plane.ArcLocalStraightening
import FiniteAvalanches.Electrical.Geometry.DiskDrawing

/-!
# Local straightening for plane graph edges

A curve injective before its final parameter has an injective initial subpath
through every interior point. Local straightening of that subpath also covers
edges whose endpoints coincide.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical

/-- A path injective before its endpoint has parameter-preserving local
straightening at every interior point. -/
theorem exists_plane_homeomorph_straightening_of_injOn_halfOpen
    {x y : ℝ × ℝ} (p : Path x y)
    (hp : InjOn p {t : unitInterval | t.val < 1})
    (t : unitInterval) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    ∃ (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (δ : ℝ), 0 < δ ∧
      ∀ s : unitInterval, |s.val - t.val| < δ → F (p s) = (s.val, 0) := by
  let c : unitInterval := ⟨(t.val + 1) / 2,
    ⟨by linarith [t.property.1], by linarith [t.property.2]⟩⟩
  have htc : t.val < c.val := by dsimp [c]; linarith
  have hc1 : c.val < 1 := by dsimp [c]; linarith
  have hc0 : 0 < c.val := lt_trans ht0 htc
  let short := p.subpath 0 c
  have hshort : Function.Injective short := by
    intro u v huv
    have hu : (Set.Icc.convexComb (0 : unitInterval) c u).val < 1 := by
      have hcu := u.property.2
      have hcpos := hc0
      simp only [Set.Icc.coe_convexComb]
      change (1 - (u : ℝ)) * 0 + (u : ℝ) * c.val < 1
      nlinarith [mul_nonneg (sub_nonneg.mpr hcu) hcpos.le]
    have hv : (Set.Icc.convexComb (0 : unitInterval) c v).val < 1 := by
      have hcv := v.property.2
      have hcpos := hc0
      simp only [Set.Icc.coe_convexComb]
      change (1 - (v : ℝ)) * 0 + (v : ℝ) * c.val < 1
      nlinarith [mul_nonneg (sub_nonneg.mpr hcv) hcpos.le]
    have heq := hp hu hv huv
    have hval := congrArg Subtype.val heq
    simp only [Set.Icc.coe_convexComb] at hval
    change (1 - (u : ℝ)) * 0 + (u : ℝ) * c.val =
      (1 - (v : ℝ)) * 0 + (v : ℝ) * c.val at hval
    apply Subtype.ext
    exact mul_right_cancel₀ (ne_of_gt hc0) (by linarith)
  let u : unitInterval := ⟨t.val / c.val,
    ⟨div_nonneg ht0.le hc0.le, (div_le_one hc0).mpr htc.le⟩⟩
  have hu0 : 0 < u.val := div_pos ht0 hc0
  have hu1 : u.val < 1 := (div_lt_one hc0).mpr htc
  obtain ⟨F, ε, hε, hF⟩ := exists_plane_homeomorph_straightening_subpath short hshort u hu0 hu1
  let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toFun := fun z => (c.val * z.1, z.2)
    invFun := fun z => (z.1 / c.val, z.2)
    left_inv := by
      intro z
      apply Prod.ext
      · dsimp
        field_simp
      · rfl
    right_inv := by
      intro z
      apply Prod.ext
      · dsimp
        field_simp
      · rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let δ := min (c.val - t.val) (c.val * ε)
  have hδ : 0 < δ := lt_min (sub_pos.mpr htc) (mul_pos hc0 hε)
  refine ⟨F.trans H, δ, hδ, ?_⟩
  intro s hs
  have hsc : s.val < c.val := by
    have h := abs_lt.mp hs
    have hδc := min_le_left (c.val - t.val) (c.val * ε)
    dsimp only [δ] at h
    linarith
  let v : unitInterval := ⟨s.val / c.val,
    ⟨div_nonneg s.property.1 hc0.le, (div_le_one hc0).mpr hsc.le⟩⟩
  have hvu : |v.val - u.val| < ε := by
    change |s.val / c.val - t.val / c.val| < ε
    rw [← sub_div, abs_div, abs_of_pos hc0, div_lt_iff₀ hc0]
    have hδe := min_le_right (c.val - t.val) (c.val * ε)
    simpa only [δ, mul_comm] using lt_of_lt_of_le hs hδe
  have hparam : Set.Icc.convexComb (0 : unitInterval) c v = s := by
    apply Subtype.ext
    simp only [Set.Icc.coe_convexComb]
    change (1 - s.val / c.val) * 0 + (s.val / c.val) * c.val = s.val
    field_simp
    ring
  have hshorts : short v = p s := by
    change p (Set.Icc.convexComb (0 : unitInterval) c v) = p s
    rw [hparam]
  have hf := hF v hvu
  rw [hshorts] at hf
  change H (F (p s)) = (s.val, 0)
  rw [hf]
  apply Prod.ext
  · dsimp [H, v]
    field_simp
  · rfl

/-- Every interior point of every copied edge has a parameter-preserving plane
straightening, including loop edges. -/
theorem Drawing.exists_interior_straightening {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (D : Drawing J) (e : E)
    (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    ∃ (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (δ : ℝ), 0 < δ ∧
      ∀ s : ArcParameter, |s.val - t.val| < δ → F (D.curve e s) = (s.val, 0) := by
  let p : Path (D.curve e 0) (D.curve e 1) := ⟨⟨D.curve e, D.continuous e⟩, rfl, rfl⟩
  exact exists_plane_homeomorph_straightening_of_injOn_halfOpen p (D.injective e) t ht0 ht1

end FiniteAvalanches.Electrical.StatementGeometry
