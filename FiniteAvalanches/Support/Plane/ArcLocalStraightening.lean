import FiniteAvalanches.Support.Plane.SubarcCompletion
import FiniteAvalanches.Support.Plane.ArcStraightHomeomorph

/-!
# Local straightening of simple plane paths

Completing an interior subarc to a Jordan curve and applying the relative
Jordan–Schönflies theorem gives a parameter-preserving local straightening.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical

/-- Every interior point of a simple plane path has a parameter-preserving
whole-plane straightening on a neighborhood of that point. -/
theorem exists_plane_homeomorph_straightening_subpath
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    (t : unitInterval) (ht0 : 0 < t.val) (ht1 : t.val < 1) :
    ∃ (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (δ : ℝ), 0 < δ ∧
      ∀ s : unitInterval, |s.val - t.val| < δ → F (p s) = (s.val, 0) := by
  let a : unitInterval := ⟨t.val / 2, ⟨by linarith [t.property.1], by linarith [t.property.2]⟩⟩
  let b : unitInterval := ⟨(t.val + 1) / 2,
    ⟨by linarith [t.property.1], by linarith [t.property.2]⟩⟩
  have ha : 0 < a.val := by dsimp [a]; linarith
  have hat : a.val < t.val := by dsimp [a]; linarith
  have htb : t.val < b.val := by dsimp [b]; linarith
  have hb : b.val < 1 := by dsimp [b]; linarith
  have hab : a.val < b.val := lt_trans hat htb
  let m := p.subpath a b
  have hm : Function.Injective m := by
    intro u v huv
    have heq := congrArg Subtype.val (hp huv)
    simp only [Set.Icc.coe_convexComb] at heq
    apply Subtype.ext
    have hzero : ((u : ℝ) - v) * (b.val - a.val) = 0 := by nlinarith [heq]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt (sub_pos.mpr hab)))
  obtain ⟨q, hq, hmeet⟩ := exists_closing_arc_of_subpath p hp a b ha hab hb
  obtain ⟨F, hF⟩ := exists_plane_homeomorph_straightening_of_closing_arc m q hm hq hmeet
  let c : ℝ := b.val - a.val
  have hc : 0 < c := sub_pos.mpr hab
  let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toFun := fun z => (a.val + c * z.1, z.2)
    invFun := fun z => ((z.1 - a.val) / c, z.2)
    left_inv := by
      intro z
      apply Prod.ext
      · dsimp
        field_simp
        ring
      · rfl
    right_inv := by
      intro z
      apply Prod.ext
      · dsimp
        field_simp
        ring
      · rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let δ := min (t.val - a.val) (b.val - t.val)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hat) (sub_pos.mpr htb)
  refine ⟨F.trans H, δ, hδ, ?_⟩
  intro s hs
  have hsa : a.val < s.val := by
    have h := abs_lt.mp hs
    have hδa := min_le_left (t.val - a.val) (b.val - t.val)
    dsimp only [δ] at h
    linarith
  have hsb : s.val < b.val := by
    have h := abs_lt.mp hs
    have hδb := min_le_right (t.val - a.val) (b.val - t.val)
    dsimp only [δ] at h
    linarith
  let u : unitInterval := ⟨(s.val - a.val) / c,
    ⟨div_nonneg (by linarith) hc.le, (div_le_one hc).mpr (by dsimp [c]; linarith)⟩⟩
  have hparam : Set.Icc.convexComb a b u = s := by
    apply Subtype.ext
    simp only [Set.Icc.coe_convexComb]
    change (1 - ((s.val - a.val) / c)) * a.val +
      ((s.val - a.val) / c) * b.val = s.val
    field_simp
    dsimp [c]
    ring
  have hms : m u = p s := by
    change p (Set.Icc.convexComb a b u) = p s
    rw [hparam]
  have hf := hF u
  rw [hms] at hf
  change H (F (p s)) = (s.val, 0)
  rw [hf]
  apply Prod.ext
  · dsimp [H, u]
    field_simp
    ring
  · rfl

end FiniteAvalanches.Electrical.StatementGeometry
