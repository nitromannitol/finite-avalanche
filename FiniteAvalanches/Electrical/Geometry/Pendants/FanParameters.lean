import FiniteAvalanches.Electrical.Geometry.Pendants.LeafAngles

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
open Filter Set Metric
noncomputable section

/-- A small common positive parameter both separates different attachments and orders every leaf. -/
theorem exists_fan_parameter (α : Fin 6 → ℝ) (_hα : Monotone α)
    (_hw : α 5 ≤ α 0+2*Real.pi) :
    ∃ l : ℝ, 0<l ∧ l<1 ∧ l*(4*Real.pi^2+1)<1 ∧
      ∀ i j, unitPoint (α i) ≠ unitPoint (α j) →
        dist (scaledPoint (1-l) (unitPoint (α i))) (unitPoint (α i)) <
          dist (unitPoint (α i)) (unitPoint (α j))/3 ∧
        dist (unitPoint (leafAngle α l i)) (unitPoint (α i)) <
          dist (unitPoint (α i)) (unitPoint (α j))/3 := by
  have hsmall : ∀ᶠ l : ℝ in nhds 0, ∀ i j,
      unitPoint (α i) ≠ unitPoint (α j) →
        dist (scaledPoint (1-l) (unitPoint (α i))) (unitPoint (α i)) <
          dist (unitPoint (α i)) (unitPoint (α j))/3 ∧
        dist (unitPoint (leafAngle α l i)) (unitPoint (α i)) <
          dist (unitPoint (α i)) (unitPoint (α j))/3 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : unitPoint (α i)=unitPoint (α j)
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    have hr : 0<dist (unitPoint (α i)) (unitPoint (α j))/3 :=
      div_pos (dist_pos.mpr hij) (by norm_num)
    have hA : Continuous (fun l : ℝ => scaledPoint (1-l) (unitPoint (α i))) := by
      unfold scaledPoint
      fun_prop
    have hB : Continuous (fun l : ℝ => unitPoint (leafAngle α l i)) := by
      unfold unitPoint leafAngle
      fun_prop
    have hAe : ∀ᶠ l : ℝ in nhds 0,
        scaledPoint (1-l) (unitPoint (α i)) ∈ ball (unitPoint (α i))
          (dist (unitPoint (α i)) (unitPoint (α j))/3) := by
      have ht : Tendsto (fun l : ℝ => scaledPoint (1-l) (unitPoint (α i))) (nhds 0)
          (nhds (unitPoint (α i))) := by
        simpa [scaledPoint] using (hA.continuousAt (x := (0:ℝ))).tendsto
      exact ht.eventually (ball_mem_nhds (unitPoint (α i)) hr)
    have hBe : ∀ᶠ l : ℝ in nhds 0,
        unitPoint (leafAngle α l i) ∈ ball (unitPoint (α i))
          (dist (unitPoint (α i)) (unitPoint (α j))/3) := by
      have ht : Tendsto (fun l : ℝ => unitPoint (leafAngle α l i)) (nhds 0)
          (nhds (unitPoint (α i))) := by
        simpa [leafAngle] using (hB.continuousAt (x := (0:ℝ))).tendsto
      exact ht.eventually (ball_mem_nhds (unitPoint (α i)) hr)
    filter_upwards [hAe,hBe] with l ha hb
    intro _
    exact ⟨ha,hb⟩
  obtain ⟨ε,hε,hεsmall⟩ := Metric.eventually_nhds_iff.mp hsmall
  let l := min (ε/2) (1/(2*(4*Real.pi^2+1)))
  have hden : 0<4*Real.pi^2+1 := by positivity
  have hl0 : 0<l := lt_min (div_pos hε (by norm_num)) (by positivity)
  have hlε : l<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlb : l*(4*Real.pi^2+1)<1 := by
    have hle : l≤1/(2*(4*Real.pi^2+1)) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_right hle hden.le
    have he : (1/(2*(4*Real.pi^2+1)))*(4*Real.pi^2+1)=(1/2:ℝ) := by
      field_simp
    rw [he] at hm
    linarith
  have hl1 : l<1 := by
    have hn : 0≤l*(4*Real.pi^2) := mul_nonneg hl0.le (by positivity)
    nlinarith only [hn,hlb]
  refine ⟨l,hl0,hl1,hlb,?_⟩
  exact hεsmall (by simpa [Real.dist_eq,abs_of_pos hl0] using hlε)

/-- Different attachment neighborhoods separate the complete straight segments. -/
theorem different_attachment_intersection (p q a b d f : ℝ × ℝ)
    (hpq : p ≠ q)
    (ha : dist a p < dist p q/3) (hb : dist b p < dist p q/3)
    (hd : dist d q < dist p q/3) (hf : dist f q < dist p q/3)
    (s t : ℝ) (hs0 : 0≤s) (hs1 : s≤1) (ht0 : 0≤t) (ht1 : t≤1) :
    segment a b s ≠ segment d f t := by
  intro h
  have hs : segment a b s ∈ ball p (dist p q/3) :=
    (convex_ball p _ : Convex ℝ _ ) ha hb (sub_nonneg.mpr hs1) hs0 (by ring)
  have ht : segment d f t ∈ ball q (dist p q/3) :=
    (convex_ball q _ : Convex ℝ _ ) hd hf (sub_nonneg.mpr ht1) ht0 (by ring)
  rw [← h] at ht
  have htri := dist_triangle p (segment a b s) q
  have hs' : dist p (segment a b s)<dist p q/3 := by simpa [dist_comm] using hs
  have ht' : dist (segment a b s) q<dist p q/3 := ht
  have hpos := dist_pos.mpr hpq
  linarith

end
end FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
