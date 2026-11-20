import FiniteAvalanches.Support.Plane.ArcThroughPoints
import FiniteAvalanches.Support.Plane.RetainedTailReparam

/-!
# Separated arms to finitely many boundary accesses

A connected open plane set and finitely many simple boundary accesses, disjoint
inside the set, admit a common root joined to every access endpoint by simple
arms that meet only at the root or at a common endpoint, each arm ending with
a terminal part of its access traversed with exact speed.

A simple arc through the starting points of all accesses is normalized inside
the closed unit ball of the sup norm. Each access is followed from its last
exit from that ball, and joined to the centre by a radial segment.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric Filter Topology

/-- The radial segment from the origin to a point of the plane. -/
noncomputable def radialPath (v : ℝ × ℝ) : Path (0 : ℝ × ℝ) v where
  toFun t := (t : ℝ) • v
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- A path ending outside the pulled-back closed unit ball, and meeting that ball,
has a last exit time, at which it lies on the pulled-back unit sphere. -/
theorem exists_last_exit (G : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) {x y : ℝ × ℝ} (P : Path x y)
    {t₀ : unitInterval} (h₀ : ‖G (P t₀)‖ ≤ 1) (hy : 1 < ‖G y‖) :
    ∃ t₁ : unitInterval, t₁ ≠ 1 ∧ ‖G (P t₁)‖ = 1 ∧
      ∀ t : unitInterval, t₁ < t → 1 < ‖G (P t)‖ := by
  let f : ℝ → ℝ := fun t => ‖G (P.extend t)‖
  have hf : Continuous f := continuous_norm.comp (G.continuous.comp P.continuous_extend)
  let S : Set ℝ := Icc 0 1 ∩ f ⁻¹' Iic 1
  have hS : IsClosed S := isClosed_Icc.inter (isClosed_Iic.preimage hf)
  have hfI : ∀ t : unitInterval, f t = ‖G (P t)‖ := by
    intro t
    simp only [f, Path.extend_apply P t.2]
  have hSne : S.Nonempty := ⟨t₀, t₀.2, by rw [mem_preimage, mem_Iic, hfI]; exact h₀⟩
  have hbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hmem := hS.csSup_mem hSne hbdd
  let t₁ : unitInterval := ⟨sSup S, hmem.1⟩
  have hf1 : 1 < f 1 := by simpa only [f, Path.extend_one] using hy
  have ht₁ : (t₁ : ℝ) < 1 := by
    apply lt_of_le_of_ne hmem.1.2
    intro h
    have h' := hmem.2
    rw [mem_preimage, mem_Iic] at h'
    change f (sSup S) ≤ 1 at h'
    rw [h] at h'
    linarith
  have hafter : ∀ t : unitInterval, t₁ < t → 1 < ‖G (P t)‖ := by
    intro t ht
    rw [← hfI]
    by_contra hle
    have htS : (t : ℝ) ∈ S := ⟨t.2, by rw [mem_preimage, mem_Iic]; exact not_lt.mp hle⟩
    have := le_csSup hbdd htS
    exact (not_le.mpr (show (t₁ : ℝ) < t from ht)) this
  refine ⟨t₁, fun h => by rw [h] at ht₁; simp at ht₁, ?_, hafter⟩
  apply le_antisymm
  · rw [← hfI]
    exact hmem.2
  · rw [← hfI]
    have hlim : Tendsto f (𝓝[>] (t₁ : ℝ)) (𝓝 (f t₁)) :=
      hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (t₁ : ℝ), 1 ≤ f t := by
      filter_upwards [Ioo_mem_nhdsGT ht₁] with t ht
      have ht0 : 0 ≤ t := le_trans t₁.2.1 ht.1.le
      have h := hafter ⟨t, ht0, ht.2.le⟩ ht.1
      rw [← hfI] at h
      exact h.le
    exact ge_of_tendsto hlim hev

/-- Connected open plane sets admit separated arms to any finite family of simple
boundary accesses that are disjoint inside the set, with exact terminal speeds. -/
theorem exists_boundary_arm_family
    {ι : Type*} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hUne : U.Nonempty) (s : Finset ι) {x y : ι → ℝ × ℝ}
    (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U) :
    ∃ r ∈ U, ∃ w : ∀ i, Path r (y i),
      (∀ i ∈ s, Function.Injective (w i)) ∧
      (∀ i ∈ s, range (w i) ∩ Uᶜ = {y i}) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ z ∈ range (w i) ∩ range (w j),
        z = r ∨ z = y i ∧ y i = y j) ∧
      (∀ i ∈ s, ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w i t = p i ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  classical
  have hxU : ∀ i ∈ s, x i ∈ U := fun i hi => by
    simpa only [Path.source] using hinside i hi 0 (by norm_num)
  obtain ⟨a, b, π, hπ, hπU, hπx⟩ :=
    exists_injective_path_through_points hU hconn hUne s x hxU
  obtain ⟨G, c, hc, hc1, hG, hGU, -⟩ := exists_square_normalization π hπ hU hπU
    isCompact_empty (empty_disjoint _)
  have hnormπ : ∀ t, ‖G (π t)‖ ≤ 1 := by
    intro t
    rw [hG t, Prod.norm_mk, norm_zero, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
    apply max_le _ zero_le_one
    have ht : |2 * (t : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
    nlinarith [abs_nonneg (2 * (t : ℝ) - 1)]
  have hGy : ∀ i ∈ s, 1 < ‖G (y i)‖ := by
    intro i hi
    by_contra hle
    apply hout i hi
    simpa only [G.symm_apply_apply] using hGU (G (y i)) (not_lt.mp hle)
  have hexit : ∀ i, ∃ T : unitInterval, i ∈ s →
      T ≠ 1 ∧ ‖G (p i T)‖ = 1 ∧ ∀ t : unitInterval, T < t → 1 < ‖G (p i t)‖ := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨t₀, ht₀⟩ := hπx i hi
      have h₀ : ‖G (p i 0)‖ ≤ 1 := by rw [Path.source, ← ht₀]; exact hnormπ t₀
      obtain ⟨T, hT⟩ := exists_last_exit G (p i) h₀ (hGy i hi)
      exact ⟨T, fun _ => hT⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose T hT using hexit
  let g : ι → ℝ × ℝ := fun i => G (p i (T i))
  let r : ℝ × ℝ := G.symm 0
  have hrU : r ∈ U := hGU 0 (by rw [norm_zero]; exact zero_le_one)
  let ρ : ∀ i, Path r (p i (T i)) := fun i =>
    ((radialPath (g i)).map G.symm.continuous).cast rfl (G.symm_apply_apply _).symm
  let tail : ∀ i, Path (p i (T i)) (y i) := fun i =>
    ((p i).subpath (T i) 1).cast rfl (p i).target.symm
  let arm : ∀ i, Path r (y i) := fun i => (ρ i).trans (tail i)
  have hρG : ∀ i (t : unitInterval), G (ρ i t) = (t : ℝ) • g i := by
    intro i t
    change G (G.symm ((t : ℝ) • g i)) = _
    rw [G.apply_symm_apply]
  have hnorm_smul : ∀ i ∈ s, ∀ t : ℝ, 0 ≤ t → ‖t • g i‖ = t := by
    intro i hi t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, (hT i hi).2.1, mul_one]
  have htail_val : ∀ i (u : unitInterval),
      tail i u = p i (Set.Icc.convexComb (T i) 1 u) := fun i u => rfl
  have htail_ge : ∀ i (u : unitInterval),
      (T i : ℝ) ≤ (Set.Icc.convexComb (T i) 1 u : ℝ) := by
    intro i u
    rw [Set.Icc.coe_convexComb]
    have := (T i).2.2
    have := u.2.1
    simp only [Set.Icc.coe_one]
    nlinarith
  have hcases : ∀ i ∈ s, ∀ z ∈ range (arm i),
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ G z = t • g i) ∨
        (∃ t : unitInterval, T i < t ∧ z = p i t ∧ 1 < ‖G z‖) := by
    intro i hi z hz
    rw [Path.trans_range] at hz
    rcases hz with ⟨t, rfl⟩ | ⟨u, rfl⟩
    · exact Or.inl ⟨t, t.2.1, t.2.2, hρG i t⟩
    · rw [htail_val]
      rcases eq_or_lt_of_le (htail_ge i u) with heq | hlt
      · left
        have hT' : Set.Icc.convexComb (T i) 1 u = T i := Subtype.ext heq.symm
        refine ⟨1, zero_le_one, le_rfl, ?_⟩
        rw [hT', one_smul]
      · right
        exact ⟨_, hlt, rfl, (hT i hi).2.2 _ hlt⟩
  have hinj_arm : ∀ i ∈ s, Function.Injective (arm i) := by
    intro i hi
    have hg0 : g i ≠ 0 := by
      intro h
      have := (hT i hi).2.1
      rw [show G (p i (T i)) = g i from rfl, h, norm_zero] at this
      exact zero_ne_one this
    have hρ : Function.Injective (ρ i) := by
      intro t t' h
      have h' := congrArg G h
      rw [hρG, hρG] at h'
      exact Subtype.ext (smul_left_injective ℝ hg0 h')
    have htail : Function.Injective (tail i) := by
      intro u v huv
      rw [htail_val, htail_val] at huv
      have h := congrArg Subtype.val (hp i hi huv)
      simp only [Set.Icc.coe_convexComb, Set.Icc.coe_one] at h
      have hT1 : (T i : ℝ) ≠ 1 := fun h => (hT i hi).1 (Subtype.ext h)
      apply Subtype.ext
      have hz : ((u : ℝ) - v) * (1 - (T i : ℝ)) = 0 := by nlinarith [h]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hT1.symm))
    apply path_trans_injective (ρ i) (tail i) hρ htail
    intro t u htu
    rw [htail_val] at htu
    rcases eq_or_lt_of_le (htail_ge i u) with heq | hlt
    · have hT' : Set.Icc.convexComb (T i) 1 u = T i := Subtype.ext heq.symm
      rw [htu, hT']
    · have h1 := (hT i hi).2.2 _ hlt
      rw [← htu, hρG, hnorm_smul i hi t t.2.1] at h1
      exact absurd t.2.2 (not_le.mpr h1)
  have hexists : ∀ i, ∃ w : Path r (y i), i ∈ s →
      Function.Injective w ∧ range w ⊆ range (arm i) ∧
        ∃ u : unitInterval, u ≠ 1 ∧
          ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
            w t = p i ⟨2 * (t : ℝ) - 1, by
              constructor
              · have := u.property.1
                linarith
              · linarith [t.property.2]⟩ := by
    intro i
    by_cases hi : i ∈ s
    · have hsub : range ((p i).subpath (T i) 1) ⊆ range (arm i) := by
        rw [Path.trans_range]
        exact subset_union_right
      obtain ⟨w, hw, hwsub, hspeed⟩ := exists_path_with_parametrized_retained_tail
        (arm i) (p i) (hinj_arm i hi) (hp i hi) (hT i hi).1 hsub
      exact ⟨w, fun _ => ⟨hw, hwsub, hspeed⟩⟩
    · exact ⟨arm i, fun h => (hi h).elim⟩
  choose w hw using hexists
  have hgU : ∀ i ∈ s, p i (T i) ∈ U := by
    intro i hi
    have h := hGU (g i) (hT i hi).2.1.le
    simpa only [g, G.symm_apply_apply] using h
  have hg_ne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g i ≠ g j := by
    intro i hi j hj hij h
    have hpq : p i (T i) = p j (T j) := G.injective h
    exact disjoint_left.mp (hd i hi j hj hij) ⟨mem_range_self _, hgU i hi⟩
      (hpq ▸ mem_range_self _)
  have hradial : ∀ z : ℝ × ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ i ∈ s, G z = t • g i → z ∈ U := by
    intro z t ht0 ht1 i hi hz
    have h := hGU (G z) (by rw [hz, hnorm_smul i hi t ht0]; exact ht1)
    simpa only [G.symm_apply_apply] using h
  refine ⟨r, hrU, w, fun i hi => ((hw i) hi).1, ?_, ?_, fun i hi => ((hw i) hi).2.2⟩
  · intro i hi
    apply Subset.antisymm
    · rintro z ⟨hz, hzU⟩
      rcases hcases i hi z ((hw i hi).2.1 hz) with ⟨t, ht0, ht1, hGz⟩ | ⟨t, _, rfl, _⟩
      · exact (hzU (hradial z t ht0 ht1 i hi hGz)).elim
      · by_cases ht : t = 1
        · rw [ht, Path.target]
          rfl
        · exact (hzU (hinside i hi t ht)).elim
    · rintro z rfl
      exact ⟨⟨1, (w i).target⟩, hout i hi⟩
  · intro i hi j hj hij z ⟨hzi, hzj⟩
    rcases hcases i hi z ((hw i hi).2.1 hzi) with ⟨t, ht0, ht1, hGi⟩ | ⟨t, _, hzt, hzn⟩ <;>
      rcases hcases j hj z ((hw j hj).2.1 hzj) with ⟨t', ht0', ht1', hGj⟩ | ⟨t', _, hzt', hzn'⟩
    · have hnorm : t = t' := by
        have h := congrArg norm (hGi.symm.trans hGj)
        rwa [hnorm_smul i hi t ht0, hnorm_smul j hj t' ht0'] at h
      subst hnorm
      by_cases ht : t = 0
      · left
        rw [ht, zero_smul] at hGi
        rw [← G.symm_apply_apply z, hGi]
      · have h := hGi.symm.trans hGj
        exact (hg_ne i hi j hj hij (smul_right_injective _ ht h)).elim
    · have h := hzn'
      rw [hGi, hnorm_smul i hi t ht0] at h
      exact absurd ht1 (not_le.mpr h)
    · have h := hzn
      rw [hGj, hnorm_smul j hj t' ht0'] at h
      exact absurd ht1' (not_le.mpr h)
    · right
      by_cases hzU : z ∈ U
      · exact (disjoint_left.mp (hd i hi j hj hij) ⟨hzt ▸ mem_range_self _, hzU⟩
          (hzt' ▸ mem_range_self _)).elim
      · have ht : t = 1 := by
          by_contra h
          exact hzU (hzt ▸ hinside i hi t h)
        have ht' : t' = 1 := by
          by_contra h
          exact hzU (hzt' ▸ hinside j hj t' h)
        rw [ht, Path.target] at hzt
        rw [ht', Path.target] at hzt'
        exact ⟨hzt, hzt.symm.trans hzt'⟩

end FiniteAvalanches.Electrical.StatementGeometry
