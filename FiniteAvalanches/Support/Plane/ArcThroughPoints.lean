import FiniteAvalanches.Support.Plane.SquareNormalization
import FiniteAvalanches.Support.Plane.CompactAvoidance
import FiniteAvalanches.Electrical.Geometry.SimpleChain
import Mathlib.Analysis.Normed.Module.Connected

/-!
# A simple arc through finitely many points of a plane domain

A simple arc in a connected open plane set is extended to a further point by
normalizing it inside the closed unit square, joining the point to that square,
running around its boundary, and entering the square along the axis through
the free end of the arc. Induction gives a simple arc through any finite set of
points of the domain.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric Filter Topology

/-- The plane `ℝ × ℝ` has real dimension larger than one. -/
theorem one_lt_rank_real_prod : 1 < Module.rank ℝ (ℝ × ℝ) := by
  rw [rank_prod', Module.rank_self]
  norm_num

/-- A simple path meeting the pulled-back closed unit ball only at its endpoint
ends on the pulled-back unit sphere. -/
theorem norm_eq_one_of_first_hit (G : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) {a z : ℝ × ℝ}
    (q : Path a z) (hq : Function.Injective q) (hz : ‖G z‖ ≤ 1)
    (hhit : range q ∩ G ⁻¹' closedBall 0 1 = {z}) : ‖G z‖ = 1 := by
  apply le_antisymm hz
  let f : ℝ → ℝ := fun t => ‖G (q.extend t)‖
  have hf : Continuous f := continuous_norm.comp (G.continuous.comp q.continuous_extend)
  have hlim : Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 1 ≤ f t := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    by_contra hlt
    have hmem : q ⟨t, ht.1.le, ht.2.le⟩ ∈ range q ∩ G ⁻¹' closedBall 0 1 := by
      refine ⟨mem_range_self _, ?_⟩
      rw [mem_preimage, mem_closedBall, dist_zero_right]
      have hft : f t = ‖G (q ⟨t, ht.1.le, ht.2.le⟩)‖ := by
        simp only [f, Path.extend_apply q ⟨ht.1.le, ht.2.le⟩]
      linarith
    rw [hhit, mem_singleton_iff] at hmem
    have := congrArg Subtype.val (hq (hmem.trans q.target.symm))
    simp only [Set.Icc.coe_one] at this
    linarith [ht.2]
  have h1 := ge_of_tendsto hlim hev
  simpa only [f, Path.extend_one] using h1

/-- The straight path between two points of the real axis. -/
noncomputable def axisPath (u v : ℝ) : Path ((u, 0) : ℝ × ℝ) (v, 0) where
  toFun t := ((1 - (t : ℝ)) * u + (t : ℝ) * v, 0)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- A simple arc in a connected open plane set through finitely many given
points of that set. -/
theorem exists_injective_path_through_points {ι : Type*} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (s : Finset ι) (x : ι → ℝ × ℝ) (hx : ∀ i ∈ s, x i ∈ U) :
    ∃ a b : ℝ × ℝ, ∃ π : Path a b, Function.Injective π ∧ range π ⊆ U ∧
      ∀ i ∈ s, x i ∈ range π := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨a, ha⟩ := hUne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU a ha
    let b : ℝ × ℝ := (a.1 + ε / 2, a.2)
    have hb : b ∈ U := by
      apply hball
      rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [b, add_sub_cancel_left, sub_self, abs_zero]
      rw [abs_of_pos (by linarith)]
      exact max_lt (by linarith) hε
    have hab : a ≠ b := by
      intro h
      have h1 := congrArg Prod.fst h
      simp only [b] at h1
      linarith
    obtain ⟨z, hz, q, hq, hqU, _⟩ := exists_path_to_closed_set_avoiding_finite hU hconn
      (isClosed_singleton (x := b)) finite_empty
      ⟨⟨ha, notMem_empty a⟩, fun h => hab (mem_singleton_iff.mp h)⟩
      ⟨⟨hb, notMem_empty b⟩, mem_singleton b⟩
    exact ⟨a, z, q, hq, hqU.trans sdiff_subset, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | @insert k s hk ih =>
    obtain ⟨a, b, π, hπ, hπU, hmeet⟩ :=
      ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    by_cases hkπ : x k ∈ range π
    · refine ⟨a, b, π, hπ, hπU, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hkπ
      · exact hmeet i hi
    obtain ⟨G, c, hc, hc1, hG, hGU, hGP⟩ := exists_square_normalization π hπ hU hπU
      (isCompact_singleton (x := x k)) (disjoint_singleton_left.mpr hkπ)
    let K : Set (ℝ × ℝ) := G ⁻¹' closedBall 0 1
    have hK : IsClosed K := isClosed_closedBall.preimage G.continuous
    have hnormπ : ∀ t, ‖G (π t)‖ < 1 := by
      intro t
      rw [hG t, Prod.norm_mk, norm_zero, Real.norm_eq_abs, abs_mul, abs_of_pos hc]
      apply max_lt _ zero_lt_one
      have ht : |2 * (t : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
      nlinarith [abs_nonneg (2 * (t : ℝ) - 1)]
    have hπK : ∀ t, π t ∈ K := fun t => by
      rw [mem_preimage, mem_closedBall, dist_zero_right]
      exact (hnormπ t).le
    have hxk : x k ∈ U := hx k (Finset.mem_insert_self k s)
    have hxK : x k ∉ K := by
      rw [mem_preimage, mem_closedBall, dist_zero_right, not_le]
      exact hGP (x k) rfl
    have hbU : b ∈ U := hπU ⟨1, π.target⟩
    have hbK : b ∈ K := π.target ▸ hπK 1
    obtain ⟨z, hzK, q, hq, hqU, hqK⟩ := exists_path_to_closed_set_avoiding_finite hU hconn hK
      finite_empty ⟨⟨hxk, notMem_empty _⟩, hxK⟩ ⟨⟨hbU, notMem_empty _⟩, hbK⟩
    have hz1 : ‖G z‖ = 1 := by
      apply norm_eq_one_of_first_hit G q hq _ hqK
      simpa only [K, mem_preimage, mem_closedBall, dist_zero_right] using hzK
    have hsph : IsPathConnected (sphere (0 : ℝ × ℝ) 1) :=
      isPathConnected_sphere one_lt_rank_real_prod 0 zero_le_one
    have hzs : G z ∈ sphere (0 : ℝ × ℝ) 1 := by rw [mem_sphere_zero_iff_norm]; exact hz1
    have h10 : ((1 : ℝ), (0 : ℝ)) ∈ sphere (0 : ℝ × ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, Prod.norm_mk, norm_zero, norm_one, max_eq_left zero_le_one]
    let σ₁ : Path (G z) ((1 : ℝ), (0 : ℝ)) := (hsph.joinedIn (G z) hzs _ h10).somePath
    have hσ₁ : ∀ t, ‖σ₁ t‖ = 1 := fun t =>
      mem_sphere_zero_iff_norm.mp ((hsph.joinedIn (G z) hzs _ h10).somePath_mem t)
    let σ₂ : Path ((1 : ℝ), (0 : ℝ)) (c, 0) := axisPath 1 c
    let σ := σ₁.trans σ₂
    have hbc : b = G.symm (c, 0) := by
      have h := hG 1
      simp only [Set.Icc.coe_one, mul_one] at h
      norm_num at h
      rw [← h, G.symm_apply_apply]
    let σ' : Path z b := (σ.map G.symm.continuous).cast (G.symm_apply_apply z).symm hbc
    have hσ'mem : ∀ w ∈ range σ', ∃ v ∈ range σ, w = G.symm v := by
      rintro w ⟨u, rfl⟩
      exact ⟨σ u, mem_range_self u, rfl⟩
    have hσnorm : ∀ v ∈ range σ, ‖v‖ ≤ 1 ∧
        (‖v‖ = 1 ∨ ∃ r : ℝ, c ≤ r ∧ v = (r, 0)) := by
      intro v hv
      rw [Path.trans_range] at hv
      rcases hv with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact ⟨(hσ₁ u).le, Or.inl (hσ₁ u)⟩
      · have hu0 := u.2.1
        have hu1 := u.2.2
        have hr : c ≤ (1 - (u : ℝ)) * 1 + (u : ℝ) * c := by nlinarith
        have hr1 : (1 - (u : ℝ)) * 1 + (u : ℝ) * c ≤ 1 := by nlinarith
        refine ⟨?_, Or.inr ⟨_, hr, rfl⟩⟩
        change ‖(((1 - (u : ℝ)) * 1 + (u : ℝ) * c), (0 : ℝ))‖ ≤ 1
        rw [Prod.norm_mk, norm_zero, Real.norm_eq_abs, abs_of_pos (by linarith)]
        exact max_le hr1 zero_le_one
    let η : Path (x k) b := q.trans σ'
    have hηU : range η ⊆ U := by
      rw [Path.trans_range]
      apply union_subset (hqU.trans sdiff_subset)
      intro w hw
      obtain ⟨v, hv, rfl⟩ := hσ'mem w hw
      exact hGU v (hσnorm v hv).1
    have hbx : b ≠ x k := fun h => hkπ (h ▸ ⟨1, π.target⟩)
    obtain ⟨τ, hτ, hτsub⟩ := exists_injective_path_in_range η.symm hbx
    rw [Path.symm_range] at hτsub
    have hfg : ∀ s t, π s = τ t → π s = b := by
      intro s t hst
      have hmem := hτsub ⟨t, rfl⟩
      rw [← hst, Path.trans_range] at hmem
      rcases hmem with hmq | hmσ
      · have hz : π s ∈ range q ∩ K := ⟨hmq, hπK s⟩
        rw [hqK, mem_singleton_iff] at hz
        have := hnormπ s
        rw [hz, hz1] at this
        exact (lt_irrefl _ this).elim
      · obtain ⟨v, hv, hveq⟩ := hσ'mem _ hmσ
        have hGv : G (π s) = v := by rw [hveq, G.apply_symm_apply]
        rcases (hσnorm v hv).2 with hv1 | ⟨r, hr, rfl⟩
        · have := hnormπ s
          rw [hGv, hv1] at this
          exact (lt_irrefl _ this).elim
        · rw [hG s] at hGv
          have h1 := congrArg Prod.fst hGv
          simp only at h1
          have hs1 : (s : ℝ) = 1 := by
            have hs := s.2.2
            nlinarith
          have hs : s = 1 := Subtype.ext hs1
          rw [hs, π.target]
    refine ⟨a, x k, π.trans τ, path_trans_injective π τ hπ hτ hfg, ?_, ?_⟩
    · rw [Path.trans_range]
      exact union_subset hπU (hτsub.trans hηU)
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨1, (π.trans τ).target⟩
      · rw [Path.trans_range]
        exact Or.inl (hmeet i hi)

end FiniteAvalanches.Electrical.StatementGeometry
