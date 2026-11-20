import FiniteAvalanches.Support.Plane.OuterRedrawing.Recursion
import FiniteAvalanches.Support.Plane.OuterRedrawing.PathCurve
import FiniteAvalanches.Support.Plane.OrientedArcStraightening
import FiniteAvalanches.Electrical.Geometry.BSST

/-!
# Redrawing in the disk with a boundary path on the circle

Let a simple path of a finite plane drawing lie on the boundary of the unbounded
face. The edge curves of the path form one simple arc, which an oriented chart
straightens onto the horizontal unit segment with equally spaced vertices; the
unbounded face is carried onto an unbounded complementary component of the
straightened drawing. The square realization of the whole graph, with the whole
path as its stretch, draws the graph in the closed square with the path on the
top edge, and the radial map from the square onto the disk carries the top edge
into the circle. A path without edges is handled by shrinking the drawing.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology
open FiniteAvalanches.Electrical.Source (drawingTrace)
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- A drawing transported by a continuous injective map of the plane. -/
def Drawing.mapEmbedding (D : Drawing J) (Ψ : ℝ × ℝ → ℝ × ℝ) (hc : Continuous Ψ)
    (hi : Function.Injective Ψ) : Drawing J where
  point v := Ψ (D.point v)
  point_injective := hi.comp D.point_injective
  curve e t := Ψ (D.curve e t)
  continuous e := hc.comp (D.continuous e)
  injective e := hi.comp_injOn (D.injective e)
  start e := congrArg Ψ (D.start e)
  finish e := congrArg Ψ (D.finish e)
  avoids e t h0 h1 v hv := D.avoids e t h0 h1 v (hi hv)
  intersects e f hef s t hst := D.intersects e f hef s t (hi hst)

theorem drawingTrace_mapEmbedding (D : Drawing J) (Ψ : ℝ × ℝ → ℝ × ℝ) (hc : Continuous Ψ)
    (hi : Function.Injective Ψ) :
    drawingTrace (Drawing.mapEmbedding D Ψ hc hi) = Ψ '' drawingTrace D := by
  ext z
  constructor
  · rintro (⟨v, rfl⟩ | hz)
    · exact ⟨_, Or.inl ⟨v, rfl⟩, rfl⟩
    · obtain ⟨e, t, rfl⟩ := mem_iUnion.mp hz
      exact ⟨_, Or.inr (mem_iUnion.mpr ⟨e, t, rfl⟩), rfl⟩
  · rintro ⟨w, (⟨v, rfl⟩ | hw), rfl⟩
    · exact Or.inl ⟨v, rfl⟩
    · obtain ⟨e, t, rfl⟩ := mem_iUnion.mp hw
      exact Or.inr (mem_iUnion.mpr ⟨e, t, rfl⟩)

/-- An unbounded complementary component of a drawing is an outer face. -/
theorem outerFace_faceRegion (D : Drawing J) (F : BSST.Face D)
    (hF : ¬ IsBounded (BSST.faceRegion D F)) : OuterFace D (BSST.faceRegion D F) := by
  obtain ⟨x₀, rfl⟩ := ConnectedComponents.surjective_coe F
  have hreg : BSST.faceRegion D (ConnectedComponents.mk x₀) =
      Subtype.val '' connectedComponent x₀ := by
    ext z
    constructor
    · rintro ⟨hz, hzF⟩
      exact ⟨⟨z, hz⟩, ConnectedComponents.coe_eq_coe'.mp hzF, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, ConnectedComponents.coe_eq_coe'.mpr hw⟩
  refine ⟨?_, ?_, hF, ?_⟩
  · rw [hreg]
    exact isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  · rw [Set.disjoint_left]
    rintro z ⟨hz, -⟩ hzT
    exact hz hzT
  · intro K hK hKT ⟨z₀, hz₀K, hz₀, hz₀F⟩
    let K' : Set {z // z ∉ drawingTrace D} := Subtype.val ⁻¹' K
    have hKK' : Subtype.val '' K' = K := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        exact ⟨⟨z, fun hzT => hKT.ne_of_mem hz hzT rfl⟩, hz, rfl⟩
    have hK' : IsPreconnected K' := by
      have h1 := hK
      rw [← hKK'] at h1
      exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp h1
    have hsub := hK'.subset_connectedComponent (x := ⟨z₀, hz₀⟩) hz₀K
    intro z hz
    have hzT : z ∉ drawingTrace D := fun hzT => hKT.ne_of_mem hz hzT rfl
    refine ⟨hzT, ?_⟩
    rw [← hz₀F]
    exact ConnectedComponents.coe_eq_coe'.mpr
      (hsub (show (⟨z, hzT⟩ : {z // z ∉ drawingTrace D}) ∈ K' from hz))

/-- An outer face transported by a homeomorphism of the plane. -/
theorem OuterFace.map {D : Drawing J} {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (Φ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) :
    OuterFace (Drawing.mapEmbedding D Φ Φ.continuous Φ.injective) (Φ '' U) := by
  refine ⟨hU.preconnected.image _ Φ.continuous.continuousOn, ?_, fun hb => hU.unbounded ?_, ?_⟩
  · rw [drawingTrace_mapEmbedding]
    exact (Set.disjoint_image_iff Φ.injective).mpr hU.disjoint
  · have := isBounded_image_of_homeomorph' Φ.symm hb
    rwa [image_image, show (fun x => Φ.symm (Φ x)) = id from funext Φ.symm_apply_apply,
      image_id] at this
  · intro K hK hKT ⟨z, hzK, u, hu, hzu⟩
    rw [drawingTrace_mapEmbedding] at hKT
    have hK' : Φ.symm '' K ⊆ U := by
      refine hU.maximal _ (hK.image _ Φ.symm.continuous.continuousOn) ?_ ⟨u, ?_, hu⟩
      · rw [Set.disjoint_left]
        rintro _ ⟨k, hk, rfl⟩ hkT
        exact hKT.ne_of_mem hk ⟨_, hkT, Φ.apply_symm_apply k⟩ rfl
      · exact ⟨z, hzK, by rw [← hzu, Φ.symm_apply_apply]⟩
    intro k hk
    exact ⟨_, hK' ⟨k, hk, rfl⟩, Φ.apply_symm_apply k⟩

/-- The Euclidean norm of the drawing plane. -/
def euclidNorm (w : ℝ × ℝ) : ℝ := Real.sqrt (w.1 ^ 2 + w.2 ^ 2)

theorem sq_euclidNorm (w : ℝ × ℝ) : euclidNorm w ^ 2 = w.1 ^ 2 + w.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem continuous_euclidNorm : Continuous euclidNorm := by
  unfold euclidNorm
  fun_prop

theorem norm_le_euclidNorm (w : ℝ × ℝ) : ‖w‖ ≤ euclidNorm w := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, euclidNorm]
  apply max_le
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg w.2])
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg w.1])

theorem euclidNorm_smul (c : ℝ) (w : ℝ × ℝ) : euclidNorm (c • w) = |c| * euclidNorm w := by
  rw [euclidNorm, euclidNorm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul, mul_pow,
    mul_pow, ← mul_add, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The radial map carrying the square `[-1, 1]²` onto the closed unit disk. -/
def squareToDisk (w : ℝ × ℝ) : ℝ × ℝ := (‖w‖ / euclidNorm w) • w

theorem euclidNorm_squareToDisk (w : ℝ × ℝ) : euclidNorm (squareToDisk w) = ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [squareToDisk, euclidNorm]
  · have he : 0 < euclidNorm w := (norm_pos_iff.mpr hw).trans_le (norm_le_euclidNorm w)
    rw [squareToDisk, euclidNorm_smul, abs_of_nonneg (div_nonneg (norm_nonneg _) he.le),
      div_mul_cancel₀ _ he.ne']

theorem norm_squareToDisk_le (w : ℝ × ℝ) : ‖squareToDisk w‖ ≤ ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [squareToDisk]
  · have he : 0 < euclidNorm w := (norm_pos_iff.mpr hw).trans_le (norm_le_euclidNorm w)
    have hc : ‖w‖ / euclidNorm w ≤ 1 := (div_le_one he).mpr (norm_le_euclidNorm w)
    rw [squareToDisk, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) he.le)]
    calc ‖w‖ / euclidNorm w * ‖w‖ ≤ 1 * ‖w‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = ‖w‖ := one_mul _

theorem continuous_squareToDisk : Continuous squareToDisk := by
  rw [continuous_iff_continuousAt]
  intro w
  rcases eq_or_ne w 0 with rfl | hw
  · rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun x hx => ?_⟩
    have h0 : squareToDisk 0 = 0 := by simp [squareToDisk]
    rw [h0, dist_zero_right]
    rw [dist_zero_right] at hx
    exact (norm_squareToDisk_le x).trans_lt hx
  · have he : euclidNorm w ≠ 0 :=
      ((norm_pos_iff.mpr hw).trans_le (norm_le_euclidNorm w)).ne'
    exact ((continuous_norm.continuousAt.div continuous_euclidNorm.continuousAt he).smul
      continuousAt_id)

theorem squareToDisk_injective : Function.Injective squareToDisk := by
  intro w w' h
  have hn : ‖w‖ = ‖w'‖ := by
    rw [← euclidNorm_squareToDisk w, ← euclidNorm_squareToDisk w', h]
  rcases eq_or_ne w 0 with rfl | hw
  · rw [norm_zero] at hn
    exact (norm_eq_zero.mp hn.symm).symm
  have hw' : w' ≠ 0 := fun h0 => hw (norm_eq_zero.mp (hn.trans (by rw [h0, norm_zero])))
  have he : 0 < euclidNorm w := (norm_pos_iff.mpr hw).trans_le (norm_le_euclidNorm w)
  have he' : 0 < euclidNorm w' := (norm_pos_iff.mpr hw').trans_le (norm_le_euclidNorm w')
  have hc : 0 < ‖w‖ / euclidNorm w := div_pos (norm_pos_iff.mpr hw) he
  have hc' : 0 < ‖w'‖ / euclidNorm w' := div_pos (norm_pos_iff.mpr hw') he'
  have hsup : ‖w‖ / euclidNorm w * ‖w‖ = ‖w'‖ / euclidNorm w' * ‖w'‖ := by
    have := congrArg norm h
    rw [squareToDisk, squareToDisk, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hc, abs_of_pos hc'] at this
    exact this
  have hcc : ‖w‖ / euclidNorm w = ‖w'‖ / euclidNorm w' := by
    have h3 : ‖w‖ / euclidNorm w * ‖w‖ = ‖w'‖ / euclidNorm w' * ‖w‖ := by
      calc ‖w‖ / euclidNorm w * ‖w‖ = ‖w'‖ / euclidNorm w' * ‖w'‖ := hsup
        _ = ‖w'‖ / euclidNorm w' * ‖w‖ := by rw [hn]
    exact mul_right_cancel₀ (norm_pos_iff.mpr hw).ne' h3
  have h2 : (‖w‖ / euclidNorm w) • w = (‖w‖ / euclidNorm w) • w' := by
    have := h
    rw [squareToDisk, squareToDisk, ← hcc] at this
    exact this
  exact smul_right_injective _ hc.ne' h2

theorem squareToDisk_mem_disk {w : ℝ × ℝ} (hw : ‖w‖ ≤ 1) : squareToDisk w ∈ disk := by
  change (squareToDisk w).1 ^ 2 + (squareToDisk w).2 ^ 2 ≤ 1
  rw [← sq_euclidNorm, euclidNorm_squareToDisk]
  nlinarith [norm_nonneg w]

theorem squareToDisk_mem_circle {w : ℝ × ℝ} (hw : ‖w‖ = 1) : squareToDisk w ∈ circle := by
  change (squareToDisk w).1 ^ 2 + (squareToDisk w).2 ^ 2 = 1
  rw [← sq_euclidNorm, euclidNorm_squareToDisk, hw, one_pow]

/-- The contraction of the plane into the square `[-1/2, 1/2]²`. -/
def shrink (w : ℝ × ℝ) : ℝ × ℝ := (2 * (1 + ‖w‖))⁻¹ • w

theorem continuous_shrink : Continuous shrink := by
  unfold shrink
  exact ((continuous_const.mul (continuous_const.add continuous_norm)).inv₀
    fun w => (mul_pos two_pos (add_pos_of_pos_of_nonneg one_pos (norm_nonneg w))).ne').smul
      continuous_id

theorem norm_shrink (w : ℝ × ℝ) : ‖shrink w‖ = ‖w‖ / (2 * (1 + ‖w‖)) := by
  rw [shrink, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_eq_div]

theorem shrink_injective : Function.Injective shrink := by
  intro w w' h
  have hn : ‖w‖ = ‖w'‖ := by
    have := congrArg norm h
    rw [norm_shrink, norm_shrink] at this
    have h1 : (0 : ℝ) < 2 * (1 + ‖w‖) := by positivity
    have h2 : (0 : ℝ) < 2 * (1 + ‖w'‖) := by positivity
    rw [div_eq_div_iff h1.ne' h2.ne'] at this
    nlinarith
  have := h
  rw [shrink, shrink, ← hn] at this
  exact smul_right_injective _ (by positivity) this

theorem shrink_mem_disk (w : ℝ × ℝ) : shrink w ∈ disk := by
  change (shrink w).1 ^ 2 + (shrink w).2 ^ 2 ≤ 1
  have hn : ‖shrink w‖ ≤ 1 / 2 := by
    rw [norm_shrink, div_le_iff₀ (by positivity)]
    linarith [norm_nonneg w]
  have h1 : |(shrink w).1| ≤ 1 / 2 := (norm_fst_le (shrink w)).trans hn
  have h2 : |(shrink w).2| ≤ 1 / 2 := (norm_snd_le (shrink w)).trans hn
  rw [abs_le] at h1 h2
  nlinarith

/-- A simple path of a drawing on the boundary of an unbounded complementary
component can be redrawn on the unit circle, with the whole drawing in the
closed unit disk. -/
theorem exists_disk_redrawing (D : Drawing J) (m : ℕ) (path : Fin (m + 1) → V)
    (hpath : Function.Injective path) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
      (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ))
    (F : BSST.Face D) (hF : ¬ IsBounded (BSST.faceRegion D F))
    (hfront : ∀ i t, D.curve (copies i) t ∈ frontier (BSST.faceRegion D F)) :
    ∃ D' : Drawing J, (∀ x, D'.point x ∈ disk) ∧ (∀ e t, D'.curve e t ∈ disk) ∧
      ∀ i t, D'.curve (copies i) t ∈ circle := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨Drawing.mapEmbedding D shrink continuous_shrink shrink_injective,
      fun x => shrink_mem_disk _, fun e t => shrink_mem_disk _, fun i => i.elim0⟩
  obtain ⟨γ, hγc, hγi, hγv, hγe⟩ := exists_pathCurve D hpath hends hm
  obtain ⟨c, hc⟩ := exists_orientedChart_arc_straightening γ hγc hγi
  let Φ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := c.map
  let D₀ := Drawing.mapEmbedding D Φ Φ.continuous Φ.injective
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h₀ : StraightPath D₀ m path copies := by
    refine ⟨hm, hpath, hends, fun k => ?_, fun i s => ?_, fun i s => ?_⟩
    · have hk : (k : ℝ) / m ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, (div_le_one hmr).mpr (by exact_mod_cast Nat.lt_succ_iff.mp k.2)⟩
      change Φ (D.point (path k)) = _
      rw [← hγv k ⟨_, hk⟩ rfl]
      exact hc _
    · obtain ⟨t, -, -, ht⟩ := hγe i s
      change (Φ (D.curve (copies i) s)).2 = 0
      rw [← ht]
      change (c.map (γ t)).2 = 0
      rw [hc]
    · obtain ⟨t, ht0, ht1, ht⟩ := hγe i s
      change (i : ℝ) / m ≤ (Φ (D.curve (copies i) s)).1 ∧
        (Φ (D.curve (copies i) s)).1 ≤ ((i : ℝ) + 1) / m
      rw [← ht]
      change (i : ℝ) / m ≤ (c.map (γ t)).1 ∧ (c.map (γ t)).1 ≤ ((i : ℝ) + 1) / m
      rw [hc]
      exact ⟨ht0, ht1⟩
  have hU₀ : OuterFace D₀ (Φ '' BSST.faceRegion D F) := (outerFace_faceRegion D F hF).map Φ
  have hfront₀ : ∀ i t, D₀.curve (copies i) t ∈ closure (Φ '' BSST.faceRegion D F) := by
    intro i t
    rw [← Φ.image_closure]
    exact ⟨_, frontier_subset_closure (hfront i t), rfl⟩
  obtain ⟨R⟩ := h₀.exists_squareRealization hU₀ hfront₀ _ univ Finset.univ rfl hm le_rfl
    (fun _ _ _ => mem_univ _) (fun _ _ _ => Finset.mem_univ _)
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  rw [Finset.coe_univ] at R
  let D₁ := R.toPartialDrawing.toDrawing
  have hsq : ∀ z ∈ R.toPartialDrawing.trace, ‖z‖ ≤ 1 := fun z hz => by
    have := R.trace_sub hz
    rwa [mem_closedBall, dist_zero_right] at this
  refine ⟨Drawing.mapEmbedding D₁ squareToDisk continuous_squareToDisk squareToDisk_injective,
    fun x => squareToDisk_mem_disk (hsq _ (R.toPartialDrawing.point_mem_trace (mem_univ x))),
    fun e t => squareToDisk_mem_disk (hsq _ (R.toPartialDrawing.curve_mem_trace (mem_univ e) t)),
    fun i t => squareToDisk_mem_circle ?_⟩
  obtain ⟨h1, h2, h3⟩ := R.path_curve i (Nat.zero_le _) i.2 t
  have hz := hsq _ (R.toPartialDrawing.curve_mem_trace (mem_univ (copies i)) t)
  change ‖R.curve (copies i) t‖ = 1
  apply le_antisymm hz
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, h1, abs_one]
  exact le_max_right _ _

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
