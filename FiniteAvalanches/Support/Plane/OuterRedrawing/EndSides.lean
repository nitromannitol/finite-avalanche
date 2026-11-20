import FiniteAvalanches.Support.Plane.OuterRedrawing.SideSeparation

/-!
# Edge ends at an interior vertex of a straight boundary path

Let an arc of the drawing leave an interior path vertex on one side of the
horizontal line and reach another path vertex, meeting the unit segment only at
its two ends. Together with the segment between the two vertices it forms a
Jordan curve. Near the vertex, the path edge pointing away from the arc lies in
the unbounded component's closure on the curve's outer side, while the collar on
the arc's side of the path edge pointing towards the arc lies on the inner side.
Hence that collar is not contained in the unbounded component.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology
open FiniteAvalanches.Electrical.Source (drawingTrace)

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
variable {D : Drawing J} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

/-- The unit segment lies on the drawing. -/
theorem unitSeg_subset_trace : unitSeg ⊆ drawingTrace D := by
  rintro w ⟨hw2, hw0, hw1⟩
  obtain ⟨i, hi0, hi1⟩ := exists_index_of_mem_Icc h.pos hw0 hw1
  obtain ⟨t, ht⟩ := h.mem_range_curve i hi0 hi1
  exact Or.inr (mem_iUnion.mpr ⟨_, t, ht.trans (Prod.ext rfl hw2.symm)⟩)

/-- A path edge lies in the closure of an accumulating component. -/
theorem axis_mem_closure {U : Set (ℝ × ℝ)} (hfront : ∀ i t, D.curve (copies i) t ∈ closure U)
    {w : ℝ × ℝ} (hw : w ∈ unitSeg) : w ∈ closure U := by
  obtain ⟨hw2, hw0, hw1⟩ := hw
  obtain ⟨i, hi0, hi1⟩ := exists_index_of_mem_Icc h.pos hw0 hw1
  obtain ⟨t, ht⟩ := h.mem_range_curve i hi0 hi1
  rw [show w = (w.1, 0) from Prod.ext rfl hw2, ← ht]
  exact hfront i t

/-- An arc leaving an interior path vertex upwards towards a later path vertex
excludes the upper collar of the next path edge from the unbounded component. -/
theorem not_upperCollar_of_up_right {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U)
    {a : ℕ} (ha0 : 0 < a) (ham : a < m) {c : Fin (m + 1)} (hac : a < (c : ℕ))
    (β : Path (D.point (path ⟨a, by omega⟩)) (D.point (path c))) (hβ : Function.Injective β)
    (hβtrace : range β ⊆ drawingTrace D)
    (hβseg : ∀ t, β t ∈ unitSeg → β t = D.point (path ⟨a, by omega⟩) ∨ β t = D.point (path c))
    (hβup : ∃ τ > 0, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < τ → 0 < (β t).2) :
    ¬ upperCollar D copies ⟨a, ham⟩ ⊆ U := by
  intro hcol
  have hm := h.m_pos_real
  set xa : ℝ := (a : ℝ) / m with hxa
  set xc : ℝ := (c : ℝ) / m with hxc
  have hpa : D.point (path ⟨a, by omega⟩) = (xa, 0) := by rw [h.point]
  have hpc : D.point (path c) = (xc, 0) := by rw [h.point]
  have hac' : xa + 1 / m ≤ xc := by
    rw [hxa, hxc, ← add_div, div_le_div_iff_of_pos_right hm]
    have : (a : ℝ) + 1 ≤ (c : ℕ) := by exact_mod_cast hac
    exact this
  have hxa0 : 1 / m ≤ xa := by
    rw [hxa, div_le_div_iff_of_pos_right hm]
    exact_mod_cast ha0
  have hxc1 : xc ≤ 1 := by
    rw [hxc, div_le_one hm]
    exact_mod_cast Nat.lt_succ_iff.mp c.isLt
  have hm1 : 0 < 1 / (m : ℝ) := by positivity
  -- the Jordan curve
  let seg : Path (D.point (path ⟨a, by omega⟩)) (D.point (path c)) :=
    (hSegPath xa xc).cast hpa hpc
  have hsegr : range seg = range (hSegPath xa xc) := rfl
  have hxac : xa ≤ xc := by linarith
  have hseginj : Function.Injective seg := hSegPath_injective (by linarith)
  have hsegU : range seg ⊆ unitSeg := by
    intro w hw
    rw [hsegr, mem_range_hSegPath hxac] at hw
    exact ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
  have hmeet : range seg ∩ range β = {D.point (path ⟨a, by omega⟩), D.point (path c)} := by
    apply Subset.antisymm
    · rintro z ⟨hzs, ⟨t, rfl⟩⟩
      rcases hβseg t (hsegU hzs) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro z (rfl | hz)
      · exact ⟨seg.source_mem_range, β.source_mem_range⟩
      · rw [mem_singleton_iff] at hz
        subst hz
        exact ⟨seg.target_mem_range, β.target_mem_range⟩
  have hJ := isJordanCurve_of_two_paths seg β hseginj hβ hmeet
  have hCtrace : range seg ∪ range β ⊆ drawingTrace D :=
    union_subset (hsegU.trans h.unitSeg_subset_trace) hβtrace
  have hUC : Disjoint U (range seg ∪ range β) := hU.disjoint.mono_right hCtrace
  -- the arc near the vertex lies above the line
  obtain ⟨τ₀, hτ₀, hτup⟩ := hβup
  set τ : ℝ := min τ₀ 1 with hτdef
  have hτ : 0 < τ := lt_min hτ₀ one_pos
  have hττ₀ : τ ≤ τ₀ := min_le_left _ _
  have hτ1 : τ ≤ 1 := min_le_right _ _
  set K : Set (ℝ × ℝ) := β '' {t : unitInterval | τ / 2 ≤ (t : ℝ)} with hK
  have hKc : IsCompact K :=
    (isClosed_le continuous_const continuous_subtype_val).isCompact.image β.continuous
  have hvaK : (xa, (0 : ℝ)) ∉ K := by
    rintro ⟨t, ht, hβt⟩
    have : t = 0 := hβ (hβt.trans (by rw [Path.source, hpa]))
    rw [this] at ht
    change τ / 2 ≤ 0 at ht
    linarith
  have h1K : (1 : unitInterval) ∈ {t : unitInterval | τ / 2 ≤ (t : ℝ)} := by
    change τ / 2 ≤ 1
    linarith
  have hd₁ : 0 < infDist (xa, (0 : ℝ)) K :=
    (hKc.isClosed.notMem_iff_infDist_pos ⟨β 1, mem_image_of_mem β h1K⟩).mp hvaK
  set ρ : ℝ := min (1 / m) (infDist (xa, (0 : ℝ)) K) with hρ
  have hρpos : 0 < ρ := lt_min hm1 hd₁
  have hρm : ρ ≤ 1 / m := min_le_left _ _
  have hρK : ρ ≤ infDist (xa, (0 : ℝ)) K := min_le_right _ _
  have hF1 : ∀ t : unitInterval, dist (β t) (xa, 0) < ρ → (t = 0 ∨ 0 < (β t).2) := by
    intro t ht
    by_cases htτ : τ / 2 ≤ (t : ℝ)
    · exfalso
      have := infDist_le_dist_of_mem (x := (xa, (0 : ℝ)))
        (mem_image_of_mem β (show t ∈ {t : unitInterval | τ / 2 ≤ (t : ℝ)} from htτ))
      rw [dist_comm] at this
      linarith
    · push Not at htτ
      rcases eq_or_lt_of_le t.2.1 with ht0 | ht0
      · exact Or.inl (Subtype.ext ht0.symm)
      · exact Or.inr (hτup t ht0 (by linarith))
  -- the straight point to the right
  set q : ℝ × ℝ := (xa + ρ / 2, 0) with hq
  have hqseg : q ∈ unitSeg :=
    ⟨rfl, show (0 : ℝ) ≤ xa + ρ / 2 by linarith, show xa + ρ / 2 ≤ 1 by linarith⟩
  have hqβ : q ∉ range β := by
    rintro ⟨t, ht⟩
    rcases hβseg t (ht ▸ hqseg) with h1 | h1
    · rw [ht, hpa] at h1
      have := congrArg Prod.fst h1
      simp only [hq] at this
      linarith
    · rw [ht, hpc] at h1
      have := congrArg Prod.fst h1
      simp only [hq] at this
      linarith
  have hd₂ : 0 < infDist q (range β) :=
    ((isCompact_range β.continuous).isClosed.notMem_iff_infDist_pos
      ⟨_, β.source_mem_range⟩).mp hqβ
  set r : ℝ := min (ρ / 2) (infDist q (range β)) with hr
  have hrpos : 0 < r := lt_min (by linarith) hd₂
  have hrρ : r ≤ ρ / 2 := min_le_left _ _
  have hrd : r ≤ infDist q (range β) := min_le_right _ _
  have hloc : ∀ w ∈ ball q r, w ∈ range seg ∪ range β ↔ w.2 = q.2 := by
    intro w hw
    have hw' : max (dist w.1 q.1) (dist w.2 q.2) < r := by
      have := mem_ball.mp hw
      rwa [Prod.dist_eq] at this
    have hw1 : |w.1 - q.1| < r := by
      have := lt_of_le_of_lt (le_max_left _ _) hw'
      rwa [Real.dist_eq] at this
    constructor
    · rintro (hws | hwβ)
      · rw [hsegr, mem_range_hSegPath hxac] at hws
        exact hws.1
      · exfalso
        have := infDist_le_dist_of_mem (x := q) hwβ
        rw [dist_comm] at this
        linarith [mem_ball.mp hw]
    · intro hw2
      left
      rw [hsegr, mem_range_hSegPath hxac]
      have h1 := (abs_lt.mp hw1)
      simp only [hq] at h1
      exact ⟨hw2, by linarith, by linarith⟩
  -- the axis piece to the left and the half-ball below
  set Λ : Set (ℝ × ℝ) := {w | w.2 = 0 ∧ xa - ρ < w.1 ∧ w.1 < xa} with hΛ
  set L : Set (ℝ × ℝ) := ball (xa, 0) ρ ∩ {w | w.2 < 0} with hL
  have hΛne : Λ.Nonempty := ⟨(xa - ρ / 2, 0), rfl, by linarith, by linarith⟩
  have hΛU : Λ ⊆ closure U := by
    rintro w ⟨hw2, hw0, hw1⟩
    exact h.axis_mem_closure hfront ⟨hw2, by linarith, by linarith⟩
  have hΛC : Disjoint Λ (range seg ∪ range β) := by
    rw [Set.disjoint_left]
    rintro w ⟨hw2, hw0, hw1⟩ (hws | ⟨t, rfl⟩)
    · rw [hsegr, mem_range_hSegPath hxac] at hws
      linarith [hws.2.1]
    · rcases hβseg t ⟨hw2, by linarith, by linarith⟩ with h1 | h1
      · rw [h1, hpa] at hw1
        exact lt_irrefl _ hw1
      · rw [h1, hpc] at hw1
        simp only at hw1
        linarith
  have hLc : IsPreconnected L :=
    ((convex_ball _ _).inter (convex_halfSpace_lt (LinearMap.snd ℝ ℝ ℝ).isLinear 0)).isPreconnected
  have hΛL : Λ ⊆ closure L := by
    rintro w ⟨hw2, hw0, hw1⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min ε ρ / 2 with hδ
    have hδpos : 0 < δ := by positivity
    refine ⟨(w.1, -δ), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt ?_ ?_
      · show |w.1 - xa| < ρ
        rw [abs_lt]
        constructor <;> linarith
      · show |-δ - 0| < ρ
        rw [sub_zero, abs_neg, abs_of_pos hδpos]
        have := min_le_right ε ρ
        linarith
    · show -δ < 0
      linarith
    · rw [Prod.dist_eq, dist_self]
      show max 0 |w.2 - -δ| < ε
      rw [hw2, zero_sub, neg_neg, abs_of_pos hδpos, max_eq_right hδpos.le]
      have := min_le_left ε ρ
      linarith
  have hLC : Disjoint L (range seg ∪ range β) := by
    rw [Set.disjoint_left]
    rintro w ⟨hwb, hw2⟩ (hws | ⟨t, rfl⟩)
    · rw [hsegr, mem_range_hSegPath hxac] at hws
      exact (ne_of_lt hw2) hws.1
    · rcases hF1 t (mem_ball.mp hwb) with h1 | h1
      · rw [h1, Path.source, hpa] at hw2
        exact lt_irrefl (0 : ℝ) hw2
      · exact lt_asymm h1 hw2
  -- the two sides at the straight point
  have hgq : 0 < gap D copies ⟨a, ham⟩ q.1 := by
    refine h.gap_pos _ ?_ ?_
    · show (a : ℝ) / m < xa + ρ / 2
      linarith
    · show xa + ρ / 2 < ((a : ℝ) + 1) / m
      have : ((a : ℝ) + 1) / m = xa + 1 / m := by rw [hxa]; ring
      linarith
  set y : ℝ := min (gap D copies ⟨a, ham⟩ q.1) r / 2 with hy
  have hy0 : 0 < y := by positivity
  have hyr : y < r := by have := min_le_right (gap D copies ⟨a, ham⟩ q.1) r; linarith
  have hyg : y < gap D copies ⟨a, ham⟩ q.1 := by
    have := min_le_left (gap D copies ⟨a, ham⟩ q.1) r; linarith
  have hup : (q.1, y) ∈ U := by
    refine hcol ⟨?_, ?_, hy0, hyg⟩
    · show (a : ℝ) / m < xa + ρ / 2
      linarith
    · show xa + ρ / 2 < ((a : ℝ) + 1) / m
      have : ((a : ℝ) + 1) / m = xa + 1 / m := by rw [hxa]; ring
      linarith
  have hball : ∀ z : ℝ, |z| < r → (q.1, z) ∈ ball q r := by
    intro z hz
    rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [hq, sub_zero]
    exact max_lt hrpos hz
  refine jordan_core_contradiction hJ hU.preconnected hUC hΛne hΛU hΛC hLc hΛL hLC hrpos hloc
    (Or.inl ⟨⟨(q.1, y), hup, hball y (by rw [abs_of_pos hy0]; exact hyr), hy0⟩,
      ⟨(q.1, -(r / 2)), ⟨?_, ?_⟩, hball _ ?_, ?_⟩⟩)
  · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [hq]
    refine max_lt ?_ ?_
    · rw [abs_of_pos (by linarith)]
      linarith
    · show |-(r / 2) - 0| < ρ
      rw [sub_zero, abs_neg, abs_of_pos (by linarith)]
      linarith
  · show -(r / 2) < 0
    linarith
  · rw [abs_neg, abs_of_pos (by linarith)]
    linarith
  · show -(r / 2) < (0 : ℝ)
    linarith

/-- An arc leaving an interior path vertex downwards towards a later path vertex
excludes the lower collar of the next path edge from the unbounded component. -/
theorem not_lowerCollar_of_down_right {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U)
    {a : ℕ} (ha0 : 0 < a) (ham : a < m) {c : Fin (m + 1)} (hac : a < (c : ℕ))
    (β : Path (D.point (path ⟨a, by omega⟩)) (D.point (path c))) (hβ : Function.Injective β)
    (hβtrace : range β ⊆ drawingTrace D)
    (hβseg : ∀ t, β t ∈ unitSeg → β t = D.point (path ⟨a, by omega⟩) ∨ β t = D.point (path c))
    (hβup : ∃ τ > 0, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < τ → (β t).2 < 0) :
    ¬ lowerCollar D copies ⟨a, ham⟩ ⊆ U := by
  intro hcol
  have hm := h.m_pos_real
  set xa : ℝ := (a : ℝ) / m with hxa
  set xc : ℝ := (c : ℝ) / m with hxc
  have hpa : D.point (path ⟨a, by omega⟩) = (xa, 0) := by rw [h.point]
  have hpc : D.point (path c) = (xc, 0) := by rw [h.point]
  have hac' : xa + 1 / m ≤ xc := by
    rw [hxa, hxc, ← add_div, div_le_div_iff_of_pos_right hm]
    have : (a : ℝ) + 1 ≤ (c : ℕ) := by exact_mod_cast hac
    exact this
  have hxa0 : 1 / m ≤ xa := by
    rw [hxa, div_le_div_iff_of_pos_right hm]
    exact_mod_cast ha0
  have hxc1 : xc ≤ 1 := by
    rw [hxc, div_le_one hm]
    exact_mod_cast Nat.lt_succ_iff.mp c.isLt
  have hm1 : 0 < 1 / (m : ℝ) := by positivity
  -- the Jordan curve
  let seg : Path (D.point (path ⟨a, by omega⟩)) (D.point (path c)) :=
    (hSegPath xa xc).cast hpa hpc
  have hsegr : range seg = range (hSegPath xa xc) := rfl
  have hxac : xa ≤ xc := by linarith
  have hseginj : Function.Injective seg := hSegPath_injective (by linarith)
  have hsegU : range seg ⊆ unitSeg := by
    intro w hw
    rw [hsegr, mem_range_hSegPath hxac] at hw
    exact ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
  have hmeet : range seg ∩ range β = {D.point (path ⟨a, by omega⟩), D.point (path c)} := by
    apply Subset.antisymm
    · rintro z ⟨hzs, ⟨t, rfl⟩⟩
      rcases hβseg t (hsegU hzs) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro z (rfl | hz)
      · exact ⟨seg.source_mem_range, β.source_mem_range⟩
      · rw [mem_singleton_iff] at hz
        subst hz
        exact ⟨seg.target_mem_range, β.target_mem_range⟩
  have hJ := isJordanCurve_of_two_paths seg β hseginj hβ hmeet
  have hCtrace : range seg ∪ range β ⊆ drawingTrace D :=
    union_subset (hsegU.trans h.unitSeg_subset_trace) hβtrace
  have hUC : Disjoint U (range seg ∪ range β) := hU.disjoint.mono_right hCtrace
  -- the arc near the vertex lies above the line
  obtain ⟨τ₀, hτ₀, hτup⟩ := hβup
  set τ : ℝ := min τ₀ 1 with hτdef
  have hτ : 0 < τ := lt_min hτ₀ one_pos
  have hττ₀ : τ ≤ τ₀ := min_le_left _ _
  have hτ1 : τ ≤ 1 := min_le_right _ _
  set K : Set (ℝ × ℝ) := β '' {t : unitInterval | τ / 2 ≤ (t : ℝ)} with hK
  have hKc : IsCompact K :=
    (isClosed_le continuous_const continuous_subtype_val).isCompact.image β.continuous
  have hvaK : (xa, (0 : ℝ)) ∉ K := by
    rintro ⟨t, ht, hβt⟩
    have : t = 0 := hβ (hβt.trans (by rw [Path.source, hpa]))
    rw [this] at ht
    change τ / 2 ≤ 0 at ht
    linarith
  have h1K : (1 : unitInterval) ∈ {t : unitInterval | τ / 2 ≤ (t : ℝ)} := by
    change τ / 2 ≤ 1
    linarith
  have hd₁ : 0 < infDist (xa, (0 : ℝ)) K :=
    (hKc.isClosed.notMem_iff_infDist_pos ⟨β 1, mem_image_of_mem β h1K⟩).mp hvaK
  set ρ : ℝ := min (1 / m) (infDist (xa, (0 : ℝ)) K) with hρ
  have hρpos : 0 < ρ := lt_min hm1 hd₁
  have hρm : ρ ≤ 1 / m := min_le_left _ _
  have hρK : ρ ≤ infDist (xa, (0 : ℝ)) K := min_le_right _ _
  have hF1 : ∀ t : unitInterval, dist (β t) (xa, 0) < ρ → (t = 0 ∨ (β t).2 < 0) := by
    intro t ht
    by_cases htτ : τ / 2 ≤ (t : ℝ)
    · exfalso
      have := infDist_le_dist_of_mem (x := (xa, (0 : ℝ)))
        (mem_image_of_mem β (show t ∈ {t : unitInterval | τ / 2 ≤ (t : ℝ)} from htτ))
      rw [dist_comm] at this
      linarith
    · push Not at htτ
      rcases eq_or_lt_of_le t.2.1 with ht0 | ht0
      · exact Or.inl (Subtype.ext ht0.symm)
      · exact Or.inr (hτup t ht0 (by linarith))
  -- the straight point to the right
  set q : ℝ × ℝ := (xa + ρ / 2, 0) with hq
  have hqseg : q ∈ unitSeg :=
    ⟨rfl, show (0 : ℝ) ≤ xa + ρ / 2 by linarith, show xa + ρ / 2 ≤ 1 by linarith⟩
  have hqβ : q ∉ range β := by
    rintro ⟨t, ht⟩
    rcases hβseg t (ht ▸ hqseg) with h1 | h1
    · rw [ht, hpa] at h1
      have := congrArg Prod.fst h1
      simp only [hq] at this
      linarith
    · rw [ht, hpc] at h1
      have := congrArg Prod.fst h1
      simp only [hq] at this
      linarith
  have hd₂ : 0 < infDist q (range β) :=
    ((isCompact_range β.continuous).isClosed.notMem_iff_infDist_pos
      ⟨_, β.source_mem_range⟩).mp hqβ
  set r : ℝ := min (ρ / 2) (infDist q (range β)) with hr
  have hrpos : 0 < r := lt_min (by linarith) hd₂
  have hrρ : r ≤ ρ / 2 := min_le_left _ _
  have hrd : r ≤ infDist q (range β) := min_le_right _ _
  have hloc : ∀ w ∈ ball q r, w ∈ range seg ∪ range β ↔ w.2 = q.2 := by
    intro w hw
    have hw' : max (dist w.1 q.1) (dist w.2 q.2) < r := by
      have := mem_ball.mp hw
      rwa [Prod.dist_eq] at this
    have hw1 : |w.1 - q.1| < r := by
      have := lt_of_le_of_lt (le_max_left _ _) hw'
      rwa [Real.dist_eq] at this
    constructor
    · rintro (hws | hwβ)
      · rw [hsegr, mem_range_hSegPath hxac] at hws
        exact hws.1
      · exfalso
        have := infDist_le_dist_of_mem (x := q) hwβ
        rw [dist_comm] at this
        linarith [mem_ball.mp hw]
    · intro hw2
      left
      rw [hsegr, mem_range_hSegPath hxac]
      have h1 := (abs_lt.mp hw1)
      simp only [hq] at h1
      exact ⟨hw2, by linarith, by linarith⟩
  -- the axis piece to the left and the half-ball below
  set Λ : Set (ℝ × ℝ) := {w | w.2 = 0 ∧ xa - ρ < w.1 ∧ w.1 < xa} with hΛ
  set L : Set (ℝ × ℝ) := ball (xa, 0) ρ ∩ {w | 0 < w.2} with hL
  have hΛne : Λ.Nonempty := ⟨(xa - ρ / 2, 0), rfl, by linarith, by linarith⟩
  have hΛU : Λ ⊆ closure U := by
    rintro w ⟨hw2, hw0, hw1⟩
    exact h.axis_mem_closure hfront ⟨hw2, by linarith, by linarith⟩
  have hΛC : Disjoint Λ (range seg ∪ range β) := by
    rw [Set.disjoint_left]
    rintro w ⟨hw2, hw0, hw1⟩ (hws | ⟨t, rfl⟩)
    · rw [hsegr, mem_range_hSegPath hxac] at hws
      linarith [hws.2.1]
    · rcases hβseg t ⟨hw2, by linarith, by linarith⟩ with h1 | h1
      · rw [h1, hpa] at hw1
        exact lt_irrefl _ hw1
      · rw [h1, hpc] at hw1
        simp only at hw1
        linarith
  have hLc : IsPreconnected L :=
    ((convex_ball _ _).inter (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear 0)).isPreconnected
  have hΛL : Λ ⊆ closure L := by
    rintro w ⟨hw2, hw0, hw1⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min ε ρ / 2 with hδ
    have hδpos : 0 < δ := by positivity
    refine ⟨(w.1, δ), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt ?_ ?_
      · show |w.1 - xa| < ρ
        rw [abs_lt]
        constructor <;> linarith
      · show |δ - 0| < ρ
        rw [sub_zero, abs_of_pos hδpos]
        have := min_le_right ε ρ
        linarith
    · show 0 < δ
      linarith
    · rw [Prod.dist_eq, dist_self]
      show max 0 |w.2 - δ| < ε
      rw [hw2, zero_sub, abs_neg, abs_of_pos hδpos, max_eq_right hδpos.le]
      have := min_le_left ε ρ
      linarith
  have hLC : Disjoint L (range seg ∪ range β) := by
    rw [Set.disjoint_left]
    rintro w ⟨hwb, hw2⟩ (hws | ⟨t, rfl⟩)
    · rw [hsegr, mem_range_hSegPath hxac] at hws
      exact (ne_of_gt hw2) hws.1
    · rcases hF1 t (mem_ball.mp hwb) with h1 | h1
      · rw [h1, Path.source, hpa] at hw2
        exact lt_irrefl (0 : ℝ) hw2
      · exact lt_asymm h1 hw2
  -- the two sides at the straight point
  have hgq : 0 < gap D copies ⟨a, ham⟩ q.1 := by
    refine h.gap_pos _ ?_ ?_
    · show (a : ℝ) / m < xa + ρ / 2
      linarith
    · show xa + ρ / 2 < ((a : ℝ) + 1) / m
      have : ((a : ℝ) + 1) / m = xa + 1 / m := by rw [hxa]; ring
      linarith
  set y : ℝ := min (gap D copies ⟨a, ham⟩ q.1) r / 2 with hy
  have hy0 : 0 < y := by positivity
  have hyr : y < r := by have := min_le_right (gap D copies ⟨a, ham⟩ q.1) r; linarith
  have hyg : y < gap D copies ⟨a, ham⟩ q.1 := by
    have := min_le_left (gap D copies ⟨a, ham⟩ q.1) r; linarith
  have hup : (q.1, -y) ∈ U := by
    refine hcol ⟨?_, ?_, by linarith, by linarith⟩
    · show (a : ℝ) / m < xa + ρ / 2
      linarith
    · show xa + ρ / 2 < ((a : ℝ) + 1) / m
      have : ((a : ℝ) + 1) / m = xa + 1 / m := by rw [hxa]; ring
      linarith
  have hball : ∀ z : ℝ, |z| < r → (q.1, z) ∈ ball q r := by
    intro z hz
    rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [hq, sub_zero]
    exact max_lt hrpos hz
  refine jordan_core_contradiction hJ hU.preconnected hUC hΛne hΛU hΛC hLc hΛL hLC hrpos hloc
    (Or.inr ⟨⟨(q.1, -y), hup, hball (-y) (by rw [abs_neg, abs_of_pos hy0]; exact hyr),
        show -y < (0 : ℝ) by linarith⟩,
      ⟨(q.1, r / 2), ⟨?_, ?_⟩, hball _ ?_, ?_⟩⟩)
  · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [hq]
    refine max_lt ?_ ?_
    · rw [abs_of_pos (by linarith)]
      linarith
    · show |r / 2 - 0| < ρ
      rw [sub_zero, abs_of_pos (by linarith)]
      linarith
  · show 0 < r / 2
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith
  · show (0 : ℝ) < r / 2
    linarith

/-- An arc leaving an interior path vertex upwards towards an earlier path vertex
excludes the upper collar of the previous path edge from the unbounded component. -/
theorem not_upperCollar_of_up_left {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U)
    {a : ℕ} (ha0 : 0 < a) (ham : a < m) {c : Fin (m + 1)} (hca : (c : ℕ) < a)
    (β : Path (D.point (path ⟨a, by omega⟩)) (D.point (path c))) (hβ : Function.Injective β)
    (hβtrace : range β ⊆ drawingTrace D)
    (hβseg : ∀ t, β t ∈ unitSeg → β t = D.point (path ⟨a, by omega⟩) ∨ β t = D.point (path c))
    (hβup : ∃ τ > 0, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < τ → 0 < (β t).2) :
    ¬ upperCollar D copies ⟨a - 1, by omega⟩ ⊆ U := by
  intro hcol
  have hm := h.m_pos_real
  set xa : ℝ := (a : ℝ) / m with hxa
  set xc : ℝ := (c : ℝ) / m with hxc
  have hpa : D.point (path ⟨a, by omega⟩) = (xa, 0) := by rw [h.point]
  have hpc : D.point (path c) = (xc, 0) := by rw [h.point]
  have hac' : xc + 1 / m ≤ xa := by
    rw [hxa, hxc, ← add_div, div_le_div_iff_of_pos_right hm]
    have : ((c : ℕ) : ℝ) + 1 ≤ a := by exact_mod_cast hca
    exact this
  have hxa0 : 1 / m ≤ xa := by
    rw [hxa, div_le_div_iff_of_pos_right hm]
    exact_mod_cast ha0
  have hxa1 : xa + 1 / m ≤ 1 := by
    rw [hxa, ← add_div, div_le_one hm]
    have : (a : ℝ) + 1 ≤ m := by exact_mod_cast ham
    exact this
  have hxc0 : 0 ≤ xc := div_nonneg (Nat.cast_nonneg _) hm.le
  have hm1 : 0 < 1 / (m : ℝ) := by positivity
  -- the Jordan curve
  let seg : Path (D.point (path ⟨a, by omega⟩)) (D.point (path c)) :=
    ((hSegPath xc xa).symm).cast hpa hpc
  have hsegr : range seg = range (hSegPath xc xa) := by
    change range ((hSegPath xc xa).symm) = _
    rw [Path.symm_range]
  have hxac : xc ≤ xa := by linarith
  have hseginj : Function.Injective seg := by
    intro s t hst
    have := hSegPath_injective (show xc ≠ xa by linarith) hst
    exact unitInterval.symm_involutive.injective this
  have hsegU : range seg ⊆ unitSeg := by
    intro w hw
    rw [hsegr, mem_range_hSegPath hxac] at hw
    exact ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
  have hmeet : range seg ∩ range β = {D.point (path ⟨a, by omega⟩), D.point (path c)} := by
    apply Subset.antisymm
    · rintro z ⟨hzs, ⟨t, rfl⟩⟩
      rcases hβseg t (hsegU hzs) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro z (rfl | hz)
      · exact ⟨seg.source_mem_range, β.source_mem_range⟩
      · rw [mem_singleton_iff] at hz
        subst hz
        exact ⟨seg.target_mem_range, β.target_mem_range⟩
  have hJ := isJordanCurve_of_two_paths seg β hseginj hβ hmeet
  have hCtrace : range seg ∪ range β ⊆ drawingTrace D :=
    union_subset (hsegU.trans h.unitSeg_subset_trace) hβtrace
  have hUC : Disjoint U (range seg ∪ range β) := hU.disjoint.mono_right hCtrace
  -- the arc near the vertex lies above the line
  obtain ⟨τ₀, hτ₀, hτup⟩ := hβup
  set τ : ℝ := min τ₀ 1 with hτdef
  have hτ : 0 < τ := lt_min hτ₀ one_pos
  have hττ₀ : τ ≤ τ₀ := min_le_left _ _
  have hτ1 : τ ≤ 1 := min_le_right _ _
  set K : Set (ℝ × ℝ) := β '' {t : unitInterval | τ / 2 ≤ (t : ℝ)} with hK
  have hKc : IsCompact K :=
    (isClosed_le continuous_const continuous_subtype_val).isCompact.image β.continuous
  have hvaK : (xa, (0 : ℝ)) ∉ K := by
    rintro ⟨t, ht, hβt⟩
    have : t = 0 := hβ (hβt.trans (by rw [Path.source, hpa]))
    rw [this] at ht
    change τ / 2 ≤ 0 at ht
    linarith
  have h1K : (1 : unitInterval) ∈ {t : unitInterval | τ / 2 ≤ (t : ℝ)} := by
    change τ / 2 ≤ 1
    linarith
  have hd₁ : 0 < infDist (xa, (0 : ℝ)) K :=
    (hKc.isClosed.notMem_iff_infDist_pos ⟨β 1, mem_image_of_mem β h1K⟩).mp hvaK
  set ρ : ℝ := min (1 / m) (infDist (xa, (0 : ℝ)) K) with hρ
  have hρpos : 0 < ρ := lt_min hm1 hd₁
  have hρm : ρ ≤ 1 / m := min_le_left _ _
  have hρK : ρ ≤ infDist (xa, (0 : ℝ)) K := min_le_right _ _
  have hF1 : ∀ t : unitInterval, dist (β t) (xa, 0) < ρ → (t = 0 ∨ 0 < (β t).2) := by
    intro t ht
    by_cases htτ : τ / 2 ≤ (t : ℝ)
    · exfalso
      have := infDist_le_dist_of_mem (x := (xa, (0 : ℝ)))
        (mem_image_of_mem β (show t ∈ {t : unitInterval | τ / 2 ≤ (t : ℝ)} from htτ))
      rw [dist_comm] at this
      linarith
    · push Not at htτ
      rcases eq_or_lt_of_le t.2.1 with ht0 | ht0
      · exact Or.inl (Subtype.ext ht0.symm)
      · exact Or.inr (hτup t ht0 (by linarith))
  -- the straight point to the left
  set q : ℝ × ℝ := (xa - ρ / 2, 0) with hq
  have hqseg : q ∈ unitSeg :=
    ⟨rfl, show (0 : ℝ) ≤ xa - ρ / 2 by linarith, show xa - ρ / 2 ≤ 1 by linarith⟩
  have hqβ : q ∉ range β := by
    rintro ⟨t, ht⟩
    rcases hβseg t (ht ▸ hqseg) with h1 | h1
    · rw [ht, hpa] at h1
      have := congrArg Prod.fst h1
      simp only [hq] at this
      linarith
    · rw [ht, hpc] at h1
      have := congrArg Prod.fst h1
      simp only [hq] at this
      linarith
  have hd₂ : 0 < infDist q (range β) :=
    ((isCompact_range β.continuous).isClosed.notMem_iff_infDist_pos
      ⟨_, β.source_mem_range⟩).mp hqβ
  set r : ℝ := min (ρ / 2) (infDist q (range β)) with hr
  have hrpos : 0 < r := lt_min (by linarith) hd₂
  have hrρ : r ≤ ρ / 2 := min_le_left _ _
  have hrd : r ≤ infDist q (range β) := min_le_right _ _
  have hloc : ∀ w ∈ ball q r, w ∈ range seg ∪ range β ↔ w.2 = q.2 := by
    intro w hw
    have hw' : max (dist w.1 q.1) (dist w.2 q.2) < r := by
      have := mem_ball.mp hw
      rwa [Prod.dist_eq] at this
    have hw1 : |w.1 - q.1| < r := by
      have := lt_of_le_of_lt (le_max_left _ _) hw'
      rwa [Real.dist_eq] at this
    constructor
    · rintro (hws | hwβ)
      · rw [hsegr, mem_range_hSegPath hxac] at hws
        exact hws.1
      · exfalso
        have := infDist_le_dist_of_mem (x := q) hwβ
        rw [dist_comm] at this
        linarith [mem_ball.mp hw]
    · intro hw2
      left
      rw [hsegr, mem_range_hSegPath hxac]
      have h1 := (abs_lt.mp hw1)
      simp only [hq] at h1
      exact ⟨hw2, by linarith, by linarith⟩
  -- the axis piece to the right and the half-ball on the other side
  set Λ : Set (ℝ × ℝ) := {w | w.2 = 0 ∧ xa < w.1 ∧ w.1 < xa + ρ} with hΛ
  set L : Set (ℝ × ℝ) := ball (xa, 0) ρ ∩ {w | w.2 < 0} with hL
  have hΛne : Λ.Nonempty := ⟨(xa + ρ / 2, 0), rfl, by linarith, by linarith⟩
  have hΛU : Λ ⊆ closure U := by
    rintro w ⟨hw2, hw0, hw1⟩
    exact h.axis_mem_closure hfront ⟨hw2, by linarith, by linarith⟩
  have hΛC : Disjoint Λ (range seg ∪ range β) := by
    rw [Set.disjoint_left]
    rintro w ⟨hw2, hw0, hw1⟩ (hws | ⟨t, rfl⟩)
    · rw [hsegr, mem_range_hSegPath hxac] at hws
      linarith [hws.2.2]
    · rcases hβseg t ⟨hw2, by linarith, by linarith⟩ with h1 | h1
      · rw [h1, hpa] at hw0
        exact lt_irrefl _ hw0
      · rw [h1, hpc] at hw0
        simp only at hw0
        linarith
  have hLc : IsPreconnected L :=
    ((convex_ball _ _).inter (convex_halfSpace_lt (LinearMap.snd ℝ ℝ ℝ).isLinear 0)).isPreconnected
  have hΛL : Λ ⊆ closure L := by
    rintro w ⟨hw2, hw0, hw1⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min ε ρ / 2 with hδ
    have hδpos : 0 < δ := by positivity
    refine ⟨(w.1, -δ), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt ?_ ?_
      · show |w.1 - xa| < ρ
        rw [abs_lt]
        constructor <;> linarith
      · show |-δ - 0| < ρ
        rw [sub_zero, abs_neg, abs_of_pos hδpos]
        have := min_le_right ε ρ
        linarith
    · show -δ < 0
      linarith
    · rw [Prod.dist_eq, dist_self]
      show max 0 |w.2 - -δ| < ε
      rw [hw2, zero_sub, neg_neg, abs_of_pos hδpos, max_eq_right hδpos.le]
      have := min_le_left ε ρ
      linarith
  have hLC : Disjoint L (range seg ∪ range β) := by
    rw [Set.disjoint_left]
    rintro w ⟨hwb, hw2⟩ (hws | ⟨t, rfl⟩)
    · rw [hsegr, mem_range_hSegPath hxac] at hws
      exact (ne_of_lt hw2) hws.1
    · rcases hF1 t (mem_ball.mp hwb) with h1 | h1
      · rw [h1, Path.source, hpa] at hw2
        exact lt_irrefl (0 : ℝ) hw2
      · exact lt_asymm h1 hw2
  -- the two sides at the straight point
  have hq0 : (((⟨a - 1, by omega⟩ : Fin m) : ℕ) : ℝ) / m < q.1 := by
    show ((a - 1 : ℕ) : ℝ) / m < xa - ρ / 2
    rw [cast_pred ha0]
    have : ((a : ℝ) - 1) / m = xa - 1 / m := by rw [hxa]; ring
    linarith
  have hq1 : q.1 < ((((⟨a - 1, by omega⟩ : Fin m) : ℕ) : ℝ) + 1) / m := by
    show xa - ρ / 2 < (((a - 1 : ℕ) : ℝ) + 1) / m
    rw [cast_pred ha0, sub_add_cancel]
    linarith
  have hgq : 0 < gap D copies ⟨a - 1, by omega⟩ q.1 := h.gap_pos _ hq0 hq1
  set y : ℝ := min (gap D copies ⟨a - 1, by omega⟩ q.1) r / 2 with hy
  have hy0 : 0 < y := by positivity
  have hyr : y < r := by have := min_le_right (gap D copies ⟨a - 1, by omega⟩ q.1) r; linarith
  have hyg : y < gap D copies ⟨a - 1, by omega⟩ q.1 := by
    have := min_le_left (gap D copies ⟨a - 1, by omega⟩ q.1) r; linarith
  have hup : (q.1, y) ∈ U := by
    exact hcol ⟨hq0, hq1, hy0, hyg⟩
  have hball : ∀ z : ℝ, |z| < r → (q.1, z) ∈ ball q r := by
    intro z hz
    rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [hq, sub_zero]
    exact max_lt hrpos hz
  refine jordan_core_contradiction hJ hU.preconnected hUC hΛne hΛU hΛC hLc hΛL hLC hrpos hloc
    (Or.inl ⟨⟨(q.1, y), hup, hball y (by rw [abs_of_pos hy0]; exact hyr), hy0⟩,
      ⟨(q.1, -(r / 2)), ⟨?_, ?_⟩, hball _ ?_, ?_⟩⟩)
  · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [hq]
    refine max_lt ?_ ?_
    · rw [abs_of_neg (by linarith)]
      linarith
    · show |-(r / 2) - 0| < ρ
      rw [sub_zero, abs_neg, abs_of_pos (by linarith)]
      linarith
  · show -(r / 2) < 0
    linarith
  · rw [abs_neg, abs_of_pos (by linarith)]
    linarith
  · show -(r / 2) < (0 : ℝ)
    linarith
/-- An arc leaving an interior path vertex downwards towards an earlier path vertex
excludes the lower collar of the previous path edge from the unbounded component. -/
theorem not_lowerCollar_of_down_left {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U)
    {a : ℕ} (ha0 : 0 < a) (ham : a < m) {c : Fin (m + 1)} (hca : (c : ℕ) < a)
    (β : Path (D.point (path ⟨a, by omega⟩)) (D.point (path c))) (hβ : Function.Injective β)
    (hβtrace : range β ⊆ drawingTrace D)
    (hβseg : ∀ t, β t ∈ unitSeg → β t = D.point (path ⟨a, by omega⟩) ∨ β t = D.point (path c))
    (hβup : ∃ τ > 0, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < τ → (β t).2 < 0) :
    ¬ lowerCollar D copies ⟨a - 1, by omega⟩ ⊆ U := by
  intro hcol
  have hm := h.m_pos_real
  set xa : ℝ := (a : ℝ) / m with hxa
  set xc : ℝ := (c : ℝ) / m with hxc
  have hpa : D.point (path ⟨a, by omega⟩) = (xa, 0) := by rw [h.point]
  have hpc : D.point (path c) = (xc, 0) := by rw [h.point]
  have hac' : xc + 1 / m ≤ xa := by
    rw [hxa, hxc, ← add_div, div_le_div_iff_of_pos_right hm]
    have : ((c : ℕ) : ℝ) + 1 ≤ a := by exact_mod_cast hca
    exact this
  have hxa0 : 1 / m ≤ xa := by
    rw [hxa, div_le_div_iff_of_pos_right hm]
    exact_mod_cast ha0
  have hxa1 : xa + 1 / m ≤ 1 := by
    rw [hxa, ← add_div, div_le_one hm]
    have : (a : ℝ) + 1 ≤ m := by exact_mod_cast ham
    exact this
  have hxc0 : 0 ≤ xc := div_nonneg (Nat.cast_nonneg _) hm.le
  have hm1 : 0 < 1 / (m : ℝ) := by positivity
  -- the Jordan curve
  let seg : Path (D.point (path ⟨a, by omega⟩)) (D.point (path c)) :=
    ((hSegPath xc xa).symm).cast hpa hpc
  have hsegr : range seg = range (hSegPath xc xa) := by
    change range ((hSegPath xc xa).symm) = _
    rw [Path.symm_range]
  have hxac : xc ≤ xa := by linarith
  have hseginj : Function.Injective seg := by
    intro s t hst
    have := hSegPath_injective (show xc ≠ xa by linarith) hst
    exact unitInterval.symm_involutive.injective this
  have hsegU : range seg ⊆ unitSeg := by
    intro w hw
    rw [hsegr, mem_range_hSegPath hxac] at hw
    exact ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
  have hmeet : range seg ∩ range β = {D.point (path ⟨a, by omega⟩), D.point (path c)} := by
    apply Subset.antisymm
    · rintro z ⟨hzs, ⟨t, rfl⟩⟩
      rcases hβseg t (hsegU hzs) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro z (rfl | hz)
      · exact ⟨seg.source_mem_range, β.source_mem_range⟩
      · rw [mem_singleton_iff] at hz
        subst hz
        exact ⟨seg.target_mem_range, β.target_mem_range⟩
  have hJ := isJordanCurve_of_two_paths seg β hseginj hβ hmeet
  have hCtrace : range seg ∪ range β ⊆ drawingTrace D :=
    union_subset (hsegU.trans h.unitSeg_subset_trace) hβtrace
  have hUC : Disjoint U (range seg ∪ range β) := hU.disjoint.mono_right hCtrace
  -- the arc near the vertex lies above the line
  obtain ⟨τ₀, hτ₀, hτup⟩ := hβup
  set τ : ℝ := min τ₀ 1 with hτdef
  have hτ : 0 < τ := lt_min hτ₀ one_pos
  have hττ₀ : τ ≤ τ₀ := min_le_left _ _
  have hτ1 : τ ≤ 1 := min_le_right _ _
  set K : Set (ℝ × ℝ) := β '' {t : unitInterval | τ / 2 ≤ (t : ℝ)} with hK
  have hKc : IsCompact K :=
    (isClosed_le continuous_const continuous_subtype_val).isCompact.image β.continuous
  have hvaK : (xa, (0 : ℝ)) ∉ K := by
    rintro ⟨t, ht, hβt⟩
    have : t = 0 := hβ (hβt.trans (by rw [Path.source, hpa]))
    rw [this] at ht
    change τ / 2 ≤ 0 at ht
    linarith
  have h1K : (1 : unitInterval) ∈ {t : unitInterval | τ / 2 ≤ (t : ℝ)} := by
    change τ / 2 ≤ 1
    linarith
  have hd₁ : 0 < infDist (xa, (0 : ℝ)) K :=
    (hKc.isClosed.notMem_iff_infDist_pos ⟨β 1, mem_image_of_mem β h1K⟩).mp hvaK
  set ρ : ℝ := min (1 / m) (infDist (xa, (0 : ℝ)) K) with hρ
  have hρpos : 0 < ρ := lt_min hm1 hd₁
  have hρm : ρ ≤ 1 / m := min_le_left _ _
  have hρK : ρ ≤ infDist (xa, (0 : ℝ)) K := min_le_right _ _
  have hF1 : ∀ t : unitInterval, dist (β t) (xa, 0) < ρ → (t = 0 ∨ (β t).2 < 0) := by
    intro t ht
    by_cases htτ : τ / 2 ≤ (t : ℝ)
    · exfalso
      have := infDist_le_dist_of_mem (x := (xa, (0 : ℝ)))
        (mem_image_of_mem β (show t ∈ {t : unitInterval | τ / 2 ≤ (t : ℝ)} from htτ))
      rw [dist_comm] at this
      linarith
    · push Not at htτ
      rcases eq_or_lt_of_le t.2.1 with ht0 | ht0
      · exact Or.inl (Subtype.ext ht0.symm)
      · exact Or.inr (hτup t ht0 (by linarith))
  -- the straight point to the left
  set q : ℝ × ℝ := (xa - ρ / 2, 0) with hq
  have hqseg : q ∈ unitSeg :=
    ⟨rfl, show (0 : ℝ) ≤ xa - ρ / 2 by linarith, show xa - ρ / 2 ≤ 1 by linarith⟩
  have hqβ : q ∉ range β := by
    rintro ⟨t, ht⟩
    rcases hβseg t (ht ▸ hqseg) with h1 | h1
    · rw [ht, hpa] at h1
      have := congrArg Prod.fst h1
      simp only [hq] at this
      linarith
    · rw [ht, hpc] at h1
      have := congrArg Prod.fst h1
      simp only [hq] at this
      linarith
  have hd₂ : 0 < infDist q (range β) :=
    ((isCompact_range β.continuous).isClosed.notMem_iff_infDist_pos
      ⟨_, β.source_mem_range⟩).mp hqβ
  set r : ℝ := min (ρ / 2) (infDist q (range β)) with hr
  have hrpos : 0 < r := lt_min (by linarith) hd₂
  have hrρ : r ≤ ρ / 2 := min_le_left _ _
  have hrd : r ≤ infDist q (range β) := min_le_right _ _
  have hloc : ∀ w ∈ ball q r, w ∈ range seg ∪ range β ↔ w.2 = q.2 := by
    intro w hw
    have hw' : max (dist w.1 q.1) (dist w.2 q.2) < r := by
      have := mem_ball.mp hw
      rwa [Prod.dist_eq] at this
    have hw1 : |w.1 - q.1| < r := by
      have := lt_of_le_of_lt (le_max_left _ _) hw'
      rwa [Real.dist_eq] at this
    constructor
    · rintro (hws | hwβ)
      · rw [hsegr, mem_range_hSegPath hxac] at hws
        exact hws.1
      · exfalso
        have := infDist_le_dist_of_mem (x := q) hwβ
        rw [dist_comm] at this
        linarith [mem_ball.mp hw]
    · intro hw2
      left
      rw [hsegr, mem_range_hSegPath hxac]
      have h1 := (abs_lt.mp hw1)
      simp only [hq] at h1
      exact ⟨hw2, by linarith, by linarith⟩
  -- the axis piece to the right and the half-ball on the other side
  set Λ : Set (ℝ × ℝ) := {w | w.2 = 0 ∧ xa < w.1 ∧ w.1 < xa + ρ} with hΛ
  set L : Set (ℝ × ℝ) := ball (xa, 0) ρ ∩ {w | 0 < w.2} with hL
  have hΛne : Λ.Nonempty := ⟨(xa + ρ / 2, 0), rfl, by linarith, by linarith⟩
  have hΛU : Λ ⊆ closure U := by
    rintro w ⟨hw2, hw0, hw1⟩
    exact h.axis_mem_closure hfront ⟨hw2, by linarith, by linarith⟩
  have hΛC : Disjoint Λ (range seg ∪ range β) := by
    rw [Set.disjoint_left]
    rintro w ⟨hw2, hw0, hw1⟩ (hws | ⟨t, rfl⟩)
    · rw [hsegr, mem_range_hSegPath hxac] at hws
      linarith [hws.2.2]
    · rcases hβseg t ⟨hw2, by linarith, by linarith⟩ with h1 | h1
      · rw [h1, hpa] at hw0
        exact lt_irrefl _ hw0
      · rw [h1, hpc] at hw0
        simp only at hw0
        linarith
  have hLc : IsPreconnected L :=
    ((convex_ball _ _).inter (convex_halfSpace_gt (LinearMap.snd ℝ ℝ ℝ).isLinear 0)).isPreconnected
  have hΛL : Λ ⊆ closure L := by
    rintro w ⟨hw2, hw0, hw1⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min ε ρ / 2 with hδ
    have hδpos : 0 < δ := by positivity
    refine ⟨(w.1, δ), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt ?_ ?_
      · show |w.1 - xa| < ρ
        rw [abs_lt]
        constructor <;> linarith
      · show |δ - 0| < ρ
        rw [sub_zero, abs_of_pos hδpos]
        have := min_le_right ε ρ
        linarith
    · show 0 < δ
      linarith
    · rw [Prod.dist_eq, dist_self]
      show max 0 |w.2 - δ| < ε
      rw [hw2, zero_sub, abs_neg, abs_of_pos hδpos, max_eq_right hδpos.le]
      have := min_le_left ε ρ
      linarith
  have hLC : Disjoint L (range seg ∪ range β) := by
    rw [Set.disjoint_left]
    rintro w ⟨hwb, hw2⟩ (hws | ⟨t, rfl⟩)
    · rw [hsegr, mem_range_hSegPath hxac] at hws
      exact (ne_of_gt hw2) hws.1
    · rcases hF1 t (mem_ball.mp hwb) with h1 | h1
      · rw [h1, Path.source, hpa] at hw2
        exact lt_irrefl (0 : ℝ) hw2
      · exact lt_asymm h1 hw2
  -- the two sides at the straight point
  have hq0 : (((⟨a - 1, by omega⟩ : Fin m) : ℕ) : ℝ) / m < q.1 := by
    show ((a - 1 : ℕ) : ℝ) / m < xa - ρ / 2
    rw [cast_pred ha0]
    have : ((a : ℝ) - 1) / m = xa - 1 / m := by rw [hxa]; ring
    linarith
  have hq1 : q.1 < ((((⟨a - 1, by omega⟩ : Fin m) : ℕ) : ℝ) + 1) / m := by
    show xa - ρ / 2 < (((a - 1 : ℕ) : ℝ) + 1) / m
    rw [cast_pred ha0, sub_add_cancel]
    linarith
  have hgq : 0 < gap D copies ⟨a - 1, by omega⟩ q.1 := h.gap_pos _ hq0 hq1
  set y : ℝ := min (gap D copies ⟨a - 1, by omega⟩ q.1) r / 2 with hy
  have hy0 : 0 < y := by positivity
  have hyr : y < r := by have := min_le_right (gap D copies ⟨a - 1, by omega⟩ q.1) r; linarith
  have hyg : y < gap D copies ⟨a - 1, by omega⟩ q.1 := by
    have := min_le_left (gap D copies ⟨a - 1, by omega⟩ q.1) r; linarith
  have hup : (q.1, -y) ∈ U := by
    exact hcol ⟨hq0, hq1, by linarith, by linarith⟩
  have hball : ∀ z : ℝ, |z| < r → (q.1, z) ∈ ball q r := by
    intro z hz
    rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [hq, sub_zero]
    exact max_lt hrpos hz
  refine jordan_core_contradiction hJ hU.preconnected hUC hΛne hΛU hΛC hLc hΛL hLC hrpos hloc
    (Or.inr ⟨⟨(q.1, -y), hup, hball (-y) (by rw [abs_neg, abs_of_pos hy0]; exact hyr),
        show -y < (0 : ℝ) by linarith⟩,
      ⟨(q.1, r / 2), ⟨?_, ?_⟩, hball _ ?_, ?_⟩⟩)
  · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [hq]
    refine max_lt ?_ ?_
    · rw [abs_of_neg (by linarith)]
      linarith
    · show |r / 2 - 0| < ρ
      rw [sub_zero, abs_of_pos (by linarith)]
      linarith
  · show 0 < r / 2
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith
  · show (0 : ℝ) < r / 2
    linarith

end StraightPath

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
