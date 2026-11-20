import FiniteAvalanches.Support.Plane.OuterRedrawing.OneSideMain
import FiniteAvalanches.Support.Plane.OuterRedrawing.PartialDrawing
import FiniteAvalanches.Support.Plane.OuterRedrawing.SquareBoundary

/-!
# A free collar above a stretch of the straight path

When all selected off-path edges leave the interior vertices of a stretch from
below, no point of the selected drawing above the horizontal line accumulates
at an interior point of the stretch. The distance to such points therefore gives
an open collar above the stretch, free of the selected drawing, whose upper
boundary is an arc from one end of the stretch to the other. The stretch and
this arc form a Jordan curve, and every point of the selected drawing off the
stretch lies in its unbounded region, joined to infinity by a vertical ray.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology Schoenflies unitInterval
open FiniteAvalanches.Electrical.Source (drawingTrace)
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
variable {D : Drawing J} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

/-- The points of a selected drawing strictly above the horizontal line. -/
def upperPart (D : Drawing J) (S : Set V) (T : Finset E) : Set (ℝ × ℝ) :=
  (Drawing.toPartial D S T).trace ∩ {w | 0 < w.2}


theorem trace_toPartial_subset (D : Drawing J) (S : Set V) (T : Set E) :
    (Drawing.toPartial D S T).trace ⊆ drawingTrace D := by
  rintro z (⟨v, -, rfl⟩ | ⟨e, -, t, rfl⟩)
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr (mem_iUnion.mpr ⟨e, t, rfl⟩)

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

/-- Near a point strictly inside a path edge, nothing of the drawing lies above
the line. -/
theorem not_mem_closure_upperPart_of_edge (S : Set V) (T : Finset E) (i : Fin m) {x : ℝ}
    (hx0 : (i : ℝ) / m < x) (hx1 : x < ((i : ℝ) + 1) / m) :
    (x, (0 : ℝ)) ∉ closure (upperPart D S T) := by
  intro hcl
  have hg := h.gap_pos i hx0 hx1
  obtain ⟨w, ⟨hwX, hw2⟩, hdist⟩ := Metric.mem_closure_iff.mp hcl (gap D copies i x / 2)
    (by positivity)
  have hwd : max (dist x w.1) (dist 0 w.2) < gap D copies i x / 2 := by
    have := hdist
    rwa [Prod.dist_eq] at this
  have h1 : |w.1 - x| < gap D copies i x / 2 := by
    have := lt_of_le_of_lt (le_max_left _ _) hwd
    rwa [Real.dist_eq, abs_sub_comm] at this
  have h2 : |w.2| < gap D copies i x / 2 := by
    have := lt_of_le_of_lt (le_max_right _ _) hwd
    rwa [Real.dist_eq, zero_sub, abs_neg] at this
  have hle := h.gap_le_of_mem_trace i (trace_toPartial_subset D S T hwX) (ne_of_gt hw2)
  have hlip := infDist_le_infDist_add_dist (x := (x, (0 : ℝ))) (y := (w.1, (0 : ℝ)))
    (s := otherTrace (D := D) (copies := copies) i)
  have hd : dist (x, (0 : ℝ)) (w.1, (0 : ℝ)) = |w.1 - x| := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_sub_comm, max_eq_left (abs_nonneg _)]
  change gap D copies i x ≤ gap D copies i w.1 + _ at hlip
  rw [hd] at hlip
  linarith

/-- Near an interior vertex of a stretch whose off-path edges all leave from below,
nothing of the selected drawing lies above the line. -/
theorem not_mem_closure_upperPart_of_vertex (S : Set V) (T : Finset E) {p q : ℕ}
    (hbelow : EndsBelow D path copies T p q) {a : ℕ} (hpa : p < a) (haq : a < q) (ham : a < m) :
    D.point (path ⟨a, by omega⟩) ∉ closure (upperPart D S T) := by
  set va := D.point (path ⟨a, by omega⟩) with hva
  have hva2 : va.2 = 0 := by rw [hva, h.point]
  have hpiece : ∀ e ∈ T, ∃ C : Set (ℝ × ℝ), IsCompact C ∧ va ∉ C ∧
      ∀ t, 0 < (D.curve e t).2 → D.curve e t ∈ C := by
    intro e heT
    by_cases hep : e ∈ range copies
    · obtain ⟨j, rfl⟩ := hep
      refine ⟨∅, isCompact_empty, notMem_empty _, fun t ht => ?_⟩
      rw [h.curve_snd j t] at ht
      exact absurd ht (lt_irrefl 0)
    have hends := hbelow e heT hep a hpa haq ham
    obtain ⟨τ₁, hτ₁, hs₁⟩ : ∃ τ₁ > 0, J.left e = path ⟨a, by omega⟩ →
        ∀ t : ArcParameter, 0 < t.val → t.val < τ₁ → (D.curve e t).2 < 0 := by
      by_cases hl : J.left e = path ⟨a, by omega⟩
      · obtain ⟨τ, hτ, hs⟩ := hends.1 hl
        exact ⟨τ, hτ, fun _ => hs⟩
      · exact ⟨1, one_pos, fun h' => absurd h' hl⟩
    obtain ⟨τ₂, hτ₂, hs₂⟩ : ∃ τ₂ > 0, J.right e = path ⟨a, by omega⟩ →
        ∀ t : ArcParameter, 1 - τ₂ < t.val → t.val < 1 → (D.curve e t).2 < 0 := by
      by_cases hr : J.right e = path ⟨a, by omega⟩
      · obtain ⟨τ, hτ, hs⟩ := hends.2 hr
        exact ⟨τ, hτ, fun _ => hs⟩
      · exact ⟨1, one_pos, fun h' => absurd h' hr⟩
    set τ₁' : ℝ := if J.left e = path ⟨a, by omega⟩ then τ₁ else 0 with hτ₁'
    set τ₂' : ℝ := if J.right e = path ⟨a, by omega⟩ then τ₂ else 0 with hτ₂'
    let A : Set ArcParameter := {t | τ₁' ≤ t.val ∧ t.val ≤ 1 - τ₂'}
    have hA : IsClosed A :=
      (isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)
    refine ⟨D.curve e '' A, hA.isCompact.image (D.continuous e), ?_, ?_⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, hte⟩
      rcases (D.curve_vertex_iff e t _).mp hte with ⟨ht0, hl⟩ | ⟨ht0, hr⟩
      · have : τ₁' = τ₁ := by rw [hτ₁', if_pos hl]
        rw [this, ht0] at ht1
        linarith
      · have : τ₂' = τ₂ := by rw [hτ₂', if_pos hr]
        rw [this, ht0] at ht2
        linarith
    · intro t ht
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · by_contra hlt
        push Not at hlt
        by_cases hl : J.left e = path ⟨a, by omega⟩
        · rw [hτ₁', if_pos hl] at hlt
          rcases eq_or_lt_of_le t.2.1 with h0 | h0
          · have : t = zeroParam := Subtype.ext h0.symm
            rw [this, D.start, hl, ← hva, hva2] at ht
            exact lt_irrefl 0 ht
          · exact lt_asymm ht (hs₁ hl t h0 hlt)
        · rw [hτ₁', if_neg hl] at hlt
          exact absurd t.2.1 (not_le.mpr hlt)
      · by_contra hlt
        push Not at hlt
        by_cases hr : J.right e = path ⟨a, by omega⟩
        · rw [hτ₂', if_pos hr] at hlt
          rcases eq_or_lt_of_le t.2.2 with h1 | h1
          · have : t = oneParam := Subtype.ext h1
            rw [this, D.finish, hr, ← hva, hva2] at ht
            exact lt_irrefl 0 ht
          · exact lt_asymm ht (hs₂ hr t hlt h1)
        · rw [hτ₂', if_neg hr, sub_zero] at hlt
          exact absurd t.2.2 (not_le.mpr hlt)
  choose! C hCc hCva hCmem using hpiece
  let CV : Set (ℝ × ℝ) := D.point '' (S \ {path ⟨a, by omega⟩})
  have hCV : IsCompact CV := ((Set.toFinite _).image _).isCompact
  have hvaCV : va ∉ CV := by
    rintro ⟨v, ⟨_, hv⟩, hve⟩
    exact hv (D.point_injective hve)
  have hall : IsCompact (CV ∪ ⋃ e ∈ T, C e) :=
    hCV.union (T.finite_toSet.isCompact_biUnion fun e he => hCc e he)
  have hsub : upperPart D S T ⊆ CV ∪ ⋃ e ∈ T, C e := by
    rintro z ⟨(⟨v, hv, rfl⟩ | ⟨e, he, t, rfl⟩), hz⟩
    · left
      refine ⟨v, ⟨hv, ?_⟩, rfl⟩
      rintro rfl
      change 0 < va.2 at hz
      rw [hva2] at hz
      exact lt_irrefl 0 hz
    · right
      exact mem_biUnion (x := e) he (hCmem e he t hz)
  intro hcl
  have := closure_minimal hsub hall.isClosed hcl
  rcases this with h1 | h1
  · exact hvaCV h1
  · obtain ⟨e, he, h2⟩ := mem_iUnion₂.mp h1
    exact hCva e he h2

/-- Nothing of the selected drawing above the line accumulates at an interior
point of a stretch whose off-path edges leave its interior vertices from below. -/
theorem not_mem_closure_upperPart (S : Set V) (T : Finset E) {p q : ℕ} (hqm : q ≤ m)
    (hbelow : EndsBelow D path copies T p q) {x : ℝ} (hx0 : (p : ℝ) / m < x)
    (hx1 : x < (q : ℝ) / m) : (x, (0 : ℝ)) ∉ closure (upperPart D S T) := by
  have hm := h.m_pos_real
  have hq1 : (q : ℝ) / m ≤ 1 := by rw [div_le_one hm]; exact_mod_cast hqm
  obtain ⟨i, hi0, hi1⟩ := exists_index_of_mem_Icc h.pos
    (le_trans (div_nonneg (Nat.cast_nonneg _) hm.le) hx0.le) (le_trans hx1.le hq1)
  have hpi : p ≤ (i : ℕ) := by
    by_contra hlt
    push Not at hlt
    have : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hlt
    have h2 : ((i : ℝ) + 1) / m ≤ (p : ℝ) / m := div_le_div_of_nonneg_right this hm.le
    linarith
  have hiq : (i : ℕ) < q := by
    by_contra hle
    push Not at hle
    have : (q : ℝ) ≤ (i : ℕ) := by exact_mod_cast hle
    have h2 : (q : ℝ) / m ≤ (i : ℝ) / m := div_le_div_of_nonneg_right this hm.le
    linarith
  rcases eq_or_lt_of_le hi0 with heq | hlt0
  · -- a vertex
    have hpa : p < (i : ℕ) := by
      by_contra hle
      push Not at hle
      have : ((i : ℕ) : ℝ) ≤ p := by exact_mod_cast hle
      have h2 : (i : ℝ) / m ≤ (p : ℝ) / m := div_le_div_of_nonneg_right this hm.le
      linarith
    have := h.not_mem_closure_upperPart_of_vertex S T hbelow hpa hiq (by omega)
    have key : (x, (0 : ℝ)) = D.point (path ⟨(i : ℕ), by omega⟩) := by
      rw [h.point]
      show (x, (0 : ℝ)) = (((i : ℕ) : ℝ) / m, 0)
      rw [heq]
    rwa [key]
  rcases eq_or_lt_of_le hi1 with heq' | hlt1
  · have hi1q : (i : ℕ) + 1 < q := by
      by_contra hle
      push Not at hle
      have : (q : ℝ) ≤ (i : ℝ) + 1 := by exact_mod_cast hle
      have h2 : (q : ℝ) / m ≤ ((i : ℝ) + 1) / m := div_le_div_of_nonneg_right this hm.le
      linarith
    have := h.not_mem_closure_upperPart_of_vertex S T hbelow (a := (i : ℕ) + 1) (by omega)
      hi1q (by omega)
    have key : (x, (0 : ℝ)) = D.point (path ⟨(i : ℕ) + 1, by omega⟩) := by
      rw [h.point]
      show (x, (0 : ℝ)) = ((((i : ℕ) + 1 : ℕ) : ℝ) / m, 0)
      rw [Nat.cast_add, Nat.cast_one, heq']
    rwa [key]
  · exact h.not_mem_closure_upperPart_of_edge S T i hlt0 hlt1

end StraightPath

/-- The distance from a point of the horizontal axis to the selected drawing above
the line, with one auxiliary point below the line. -/
def upperDist (D : Drawing J) (S : Set V) (T : Finset E) (x : ℝ) : ℝ :=
  infDist (x, (0 : ℝ)) (insert ((0 : ℝ), (-1 : ℝ)) (upperPart D S T))

/-- The tent function of an interval. -/
def tent (a b x : ℝ) : ℝ := max 0 (min (x - a) (b - x))

/-- The height of the free collar above a stretch. -/
def collarHeight (D : Drawing J) (S : Set V) (T : Finset E) (a b x : ℝ) : ℝ :=
  min (upperDist D S T x) (tent a b x) / 2

theorem continuous_collarHeight (D : Drawing J) (S : Set V) (T : Finset E) (a b : ℝ) :
    Continuous (collarHeight D S T a b) := by
  have h1 : Continuous (upperDist D S T) :=
    (continuous_infDist_pt _).comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous (tent a b) := by
    unfold tent
    fun_prop
  unfold collarHeight
  exact (h1.min h2).div_const 2

theorem collarHeight_nonneg (D : Drawing J) (S : Set V) (T : Finset E) (a b x : ℝ) :
    0 ≤ collarHeight D S T a b x :=
  div_nonneg (le_min infDist_nonneg (le_max_left _ _)) zero_le_two

theorem collarHeight_eq_zero (D : Drawing J) (S : Set V) (T : Finset E) {a b x : ℝ}
    (hx : x ≤ a ∨ b ≤ x) : collarHeight D S T a b x = 0 := by
  have ht : tent a b x = 0 := by
    apply max_eq_left
    rcases hx with hx | hx
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  have hd : 0 ≤ upperDist D S T x := infDist_nonneg
  rw [collarHeight, ht, min_eq_right hd, zero_div]

theorem collarHeight_lt (D : Drawing J) (S : Set V) (T : Finset E) (a b : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ (Drawing.toPartial D S T).trace) (hz2 : 0 < z.2) :
    collarHeight D S T a b z.1 < z.2 := by
  have hd : upperDist D S T z.1 ≤ z.2 := by
    have := infDist_le_dist_of_mem (x := (z.1, (0 : ℝ)))
      (mem_insert_of_mem ((0 : ℝ), (-1 : ℝ)) (show z ∈ upperPart D S T from ⟨hz, hz2⟩))
    rw [Prod.dist_eq, dist_self, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hz2,
      max_eq_right (le_of_lt hz2)] at this
    exact this
  have := min_le_left (upperDist D S T z.1) (tent a b z.1)
  unfold collarHeight
  linarith

/-- A point on the horizontal line between the ends of the parameter interval. -/
def lerp (a b s : ℝ) : ℝ := a + s * (b - a)

/-- The stretch, as the lower arc of the collar. -/
def collarBase (a b s : ℝ) : ℝ × ℝ := (lerp a b s, 0)

/-- The upper arc of the collar. -/
def collarTop (D : Drawing J) (S : Set V) (T : Finset E) (a b s : ℝ) : ℝ × ℝ :=
  (lerp a b s, collarHeight D S T a b (lerp a b s))

theorem lerp_injective {a b : ℝ} (hab : a < b) : Function.Injective (lerp a b) := by
  intro s t hst
  simp only [lerp] at hst
  have := mul_right_cancel₀ (sub_ne_zero.mpr hab.ne') (by linarith : s * (b - a) = t * (b - a))
  exact this

theorem lerp_mem {a b s : ℝ} (hab : a < b) (hs : s ∈ I) : a ≤ lerp a b s ∧ lerp a b s ≤ b := by
  obtain ⟨h0, h1⟩ := hs
  simp only [lerp]
  constructor <;> nlinarith

theorem arcPair_collar (D : Drawing J) (S : Set V) (T : Finset E) {a b : ℝ} (hab : a < b)
    (hpos : ∀ x, a < x → x < b → 0 < collarHeight D S T a b x) :
    ArcPair (collarBase a b) (collarTop D S T a b) where
  continuousOn_left := by
    unfold collarBase lerp
    fun_prop
  injOn_left := fun s _ t _ h => lerp_injective hab (Prod.mk.inj h).1
  continuousOn_right := by
    have := continuous_collarHeight D S T a b
    unfold collarTop
    exact (Continuous.prodMk (by unfold lerp; fun_prop)
      (this.comp (by unfold lerp; fun_prop))).continuousOn
  injOn_right := fun s _ t _ h => lerp_injective hab (Prod.mk.inj h).1
  start := by
    simp only [collarTop, collarBase, lerp, zero_mul, add_zero]
    rw [collarHeight_eq_zero D S T (Or.inl le_rfl)]
  finish := by
    simp only [collarTop, collarBase, lerp, one_mul, add_sub_cancel]
    rw [collarHeight_eq_zero D S T (Or.inr le_rfl)]
  meet := by
    rintro z ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
    obtain ⟨h1, h2⟩ := Prod.mk.inj hts
    have hst : t = s := lerp_injective hab h1
    subst hst
    have hz : ¬ (a < lerp a b t ∧ lerp a b t < b) := fun hx => (hpos _ hx.1 hx.2).ne' h2
    obtain ⟨h0, h1⟩ := hs
    rcases eq_or_lt_of_le h0 with h0 | h0
    · left
      rw [← h0]
    rcases eq_or_lt_of_le h1 with h1 | h1
    · right
      rw [h1, mem_singleton_iff]
    exfalso
    apply hz
    simp only [lerp]
    constructor <;> nlinarith

theorem not_isBounded_vertical_up (x b : ℝ) : ¬ IsBounded ((fun y : ℝ => (x, y)) '' Ici b) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have := hR ⟨max b R + 1, mem_Ici.mpr (by linarith [le_max_left b R]), rfl⟩
  rw [mem_closedBall, dist_zero_right, Prod.norm_def] at this
  have h2 := (le_max_right _ _).trans this
  rw [Real.norm_eq_abs] at h2
  linarith [le_abs_self (max b R + 1), le_max_right b R]

theorem not_isBounded_vertical_down (x b : ℝ) : ¬ IsBounded ((fun y : ℝ => (x, y)) '' Iic b) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have := hR ⟨min b (-R) - 1, mem_Iic.mpr (by linarith [min_le_left b (-R)]), rfl⟩
  rw [mem_closedBall, dist_zero_right, Prod.norm_def] at this
  have h2 := (le_max_right _ _).trans this
  rw [Real.norm_eq_abs] at h2
  linarith [neg_abs_le (min b (-R) - 1), min_le_right b (-R)]

/-- A point below the line, on the line beyond the stretch, or above the collar,
lies in the unbounded region of the boundary of the collar. -/
theorem mem_outside_collar (D : Drawing J) (S : Set V) (T : Finset E) {a b : ℝ} (hab : a < b)
    (hpos : ∀ x, a < x → x < b → 0 < collarHeight D S T a b x) {w : ℝ × ℝ}
    (hw : w.2 < 0 ∨ (w.2 = 0 ∧ (w.1 < a ∨ b < w.1)) ∨
      (0 < w.2 ∧ collarHeight D S T a b w.1 < w.2)) :
    euclideanPlaneHomeomorph w ∈
      outside (euclideanPlaneHomeomorph '' (collarBase a b '' I ∪ collarTop D S T a b '' I)) := by
  have hJ := (arcPair_collar D S T hab hpos).isJordanCurve
  have hZ : ∀ z ∈ collarBase a b '' I ∪ collarTop D S T a b '' I,
      a ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = 0 ∨ z.2 = collarHeight D S T a b z.1) := by
    rintro z (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨(lerp_mem hab hs).1, (lerp_mem hab hs).2, Or.inl rfl⟩
    · exact ⟨(lerp_mem hab hs).1, (lerp_mem hab hs).2, Or.inr rfl⟩
  have hw' : w = (w.1, w.2) := rfl
  rcases hw with hw | hw | hw
  · refine image_subset_outside_of_unbounded hJ (isPreconnected_Iic.image _ (by fun_prop))
      ?_ (not_isBounded_vertical_down w.1 w.2) ⟨w, ⟨w.2, mem_Iic.mpr le_rfl, rfl⟩, rfl⟩
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hz
    obtain ⟨-, -, h | h⟩ := hZ _ hz
    · change y = 0 at h
      linarith [mem_Iic.mp hy]
    · change y = _ at h
      linarith [mem_Iic.mp hy, collarHeight_nonneg D S T a b w.1]
  · refine image_subset_outside_of_unbounded hJ (isPreconnected_Iic.image _ (by fun_prop))
      ?_ (not_isBounded_vertical_down w.1 w.2) ⟨w, ⟨w.2, mem_Iic.mpr le_rfl, rfl⟩, rfl⟩
    rw [Set.disjoint_left]
    rintro _ ⟨y, -, rfl⟩ hz
    obtain ⟨h1, h2, -⟩ := hZ _ hz
    rcases hw.2 with h | h
    · exact absurd h1 (not_le.mpr h)
    · exact absurd h2 (not_le.mpr h)
  · refine image_subset_outside_of_unbounded hJ (isPreconnected_Ici.image _ (by fun_prop))
      ?_ (not_isBounded_vertical_up w.1 w.2) ⟨w, ⟨w.2, mem_Ici.mpr le_rfl, rfl⟩, rfl⟩
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hz
    obtain ⟨-, -, h | h⟩ := hZ _ hz
    · change y = 0 at h
      linarith [mem_Ici.mp hy]
    · change y = _ at h
      linarith [mem_Ici.mp hy]

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

/-- The collar above a stretch whose off-path edges leave its interior vertices
from below has positive height over the interior of the stretch. -/
theorem collarHeight_pos (S : Set V) (T : Finset E) {p q : ℕ} (hqm : q ≤ m)
    (hbelow : EndsBelow D path copies T p q) {x : ℝ} (hx0 : (p : ℝ) / m < x)
    (hx1 : x < (q : ℝ) / m) : 0 < collarHeight D S T ((p : ℝ) / m) ((q : ℝ) / m) x := by
  have hd : 0 < upperDist D S T x := by
    rw [upperDist, ← infDist_pos_iff_notMem_closure ⟨_, mem_insert _ _⟩, insert_eq,
      closure_union, closure_singleton]
    rintro (hx | hx)
    · have := (Prod.mk.inj (mem_singleton_iff.mp hx)).2
      norm_num at this
    · exact h.not_mem_closure_upperPart S T hqm hbelow hx0 hx1 hx
  have ht : 0 < tent ((p : ℝ) / m) ((q : ℝ) / m) x :=
    lt_max_of_lt_right (lt_min (by linarith) (by linarith))
  exact div_pos (lt_min hd ht) zero_lt_two

end StraightPath

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
