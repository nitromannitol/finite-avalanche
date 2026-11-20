import FiniteAvalanches.Support.Plane.ArcComponentPreservation
import FiniteAvalanches.Support.Plane.TreePaths

/-!
# Local connectivity near an arc endpoint

Janiszewski's theorem controls the complement of a short initial subarc in a
ball, giving connected neighborhoods of an endpoint in the arc complement.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric

/-- Adjoining an arc along a preconnected intersection preserves each component
of the complement of a compact plane set. -/
theorem connectedComponentIn_compl_union_path
    {K : Set (ℝ × ℝ)} {x y a b : ℝ × ℝ}
    (hK : IsCompact K) (p : Path x y) (hp : Function.Injective p)
    (hPK : IsPreconnected (range p ∩ K))
    (ha : a ∉ range p ∪ K) (hb : b ∉ range p ∪ K)
    (hconn : b ∈ connectedComponentIn Kᶜ a) :
    b ∈ connectedComponentIn (range p ∪ K)ᶜ a := by
  simpa only [union_empty] using
    (connectedComponentIn_compl_union_path_two hK isCompact_empty p hp hPK
      (by simp only [inter_empty]; exact isPreconnected_empty)
      (by simpa only [union_empty] using ha)
      (by simpa only [union_empty] using hb)
      (by simpa only [union_empty] using hconn))

/-- A simple arc has a nontrivial initial subarc inside any neighborhood of its
initial endpoint. -/
theorem exists_initial_subpath_subset_open
    {x y : ℝ × ℝ} (p : Path x y) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ s : unitInterval, s ≠ 0 ∧ range (p.subpath 0 s) ⊆ U := by
  have hn : p ⁻¹' U ∈ nhds (0 : unitInterval) := by
    apply p.continuous.continuousAt.tendsto
    simpa only [Path.source] using hU.mem_nhds hx
  obtain ⟨v, hv, hvsub⟩ := exists_Ico_subset_of_mem_nhds hn
    ⟨1, by norm_num⟩
  obtain ⟨s, hs0, hsv⟩ := exists_between hv
  refine ⟨s, ne_of_gt hs0, ?_⟩
  rw [Path.range_subpath_of_le p 0 s bot_le]
  rintro z ⟨t, ht, rfl⟩
  exact hvsub ⟨bot_le, lt_of_le_of_lt ht.2 hsv⟩

/-- Near an endpoint of a simple plane arc, any two complement points can be
joined in the complement inside an arbitrarily prescribed ball. -/
theorem exists_endpoint_ball_paths
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p)
    {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, ∀ a ∈ ball x δ \ range p, ∀ b ∈ ball x δ \ range p,
      ∃ q : Path a b, range q ⊆ ball x R \ range p := by
  obtain ⟨s, hs, hsball⟩ := exists_initial_subpath_subset_open p isOpen_ball
    (mem_ball_self hR)
  let P := p.subpath 0 s
  let Q := p.subpath s 1
  have hP : Function.Injective P := by
    intro u v huv
    have heq := congrArg Subtype.val (hp huv)
    simp only [Set.Icc.coe_convexComb] at heq
    simp only [show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero, zero_add] at heq
    apply Subtype.ext
    have hs' : (s : ℝ) ≠ 0 := fun h => hs (Subtype.ext h)
    have heq' : ((u : ℝ) - v) * (s : ℝ) = 0 := by nlinarith [heq]
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq').resolve_right hs')
  have hxQ : x ∉ range Q := by
    change x ∉ range (p.subpath s 1)
    rw [Path.range_subpath_of_le p s 1 le_top]
    rintro ⟨t, ht, heq⟩
    have ht0 : t = 0 := hp (by simpa only [Path.source] using heq)
    exact hs (le_antisymm (ht0 ▸ ht.1) bot_le)
  have hopen : IsOpen (range Q)ᶜ := (isCompact_range Q.continuous).isClosed.isOpen_compl
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen x hxQ
  let δ := min ε (R / 2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδR : δ < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hδQ : ball x δ ⊆ (range Q)ᶜ :=
    (ball_subset_ball (min_le_left _ _)).trans hεsub
  let K := range Q ∪ sphere x R
  have hK : IsCompact K := (isCompact_range Q.continuous).union (isCompact_sphere x R)
  have hPK : range P ∩ K = {p s} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hzP, hzQ | hzS⟩
      · change z ∈ range (p.subpath 0 s) at hzP
        change z ∈ range (p.subpath s 1) at hzQ
        rw [Path.range_subpath_of_le p 0 s bot_le] at hzP
        rw [Path.range_subpath_of_le p s 1 le_top] at hzQ
        obtain ⟨u, hu, rfl⟩ := hzP
        obtain ⟨v, hv, heq⟩ := hzQ
        have huv : v = u := hp heq
        have huS : u = s := le_antisymm hu.2 (huv ▸ hv.1)
        rw [huS]
      · exact (Metric.sphere_disjoint_ball.le_bot ⟨hzS, hsball hzP⟩).elim
    · intro hz
      subst z
      exact ⟨P.target_mem_range, Or.inl Q.source_mem_range⟩
  have hballK : ball x δ ⊆ Kᶜ := by
    intro z hz
    refine fun hzK => ?_
    rcases hzK with hzQ | hzS
    · exact hδQ hz hzQ
    · exact (Metric.sphere_disjoint_ball.le_bot
        ⟨hzS, (ball_subset_ball hδR.le) hz⟩).elim
  have hfull : range P ∪ range Q = range p := by
    change range (p.subpath 0 s) ∪ range (p.subpath s 1) = range p
    rw [Path.range_subpath_of_le p 0 s bot_le, Path.range_subpath_of_le p s 1 le_top]
    ext z
    simp only [mem_union, mem_image, mem_Icc, mem_range]
    constructor
    · rintro (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩) <;> exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      by_cases h : t ≤ s
      · exact Or.inl ⟨t, ⟨bot_le, h⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨le_of_not_ge h, le_top⟩, rfl⟩
  refine ⟨δ, hδ, ?_⟩
  intro a ha b hb
  have haK : a ∉ range P ∪ K := by
    rintro (haP | haQ | haS)
    · exact ha.2 (hfull ▸ Or.inl haP)
    · exact hballK ha.1 (Or.inl haQ)
    · exact hballK ha.1 (Or.inr haS)
  have hbK : b ∉ range P ∪ K := by
    rintro (hbP | hbQ | hbS)
    · exact hb.2 (hfull ▸ Or.inl hbP)
    · exact hballK hb.1 (Or.inl hbQ)
    · exact hballK hb.1 (Or.inr hbS)
  have habK : b ∈ connectedComponentIn Kᶜ a :=
    ((convex_ball x δ).isPreconnected.subset_connectedComponentIn ha.1 hballK) hb.1
  have hab := connectedComponentIn_compl_union_path hK P hP
    (hPK ▸ isPreconnected_singleton) haK hbK habK
  let C := connectedComponentIn (range P ∪ K)ᶜ a
  have hCopen : IsOpen C :=
    ((isCompact_range P.continuous).union hK).isClosed.isOpen_compl.connectedComponentIn
  have hCa : a ∈ C := mem_connectedComponentIn haK
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr haK
  have hCball : C ⊆ ball x R := by
    apply hCconn.isPreconnected.subset_left_of_subset_union
      isOpen_ball isClosed_closedBall.isOpen_compl
    · exact Set.disjoint_left.mpr (fun _ hz hzc => hzc (ball_subset_closedBall hz))
    · intro z hz
      have hzS : z ∉ sphere x R := fun hzS =>
        (connectedComponentIn_subset (range P ∪ K)ᶜ a hz) (Or.inr (Or.inr hzS))
      simp only [mem_ball, mem_compl_iff, mem_closedBall, mem_union]
      rw [mem_sphere] at hzS
      exact (lt_or_gt_of_ne hzS).imp_right not_le_of_gt
    · exact ⟨a, hCa, (ball_subset_ball hδR.le) ha.1⟩
  obtain ⟨q, hq⟩ := (hCopen.isConnected_iff_isPathConnected.mp hCconn).joinedIn a hCa b hab
  refine ⟨q, ?_⟩
  rintro z ⟨t, rfl⟩
  refine ⟨hCball (hq t), ?_⟩
  intro hz
  have hnot := connectedComponentIn_subset (range P ∪ K)ᶜ a (hq t)
  rw [← hfull] at hz
  rcases hz with hzP | hzQ
  · exact hnot (Or.inl hzP)
  · exact hnot (Or.inr (Or.inl hzQ))

end FiniteAvalanches.Electrical.StatementGeometry
