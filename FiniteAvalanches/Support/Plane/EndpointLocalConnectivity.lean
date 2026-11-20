import FiniteAvalanches.Support.Plane.ArcComponentPreservation
import FiniteAvalanches.Support.Plane.TreePaths
import FiniteAvalanches.Support.Plane.PuncturedTransport

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

private theorem endpoint_arc_ball_contra {a b : ℝ} (f : Icc a b → (ℝ × ℝ)) (hf : Continuous f)
    (hi : Function.Injective f) {r : ℝ} (hr : 0 < r)
    (t l u : Icc a b) (hlt : l.val < t.val) (htu : t.val < u.val)
    (hl : f l ∈ Metric.ball (f t) r) (hu : f u ∈ Metric.ball (f t) r)
    (hball : Metric.ball (f t) r ⊆ range f) : False := by
  let A := Metric.ball (f t) r \ {f t}
  have hconn : IsPreconnected (f ⁻¹' A) :=
    (isPathConnected_ball_diff_singleton (f t) hr).isConnected.isPreconnected.preimage_of_isClosedMap
      hi hf.isClosedMap (fun x hx => hball hx.1)
  have hconn' : IsPreconnected ((Subtype.val : Icc a b → ℝ) '' (f ⁻¹' A)) :=
    hconn.image _ continuous_subtype_val.continuousOn
  have hl' : l.val ∈ (Subtype.val : Icc a b → ℝ) '' (f ⁻¹' A) := by
    refine ⟨l, ⟨hl, ?_⟩, rfl⟩
    simpa only [mem_singleton_iff] using (fun h : f l = f t => (ne_of_lt hlt) (congrArg Subtype.val (hi h)))
  have hu' : u.val ∈ (Subtype.val : Icc a b → ℝ) '' (f ⁻¹' A) := by
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    simpa only [mem_singleton_iff] using (fun h : f u = f t => (ne_of_gt htu) (congrArg Subtype.val (hi h)))
  have ht' := hconn'.ordConnected.out hl' hu' ⟨hlt.le, htu.le⟩
  obtain ⟨v, hv, hv'⟩ := ht'
  have : v = t := Subtype.ext hv'
  subst v
  exact hv.2 (by simp)


private theorem endpoint_compact_arc_interior {a b : ℝ} (hab : a < b) (f : Icc a b → (ℝ × ℝ))
    (hf : Continuous f) (hi : Function.Injective f) : interior (range f) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  let a' : Icc a b := ⟨a, ⟨le_refl _, hab.le⟩⟩
  let b' : Icc a b := ⟨b, ⟨hab.le, le_refl _⟩⟩
  have hd : Dense ((Set.univ : Set (ℝ × ℝ)) \ {f a', f b'}) :=
    dense_univ.sdiff_finite (Set.toFinite _)
  obtain ⟨y, hy, hyend⟩ := hd.inter_open_nonempty (Metric.ball x r) Metric.isOpen_ball
    ⟨x, Metric.mem_ball_self hr⟩
  have hyRange : y ∈ range f := interior_subset (hrsub hy)
  obtain ⟨t, rfl⟩ := hyRange
  have hta : a < t.val := by
    have hne : t.val ≠ a := by
      intro h
      have : t = a' := Subtype.ext h
      subst t
      exact hyend.2 (by simp)
    exact lt_of_le_of_ne t.property.1 (Ne.symm hne)
  have htb : t.val < b := by
    have hne : t.val ≠ b := by
      intro h
      have : t = b' := Subtype.ext h
      subst t
      exact hyend.2 (by simp)
    exact lt_of_le_of_ne t.property.2 hne
  obtain ⟨q, hq, hqsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball (f t) hy
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hf.continuousAt q hq
  let d : ℝ := min ((t.val - a)/2) (min ((b - t.val)/2) (δ/2))
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hda : d ≤ (t.val - a)/2 := min_le_left _ _
  have hdb : d ≤ (b - t.val)/2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hdd : d ≤ δ/2 := le_trans (min_le_right _ _) (min_le_right _ _)
  let l : Icc a b := ⟨t.val - d, ⟨by linarith, by linarith [t.property.2]⟩⟩
  let u : Icc a b := ⟨t.val + d, ⟨by linarith [t.property.1], by linarith⟩⟩
  have hld : dist l t < δ := by
    change dist (t.val - d) t.val < δ
    rw [Real.dist_eq, show t.val - d - t.val = -d by ring, abs_neg, abs_of_pos hdpos]
    linarith
  have hud : dist u t < δ := by
    change dist (t.val + d) t.val < δ
    rw [Real.dist_eq, show t.val + d - t.val = d by ring, abs_of_pos hdpos]
    linarith
  exact endpoint_arc_ball_contra f hf hi hq t l u (by dsimp [l]; linarith)
    (by dsimp [u]; linarith) (hδf hld) (hδf hud)
    (fun z hz => interior_subset (hrsub (hqsub hz)))

/-- The complement of a simple plane path is dense. -/
theorem dense_compl_range_injective_path {x y : ℝ × ℝ}
    (p : Path x y) (hp : Function.Injective p) : Dense (range p)ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  exact endpoint_compact_arc_interior (by norm_num : (0 : ℝ) < 1) p p.continuous hp

/-- A simple plane arc admits complement points joined by paths in balls
shrinking to its initial endpoint. -/
theorem exists_shrinking_endpoint_paths
    {x y : ℝ × ℝ} (p : Path x y) (hp : Function.Injective p) :
    ∃ z : ℕ → ℝ × ℝ,
      (∀ n, z n ∉ range p) ∧
      (∀ n : ℕ, z n ∈ ball x (1 / ((n : ℝ) + 1))) ∧
      ∀ n : ℕ, ∃ q : Path (z n) (z (n + 1)),
        range q ⊆ ball x (1 / ((n : ℝ) + 1)) \ range p := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := by
    intro n
    dsimp [r]
    positivity
  have hlocal : ∀ n, ∃ δ > 0, ∀ a ∈ ball x δ \ range p,
      ∀ b ∈ ball x δ \ range p, ∃ q : Path a b, range q ⊆ ball x (r n) \ range p :=
    fun n => exists_endpoint_ball_paths p hp (hr n)
  choose δ hδ hpath using hlocal
  have hchoice : ∀ n, ∃ z : ℝ × ℝ,
      z ∈ ball x (min (δ n) (min (δ (n + 1)) (r n))) ∧ z ∉ range p := by
    intro n
    have hpos : 0 < min (δ n) (min (δ (n + 1)) (r n)) :=
      lt_min (hδ n) (lt_min (hδ (n + 1)) (hr n))
    obtain ⟨z, hz, hznot⟩ := (dense_compl_range_injective_path p hp).inter_open_nonempty
      _ isOpen_ball ⟨x, mem_ball_self hpos⟩
    exact ⟨z, hz, hznot⟩
  choose z hz hznot using hchoice
  refine ⟨z, hznot, ?_, ?_⟩
  · intro n
    exact ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _)) (hz n)
  · intro n
    have ha : z n ∈ ball x (δ (n + 1)) \ range p :=
      ⟨ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) (hz n), hznot n⟩
    have hb : z (n + 1) ∈ ball x (δ (n + 1)) \ range p :=
      ⟨ball_subset_ball (min_le_left _ _) (hz (n + 1)), hznot (n + 1)⟩
    obtain ⟨q, hq⟩ := hpath (n + 1) (z n) ha (z (n + 1)) hb
    refine ⟨q, hq.trans (sdiff_subset_sdiff_left (ball_subset_ball ?_))⟩
    dsimp [r]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith

end FiniteAvalanches.Electrical.StatementGeometry
