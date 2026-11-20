import FiniteAvalanches.Support.Plane.FaceWinding
import FiniteAvalanches.Support.Plane.CopiedSimplePath
import FiniteAvalanches.Support.Plane.BondDualCycle
import FiniteAvalanches.External.PlaneTreeComplement
import FiniteAvalanches.Electrical.Plane.Incidence

/-!
# The face boundary law of a connected plane drawing

For a connected plane drawing with oriented edge charts, the signed boundary of
every face, taken against the chart sides of the edges, annihilates every
gradient of a vertex function.

For each edge outside a spanning tree, the closed path formed by that edge and
the tree path between its endpoints has a winding number on faces. Across each
edge it jumps by the signed passage of the closed path, so the signed cycle of
the edge is the dual coboundary of that winding function. Since the complement
of the tree is a spanning tree of the dual graph, every dual coboundary is a
combination of these cycles, and cycles annihilate gradients.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Plane Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
/-- Copied reachability is symmetric. -/
theorem CopiedGraph.reaches_symm_of_reaches (B : CopiedGraph V E) {S : Finset E} {x y : V}
    (h : B.reaches S x y) : B.reaches S y x := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨e, he, hends⟩ := hstep
    refine Relation.ReflTransGen.head ⟨e, he, ?_⟩ ih
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩

omit [Fintype V] in
/-- A connected copied graph has a spanning tree of original copies. -/
theorem CopiedGraph.exists_spanning_finset (B : CopiedGraph V E)
    (hB : ∀ x y, B.reaches Finset.univ x y) :
    ∃ T : Finset E, (∀ x y, B.reaches T x y) ∧
      ∀ e ∈ T, ¬ B.reaches (T.erase e) (B.left e) (B.right e) := by
  let s := (Finset.univ : Finset (Finset E)).filter (fun T => ∀ x y, B.reaches T x y)
  have hs : s.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩⟩
  obtain ⟨T, hT, hmin⟩ := s.exists_min_image Finset.card hs
  have hTc := (Finset.mem_filter.mp hT).2
  refine ⟨T, hTc, fun e he hcyc => ?_⟩
  have hall : ∀ x y, B.reaches (T.erase e) x y := by
    intro x y
    have hxy := hTc x y
    induction hxy with
    | refl => exact .refl
    | @tail b c _ hstep ih =>
      obtain ⟨f, hf, hends⟩ := hstep
      by_cases hfe : f = e
      · subst hfe
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1 h2
          exact ih.trans hcyc
        · subst h1 h2
          exact ih.trans (B.reaches_symm_of_reaches hcyc)
      · exact ih.tail ⟨f, Finset.mem_erase.mpr ⟨hfe, hf⟩, hends⟩
  have := hmin (T.erase e) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
  exact absurd this (not_le.mpr (Finset.card_erase_lt_of_mem he))

/-- Consecutive differences along a finite sequence telescope. -/
theorem fin_sum_castSucc_sub_succ {m : ℕ} (f : Fin (m + 1) → ℝ) :
    ∑ k : Fin m, (f k.castSucc - f k.succ) = f 0 - f (Fin.last m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (f ∘ Fin.castSucc)
    simp only [Function.comp_apply] at h
    have hsucc : ∀ k : Fin m, f k.succ.castSucc = f k.castSucc.succ := fun k => by
      rw [Fin.succ_castSucc]
    simp only [← hsucc] at h ⊢
    rw [h, Fin.castSucc_zero, Fin.succ_last]
    ring

/-- The fundamental closed path of an edge outside a spanning tree has a face
winding function whose jumps across the edges form the signed cycle of that
edge, and this cycle annihilates gradients. -/
theorem exists_fundamental_winding {B : CopiedGraph V E} (D : Drawing B)
    (charts : ∀ e, EdgeChart D e) (T : Finset E) (hT : ∀ x y, B.reaches T x y)
    (e : E) (he : e ∉ T) :
    ∃ (c : E → ℤ) (W : Face D → ℤ),
      (∀ e', W (positiveChartFace D e' (charts e')) =
        W (negativeChartFace D e' (charts e')) + c e') ∧
      (∀ e' ∉ T, c e' = if e' = e then 1 else 0) ∧
      (∀ q : V → ℝ, ∑ e', (c e' : ℝ) * (q (B.left e') - q (B.right e')) = 0) := by
  obtain ⟨m, vertices, copies, hinj, h0, hlast, hcopies, hends⟩ :=
    B.exists_simple_ordered_path T (hT (B.right e) (B.left e))
  have hcinj := B.copies_injective_of_vertices_injective m vertices hinj copies hends
  have hfwd : ∀ k, B.left (copies k) = vertices k.castSucc →
      B.right (copies k) = vertices k.succ := by
    intro k h
    rcases hends k with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · have := hinj (h.symm.trans h2)
      exact absurd (congrArg Fin.val this) (by simp)
  have hbwd : ∀ k, B.left (copies k) ≠ vertices k.castSucc →
      B.right (copies k) = vertices k.castSucc ∧ B.left (copies k) = vertices k.succ := by
    intro k h
    rcases hends k with ⟨h1, _⟩ | h'
    · exact absurd h1 h
    · exact h'
  let sign : Fin m → ℤ := fun k => if B.left (copies k) = vertices k.castSucc then 1 else -1
  let p : Fin (m + 1) → ℝ × ℝ := fun k => D.point (vertices k)
  let piece : (k : Fin m) → Path (p k.castSucc) (p k.succ) := fun k =>
    if h : B.left (copies k) = vertices k.castSucc then
      (D.edgePath (copies k)).cast (by simp only [p]; rw [h]) (by simp only [p]; rw [hfwd k h])
    else
      (D.edgePath (copies k)).symm.cast (by simp only [p]; rw [(hbwd k h).1])
        (by simp only [p]; rw [(hbwd k h).2])
  have hpiece : ∀ e' k, EdgeCrossingSign D e' (piece k)
      (if copies k = e' then sign k else 0) := by
    intro e' k
    simp only [piece, sign]
    split_ifs with h hc hc
    · subst hc
      exact (D.edgePath_crossingSign_self _).cast _ _
    · exact (D.edgePath_crossingSign_of_ne hc).cast _ _
    · subst hc
      exact (D.edgePath_crossingSign_self _).symm.cast _ _
    · have := (D.edgePath_crossingSign_of_ne hc).symm
      rw [neg_zero] at this
      exact this.cast _ _
  have hpiece_range : ∀ k, range (piece k) ⊆ drawingTrace D := by
    intro k
    simp only [piece]
    split_ifs
    · rw [Path.cast_coe]
      rintro _ ⟨t, rfl⟩
      exact Or.inr (mem_iUnion.mpr ⟨copies k, t, rfl⟩)
    · rw [Path.cast_coe, Path.symm_range]
      rintro _ ⟨t, rfl⟩
      exact Or.inr (mem_iUnion.mpr ⟨copies k, t, rfl⟩)
  let P : Path (D.point (B.right e)) (D.point (B.left e)) :=
    (Path.concat p piece).cast (by simp only [p]; rw [h0]) (by simp only [p]; rw [hlast])
  let γ : Path (D.point (B.left e)) (D.point (B.left e)) := (D.edgePath e).trans P
  have hγrange : range γ ⊆ drawingTrace D := by
    rw [Path.trans_range]
    apply union_subset
    · rintro _ ⟨t, rfl⟩
      exact Or.inr (mem_iUnion.mpr ⟨e, t, rfl⟩)
    · change range (Path.concat p piece) ⊆ drawingTrace D
      exact range_concat_subset p piece _ hpiece_range (Or.inl ⟨_, rfl⟩)
  have hne : ∀ k, copies k ≠ e := fun k h => he (h ▸ hcopies k)
  let c : E → ℤ := fun e' =>
    (if e' = e then 1 else 0) + ∑ k, if copies k = e' then sign k else 0
  have hcross : ∀ e', EdgeCrossingSign D e' γ (c e') := by
    intro e'
    apply EdgeCrossingSign.trans
    · by_cases h : e' = e
      · subst h
        rw [if_pos rfl]
        exact D.edgePath_crossingSign_self _
      · rw [if_neg h]
        exact D.edgePath_crossingSign_of_ne (Ne.symm h)
    · exact (EdgeCrossingSign.concat p piece _ (hpiece e')
        (fun k k' hkk' => by
          by_cases hk : copies k = e'
          · right
            rw [if_neg]
            intro hk'
            exact hkk' (hcinj (hk.trans hk'.symm))
          · left
            rw [if_neg hk])
        (fun k => D.avoids e' halfParameter (by norm_num [halfParameter])
          (by norm_num [halfParameter]) _ ∘ Eq.symm)).cast _ _
    · by_cases h : e' = e
      · right
        apply Finset.sum_eq_zero
        intro k _
        rw [if_neg (fun hk => hne k (hk.trans h))]
      · left
        rw [if_neg h]
  refine ⟨c, faceWinding D γ hγrange, fun e' =>
    faceWinding_chart_sides D γ hγrange e' (charts e') (hcross e'), ?_, ?_⟩
  · intro e' he'
    simp only [c]
    rw [Finset.sum_eq_zero, add_zero]
    intro k _
    rw [if_neg (fun (hk : copies k = e') => he' (hk ▸ hcopies k))]
  · intro q
    have hsplit : ∀ e', (c e' : ℝ) * (q (B.left e') - q (B.right e')) =
        (if e' = e then (q (B.left e') - q (B.right e')) else 0) +
          ∑ k, if copies k = e' then (sign k : ℝ) * (q (B.left e') - q (B.right e')) else 0 := by
      intro e'
      simp only [c]
      push_cast
      rw [add_mul, Finset.sum_mul]
      congr 1
      · split_ifs <;> ring
      · apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> simp
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hstep : ∀ k, (sign k : ℝ) * (q (B.left (copies k)) - q (B.right (copies k))) =
        q (vertices k.castSucc) - q (vertices k.succ) := by
      intro k
      simp only [sign]
      split_ifs with h
      · rw [h, hfwd k h]
        ring
      · rw [(hbwd k h).1, (hbwd k h).2]
        push_cast
        ring
    simp only [hstep]
    rw [fin_sum_castSucc_sub_succ (fun k => q (vertices k)), h0, hlast]
    ring

/-- The face boundary law: the signed chart-side boundary of every face of a
connected plane drawing annihilates every gradient of a vertex function. -/
theorem copyBoundary_chartFaces_gradient_eq_zero {B : CopiedGraph V E} (D : Drawing B)
    (charts : ∀ e, EdgeChart D e) (hV : (Set.univ : Set V).Nonempty)
    (hB : ∀ x y, B.reaches Finset.univ x y) [Fintype (Face D)] (q : V → ℝ) (F : Face D) :
    copyBoundary (fun e => negativeChartFace D e (charts e))
      (fun e => positiveChartFace D e (charts e)) (copyGradient B.left B.right q) F = 0 := by
  obtain ⟨T, hTconn, hTmin⟩ := B.exists_spanning_finset hB
  have hdual := (FiniteAvalanches.External.finite_plane_tree_complement B D charts hV hB
    inferInstance T).mp ⟨hV, hTconn, hTmin⟩
  have hfund : ∀ e, ∃ (c : E → ℤ) (W : Face D → ℤ), e ∉ T →
      (∀ e', W (positiveChartFace D e' (charts e')) =
        W (negativeChartFace D e' (charts e')) + c e') ∧
      (∀ e' ∉ T, c e' = if e' = e then 1 else 0) ∧
      (∀ q : V → ℝ, ∑ e', (c e' : ℝ) * (q (B.left e') - q (B.right e')) = 0) := by
    intro e
    by_cases he : e ∈ T
    · exact ⟨0, 0, fun h => (h he).elim⟩
    · obtain ⟨c, W, h⟩ := exists_fundamental_winding D charts T hTconn e he
      exact ⟨c, W, fun _ => h⟩
  choose c W hcW using hfund
  let pos : E → Face D := fun e => positiveChartFace D e (charts e)
  let neg : E → Face D := fun e => negativeChartFace D e (charts e)
  let f : Face D → ℝ := fun G => if G = F then 1 else 0
  let a : E → ℝ := fun e => f (pos e) - f (neg e)
  let h : Face D → ℝ := fun G => f G - ∑ e ∈ Tᶜ, a e * (W e G : ℝ)
  have hjump : ∀ e ∈ Tᶜ, ∀ e', (W e (pos e') : ℝ) - W e (neg e') = c e e' := by
    intro e he e'
    have := ((hcW e) (Finset.mem_compl.mp he)).1 e'
    simp only [pos, neg, this]
    push_cast
    ring
  have hdiff : ∀ e', h (pos e') - h (neg e') = a e' - ∑ e ∈ Tᶜ, a e * c e e' := by
    intro e'
    simp only [h]
    rw [show ∀ x y z w : ℝ, x - z - (y - w) = (x - y) - (z - w) by intros; ring,
      ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    rw [← mul_sub, hjump e he e']
  have hstep : ∀ e' ∈ Tᶜ, h (pos e') = h (neg e') := by
    intro e' he'
    have hsum : ∑ e ∈ Tᶜ, a e * (c e e' : ℝ) = a e' := by
      rw [Finset.sum_eq_single e']
      · rw [((hcW e') (Finset.mem_compl.mp he')).2.1 e' (Finset.mem_compl.mp he'), if_pos rfl]
        simp
      · intro e he hne
        rw [((hcW e) (Finset.mem_compl.mp he)).2.1 e' (Finset.mem_compl.mp he'),
          if_neg (Ne.symm hne)]
        simp
      · intro h
        exact (h he').elim
    have := hdiff e'
    rw [hsum, sub_self] at this
    linarith
  have hconst : ∀ G G', h G = h G' := by
    intro G G'
    have hr := hdual.2.1 G G'
    induction hr with
    | refl => rfl
    | tail _ hst ih =>
      obtain ⟨e, he, hends⟩ := hst
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [ih, ← h1, ← h2]
        exact (hstep e he).symm
      · rw [ih, ← h1, ← h2]
        exact hstep e he
  have hcoboundary : ∀ e', f (pos e') - f (neg e') = ∑ e ∈ Tᶜ, a e * c e e' := by
    intro e'
    have := hdiff e'
    rw [hconst (pos e') (neg e'), sub_self] at this
    linarith
  unfold copyBoundary
  have hterm : ∀ e', ((if negativeChartFace D e' (charts e') = F then
        copyGradient B.left B.right q e' else 0) -
      (if positiveChartFace D e' (charts e') = F then copyGradient B.left B.right q e' else 0)) =
      -((∑ e ∈ Tᶜ, a e * (c e e' : ℝ)) * (q (B.left e') - q (B.right e'))) := by
    intro e'
    rw [← hcoboundary e']
    simp only [f, pos, neg, copyGradient]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun e' _ => hterm e'), Finset.sum_neg_distrib, neg_eq_zero]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  have h0 := ((hcW e) (Finset.mem_compl.mp he)).2.2 q
  rw [show (∑ e', a e * (c e e' : ℝ) * (q (B.left e') - q (B.right e'))) =
      a e * ∑ e', (c e e' : ℝ) * (q (B.left e') - q (B.right e')) by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring), h0, mul_zero]

end FiniteAvalanches.Electrical.StatementGeometry
