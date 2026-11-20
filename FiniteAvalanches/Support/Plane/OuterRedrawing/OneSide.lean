import FiniteAvalanches.Support.Plane.OuterRedrawing.EndSides

/-!
# Edge ends on one side of a straight boundary path

Consider a connected selection of a drawing containing a stretch of a straight
boundary path, such that no interior vertex of the stretch carries a loop or
separates the selection. Then all other edges leave the interior vertices of the
stretch on one common side of the horizontal line.

An edge end above an interior vertex extends, through the selection with the
vertex removed, to an arc reaching another path vertex; this blocks an upper
collar next to the vertex. Symmetrically an end below blocks a lower collar.
Since every path edge has an outer collar on some side, both kinds of ends would
force consecutive path edges with outer collars on opposite sides, making their
common vertex separating.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology
open FiniteAvalanches.Electrical.Source (drawingTrace)
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
variable {D : Drawing J} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

/-- Edges with no endpoint at a given vertex. -/
def avoiding (J : CopiedGraph V E) (T : Finset E) (v : V) : Finset E :=
  T.filter fun e => J.left e ≠ v ∧ J.right e ≠ v

/-- Edges off a path whose path endpoints, if any, are a single path vertex. -/
def offPathTo (J : CopiedGraph V E) (path : Fin (m + 1) → V) (copies : Fin m → E)
    (A : Finset E) (c : Fin (m + 1)) : Finset E :=
  A.filter fun e => e ∉ range copies ∧ (J.left e ∉ range path ∨ J.left e = path c) ∧
    (J.right e ∉ range path ∨ J.right e = path c)

/-- A walk reaching the path reaches a first path vertex through edges off the
path touching the path only there. -/
theorem first_path_vertex (h : StraightPath D m path copies) (A : Finset E) {w x : V}
    (hreach : J.reaches A w x) (hx : x ∈ range path) :
    ∃ c : Fin (m + 1), (w ∈ range path → path c = w) ∧
      J.reaches (offPathTo J path copies A c) w (path c) := by
  unfold CopiedGraph.reaches at hreach ⊢
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, fun _ => rfl, Relation.ReflTransGen.refl⟩
  | @head w w' hstep _ ih =>
    by_cases hw : w ∈ range path
    · obtain ⟨c, rfl⟩ := hw
      exact ⟨c, fun _ => rfl, Relation.ReflTransGen.refl⟩
    obtain ⟨e, heA, hends⟩ := hstep
    have hepath : e ∉ range copies := by
      rintro ⟨i, rfl⟩
      rcases hends with ⟨hl, _⟩ | ⟨hr, _⟩
      · rcases h.ends i with ⟨hl', _⟩ | ⟨_, hl'⟩
        · exact hw ⟨_, (hl.symm.trans hl').symm⟩
        · exact hw ⟨_, (hl.symm.trans hl').symm⟩
      · rcases h.ends i with ⟨_, hr'⟩ | ⟨hr', _⟩
        · exact hw ⟨_, (hr.symm.trans hr').symm⟩
        · exact hw ⟨_, (hr.symm.trans hr').symm⟩
    by_cases hw' : w' ∈ range path
    · obtain ⟨c, rfl⟩ := hw'
      refine ⟨c, fun h' => absurd h' hw, Relation.ReflTransGen.single ⟨e, ?_, hends⟩⟩
      rw [offPathTo, Finset.mem_filter]
      refine ⟨heA, hepath, ?_, ?_⟩
      · rcases hends with ⟨hl, _⟩ | ⟨_, hl⟩
        · exact Or.inl (hl ▸ hw)
        · exact Or.inr hl
      · rcases hends with ⟨_, hr⟩ | ⟨hr, _⟩
        · exact Or.inr hr
        · exact Or.inl (hr ▸ hw)
    · obtain ⟨c, -, hc⟩ := ih
      refine ⟨c, fun h' => absurd h' hw, Relation.ReflTransGen.head ⟨e, ?_, hends⟩ hc⟩
      rw [offPathTo, Finset.mem_filter]
      refine ⟨heA, hepath, ?_, ?_⟩
      · rcases hends with ⟨hl, _⟩ | ⟨_, hl⟩
        · exact Or.inl (hl ▸ hw)
        · exact Or.inl (hl ▸ hw')
      · rcases hends with ⟨_, hr⟩ | ⟨hr, _⟩
        · exact Or.inl (hr ▸ hw')
        · exact Or.inl (hr ▸ hw)

omit [Fintype V] [Fintype E] in
theorem offPathTo_subset (A : Finset E) (c : Fin (m + 1)) :
    offPathTo J path copies A c ⊆ A := Finset.filter_subset _ _

/-- An edge end at a path vertex extends, through edges avoiding that vertex, to an
arc ending at another path vertex and meeting the unit segment only at its ends. -/
theorem exists_arc_to_path_vertex (h : StraightPath D m path copies) (A : Finset E)
    {a : Fin (m + 1)} (hA : ∀ e ∈ A, J.left e ≠ path a ∧ J.right e ≠ path a)
    {e : E} (he : e ∉ range copies) {w : V} (hwa : w ≠ path a)
    (hends : (J.left e = path a ∧ J.right e = w) ∨ (J.right e = path a ∧ J.left e = w))
    (hreach : ∃ x ∈ range path, J.reaches A w x)
    (γ₀ : Path (D.point (path a)) (D.point w)) (hγ₀inj : Function.Injective γ₀)
    (hγ₀range : range γ₀ = range (D.curve e)) :
    ∃ c : Fin (m + 1), c ≠ a ∧ ∃ β : Path (D.point (path a)) (D.point (path c)),
      Function.Injective β ∧ range β ⊆ drawingTrace D ∧
      (∀ t, β t ∈ unitSeg → β t = D.point (path a) ∨ β t = D.point (path c)) ∧
      ∀ τ₀ > 0, ∃ τ > 0, ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < τ →
        ∃ s : unitInterval, 0 < (s : ℝ) ∧ (s : ℝ) < τ₀ ∧ β t = γ₀ s := by
  obtain ⟨x, hx, hr⟩ := hreach
  obtain ⟨c, hcw, hc⟩ := first_path_vertex h A hr hx
  have heA : e ∉ A := by
    intro heA
    rcases hends with ⟨hl, _⟩ | ⟨hr', _⟩
    · exact (hA e heA).1 hl
    · exact (hA e heA).2 hr'
  have hγ₀trace : range γ₀ ⊆ drawingTrace D := by
    rw [hγ₀range]
    rintro z ⟨t, rfl⟩
    exact Or.inr (mem_iUnion.mpr ⟨e, t, rfl⟩)
  -- points of the edge on the unit segment
  have hγ₀seg : ∀ z ∈ range γ₀, z ∈ unitSeg → z = D.point (path a) ∨ z = D.point w := by
    intro z hz hzs
    rw [hγ₀range] at hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨ht, -⟩ := h.nonpath_curve_on_unitSeg he hzs
    rcases ht with ht | ht
    · have : t = zeroParam := Subtype.ext ht
      rw [this, D.start]
      rcases hends with ⟨hl, _⟩ | ⟨_, hl⟩
      · exact Or.inl (by rw [hl])
      · exact Or.inr (by rw [hl])
    · have : t = oneParam := Subtype.ext ht
      rw [this, D.finish]
      rcases hends with ⟨_, hr'⟩ | ⟨hr', _⟩
      · exact Or.inr (by rw [hr'])
      · exact Or.inl (by rw [hr'])
  by_cases hwc : w = path c
  · -- the edge itself reaches the path vertex
    have hca : c ≠ a := by
      rintro rfl
      exact hwa hwc
    subst hwc
    refine ⟨c, hca, γ₀, hγ₀inj, hγ₀trace, fun t ht => hγ₀seg _ ⟨t, rfl⟩ ht, ?_⟩
    intro τ₀ hτ₀
    exact ⟨τ₀, hτ₀, fun t ht0 htτ => ⟨t, ht0, htτ, rfl⟩⟩
  · have hwpath : w ∉ range path := fun hw => hwc (hcw hw).symm
    -- the last edge of the walk is incident to the target vertex
    have hca : c ≠ a := by
      rintro rfl
      unfold CopiedGraph.reaches at hc
      rcases Relation.ReflTransGen.cases_tail hc with h1 | ⟨b, -, e', he', hends'⟩
      · exact hwc h1.symm
      · have hA' := hA e' (offPathTo_subset A c he')
        rcases hends' with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact hA'.2 h2
        · exact hA'.1 h2
    obtain ⟨Q, hQinj, hQr⟩ := exists_simple_path_on_curves D (offPathTo J path copies A c) hwc hc
    have hmeet : range γ₀ ∩ range Q = {D.point w} := by
      apply Subset.antisymm
      · rintro z ⟨hz1, hz2⟩
        obtain ⟨e', he', t', ht'⟩ := hQr hz2
        rw [hγ₀range] at hz1
        obtain ⟨s, rfl⟩ := hz1
        have hne : e ≠ e' := fun heq => heA (heq ▸ offPathTo_subset A c he')
        obtain ⟨hs, -⟩ := D.intersects e e' hne s t' ht'.symm
        rcases hs with hs | hs
        · have : s = zeroParam := Subtype.ext hs
          rw [this, D.start]
          rcases hends with ⟨hl, _⟩ | ⟨_, hl⟩
          · exfalso
            rw [this, D.start, hl] at ht'
            have hA' := hA e' (offPathTo_subset A c he')
            exact curve_ne_point_of_ne hA'.1 hA'.2 t' ht'
          · rw [hl]
            rfl
        · have : s = oneParam := Subtype.ext hs
          rw [this, D.finish]
          rcases hends with ⟨_, hr'⟩ | ⟨hr', _⟩
          · rw [hr']
            rfl
          · exfalso
            rw [this, D.finish, hr'] at ht'
            have hA' := hA e' (offPathTo_subset A c he')
            exact curve_ne_point_of_ne hA'.1 hA'.2 t' ht'
      · rintro z hz
        rw [mem_singleton_iff] at hz
        subst hz
        exact ⟨γ₀.target_mem_range, Q.source_mem_range⟩
    refine ⟨c, hca, γ₀.trans Q, LatticeProb.Topology.path_trans_injective hγ₀inj hQinj hmeet,
      ?_, ?_, ?_⟩
    · rw [Path.trans_range]
      refine union_subset hγ₀trace ?_
      intro z hz
      obtain ⟨e', -, t', rfl⟩ := hQr hz
      exact Or.inr (mem_iUnion.mpr ⟨e', t', rfl⟩)
    · intro t ht
      have hmem : (γ₀.trans Q) t ∈ range γ₀ ∪ range Q := by
        rw [← Path.trans_range]
        exact ⟨t, rfl⟩
      rcases hmem with hz | hz
      · rcases hγ₀seg _ hz ht with h1 | h1
        · exact Or.inl h1
        · exact absurd (h1 ▸ ht) (h.nonpath_point_not_mem_unitSeg hwpath)
      · obtain ⟨e', he', t', ht'⟩ := hQr hz
        rw [offPathTo, Finset.mem_filter] at he'
        obtain ⟨-, hep, hl, hr'⟩ := he'
        obtain ⟨-, j, hj⟩ := h.nonpath_curve_on_unitSeg hep (ht' ▸ ht)
        right
        rw [← ht', hj]
        rcases (D.curve_vertex_iff e' t' (path j)).mp hj with ⟨_, h2⟩ | ⟨_, h2⟩
        · rcases hl with hl | hl
          · exact absurd ⟨j, h2.symm⟩ hl
          · rw [← h2, hl]
        · rcases hr' with hr' | hr'
          · exact absurd ⟨j, h2.symm⟩ hr'
          · rw [← h2, hr']
    · intro τ₀ hτ₀
      refine ⟨min (τ₀ / 2) (1 / 2), lt_min (by linarith) (by norm_num), ?_⟩
      intro t ht0 htτ
      have ht2 : (t : ℝ) ≤ 1 / 2 := le_trans htτ.le (min_le_right _ _)
      refine ⟨⟨2 * t, by constructor <;> nlinarith [t.2.1]⟩, by
        show (0 : ℝ) < 2 * t; linarith, by
        show 2 * (t : ℝ) < τ₀; have := min_le_left (τ₀ / 2) (1 / 2); linarith, ?_⟩
      rw [Path.trans_apply, dif_pos ht2]

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
