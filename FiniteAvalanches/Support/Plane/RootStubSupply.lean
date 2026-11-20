import FiniteAvalanches.Support.Plane.BoundaryProtectedFamily

/-!
# Finite supplies of root stubs

An open plane neighborhood of a point contains arbitrarily many simple paths
that meet pairwise only at that point.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- Every open neighborhood of a plane point contains a finite family of
injective paths to that point, with pairwise intersections equal to the root. -/
theorem exists_root_stub_supply {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    {r : ℝ × ℝ} (hr : r ∈ W) (n : ℕ) :
    ∃ (q : Fin n → ℝ × ℝ) (p : ∀ i, Path (q i) r),
      (∀ i, q i ≠ r) ∧
      (∀ i, Function.Injective (p i)) ∧
      (∀ i, range (p i) ⊆ W) ∧
      (∀ i j, i ≠ j → range (p i) ∩ range (p j) = {r}) := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW r hr
  let e := (Set.Ioo_infinite hε).natEmbedding
  let q : Fin n → ℝ × ℝ := fun i => (r.1 + (e i.val).val, r.2)
  have hqball : ∀ i, q i ∈ Metric.ball r ε := by
    intro i
    have ht := (e i.val).property
    change dist (r.1 + (e i.val).val, r.2) (r.1, r.2) < ε
    rw [dist_prod_same_right, Real.dist_eq]
    have : r.1 + (e i.val).val - r.1 = (e i.val).val := by ring
    rw [this, abs_of_pos ht.1]
    exact ht.2
  have hqr : ∀ i, q i ≠ r := by
    intro i h
    have hzero : (e i.val).val = 0 := by
      have hh := congrArg Prod.fst h
      dsimp only [q] at hh
      linarith
    exact (ne_of_gt (e i.val).property.1) hzero
  have hqinj : Function.Injective q := by
    intro i j h
    have ht : (e i.val).val = (e j.val).val := by
      have hh := congrArg Prod.fst h
      dsimp only [q] at hh
      linarith
    exact Fin.ext (e.injective (Subtype.ext ht))
  obtain ⟨p, hp, hpW, hpair⟩ := exists_disjoint_path_star
    (U := Metric.ball r ε) (S := ∅) (r := r) (x := q)
    Metric.isOpen_ball (convex_ball r ε).isPreconnected (Finset.univ : Finset (Fin n))
    (Set.finite_empty) (by simpa using (Metric.mem_ball_self hε : r ∈ Metric.ball r ε))
    (by simpa using hqball) (by simpa using hqr)
    (by simpa using fun i j hij => hqinj.ne hij)
  refine ⟨q, p, hqr, ?_, ?_, ?_⟩
  · intro i
    exact hp i (Finset.mem_univ i)
  · intro i
    exact (hpW i (Finset.mem_univ i)).trans (by simpa using hball)
  · intro i j hij
    exact hpair i (Finset.mem_univ i) j (Finset.mem_univ j) hij

end FiniteAvalanches.Electrical.StatementGeometry
