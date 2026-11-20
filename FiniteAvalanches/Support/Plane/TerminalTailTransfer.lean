import FiniteAvalanches.Support.Plane.TwoArcReroot

/-!
# Transfer of terminal subpaths

A terminal subarc contained in a simple path can be shortened to fit inside
any prescribed terminal subarc of that path.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- The initial part of a reversed path is its terminal subpath. -/
theorem range_reverse_initial_subpath {X : Type*} [TopologicalSpace X]
    {a b : X} (p : Path a b) (t : unitInterval) :
    range (p.symm.subpath 0 (unitInterval.symm t)) = range (p.subpath t 1) := by
  rw [Path.range_subpath_of_le p.symm 0 (unitInterval.symm t) bot_le,
    Path.range_subpath_of_le p t 1 le_top]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨unitInterval.symm u, ?_, rfl⟩
    constructor
    · change (t : ℝ) ≤ 1 - (u : ℝ)
      have h : (u : ℝ) ≤ 1 - (t : ℝ) := hu.2
      linarith
    · exact le_top
  · rintro ⟨u, hu, rfl⟩
    refine ⟨unitInterval.symm u, ?_, ?_⟩
    · constructor
      · exact bot_le
      · change 1 - (u : ℝ) ≤ 1 - (t : ℝ)
        have h : (t : ℝ) ≤ u := hu.1
        linarith
    · change p (unitInterval.symm (unitInterval.symm u)) = p u
      rw [unitInterval.symm_symm]

/-- A terminal subarc of one simple path that lies in another can be
shortened into any nondegenerate terminal subarc of the latter. -/
theorem exists_terminal_subpath_subset_terminal_subpath
    {X : Type*} [TopologicalSpace X] [T2Space X] {a b c : X}
    (p : Path a b) (q : Path c b) (hp : Function.Injective p)
    {s t : unitInterval} (hs : s ≠ 1) (ht : t ≠ 1)
    (hsub : range (q.subpath s 1) ⊆ range p) :
    ∃ u : unitInterval, u ≠ 1 ∧ range (q.subpath u 1) ⊆ range (p.subpath t 1) := by
  have ht' : unitInterval.symm t ≠ 0 := by
    intro h
    apply ht
    apply unitInterval.symm_involutive.injective
    simpa using h
  obtain ⟨u, hu, htail⟩ := terminal_subpath_in_initial_reverse p q hp hs ht' hsub
  exact ⟨u, hu, (range_reverse_initial_subpath p t) ▸ htail⟩

end FiniteAvalanches.Electrical.StatementGeometry
