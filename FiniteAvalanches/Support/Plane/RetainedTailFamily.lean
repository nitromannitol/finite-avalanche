import FiniteAvalanches.Support.Plane.RetainedTailReparam

/-!
# Families of parametrized retained tails

Retained terminal subarcs in a family of simple paths can be parametrized
simultaneously without enlarging any of the path ranges.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A finite family of simple paths containing prescribed terminal subarcs
admits exact terminal speeds while retaining every range-based constraint. -/
theorem exists_family_with_parametrized_retained_tails
    {ι X : Type*} [TopologicalSpace X] [T2Space X] (s : Finset ι)
    {r x y : ι → X} (a : ∀ i, Path (r i) (y i)) (p : ∀ i, Path (x i) (y i))
    (ha : ∀ i ∈ s, Function.Injective (a i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (htail : ∀ i ∈ s, ∃ t : unitInterval, t ≠ 1 ∧
      range ((p i).subpath t 1) ⊆ range (a i)) :
    ∃ w : ∀ i, Path (r i) (y i),
      (∀ i ∈ s, Function.Injective (w i)) ∧
      (∀ i ∈ s, range (w i) ⊆ range (a i)) ∧
      (∀ i ∈ s, ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w i t = p i ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  classical
  have hex : ∀ i, ∃ w : Path (r i) (y i), i ∈ s →
      Function.Injective w ∧ range w ⊆ range (a i) ∧
      ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = p i ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩ := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨t, ht, hsub⟩ := htail i hi
      obtain ⟨w, hw, hwsub, u, hu, hspeed⟩ :=
        exists_path_with_parametrized_retained_tail (a i) (p i) (ha i hi) (hp i hi) ht hsub
      exact ⟨w, fun _ => ⟨hw, hwsub, u, hu, hspeed⟩⟩
    · exact ⟨a i, fun h => (hi h).elim⟩
  choose w hw using hex
  exact ⟨w, fun i hi => (hw i hi).1, fun i hi => (hw i hi).2.1,
    fun i hi => (hw i hi).2.2⟩

end FiniteAvalanches.Electrical.StatementGeometry
