import FiniteAvalanches.Electrical.Geometry.SimpleChain
import FiniteAvalanches.Support.Plane.TerminalReparam

/-!
# Assembly of crossing stars

Separated approach paths and boundary tails concatenate to a separated star
with a prescribed terminal parametrization.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Separated approach paths can be joined to separated terminal subpaths while
retaining injectivity, separation, and the original terminal speed. -/
theorem exists_separated_paths_with_terminal_subpaths
    {ι X : Type*} [TopologicalSpace X] (s : Finset ι)
    {r : X} {x y : ι → X} (q : ∀ i, Path (x i) (y i))
    (u : ι → unitInterval) (p : ∀ i, Path r (q i (u i)))
    (hu : ∀ i ∈ s, u i ≠ 1)
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hq : ∀ i ∈ s, Function.Injective ((q i).subpath (u i) 1))
    (hjoin : ∀ i ∈ s, range (p i) ∩ range ((q i).subpath (u i) 1) = {q i (u i)})
    (hpp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) ⊆ {r})
    (hpq : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i))
      (range ((q j).subpath (u j) 1)))
    (hqq : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      range ((q i).subpath (u i) 1) ∩ range ((q j).subpath (u j) 1) ⊆
        {q i 1} ∩ {q j 1}) :
    ∃ w : ∀ i, Path r (q i 1),
      (∀ i ∈ s, Function.Injective (w i)) ∧
      (∀ i ∈ s, range (w i) = range (p i) ∪ range ((q i).subpath (u i) 1)) ∧
      (∀ i ∈ s, ∀ (t : unitInterval) (ht : ((u i : ℝ) + 1) / 2 ≤ (t : ℝ)),
        w i t = q i ⟨2 * (t : ℝ) - 1, by
          constructor
          · have := (u i).property.1
            linarith
          · linarith [t.property.2]⟩) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (w i) ∩ range (w j) ⊆
        {r} ∪ ({q i 1} ∩ {q j 1})) := by
  classical
  have hex : ∀ i, ∃ w : Path r (q i 1), i ∈ s →
      Function.Injective w ∧
      range w = range (p i) ∪ range ((q i).subpath (u i) 1) ∧
      ∀ (t : unitInterval) (ht : ((u i : ℝ) + 1) / 2 ≤ (t : ℝ)),
        w t = q i ⟨2 * (t : ℝ) - 1, by
          constructor
          · have := (u i).property.1
            linarith
          · linarith [t.property.2]⟩ := by
    intro i
    by_cases hi : i ∈ s
    · have hinj : Function.Injective ((p i).trans ((q i).subpath (u i) 1)) :=
        path_trans_injective (p i) ((q i).subpath (u i) 1) (hp i hi) (hq i hi) (by
          intro a b hab
          have hz : p i a ∈ ({q i (u i)} : Set X) := by
            rw [← hjoin i hi]
            exact ⟨⟨a, rfl⟩, ⟨b, hab.symm⟩⟩
          exact mem_singleton_iff.mp hz)
      obtain ⟨w, hw, hwrange, hwtail⟩ :=
        path_trans_subpath_reparam_terminal (q i) (u i) (hu i hi) (p i) hinj
      exact ⟨w, fun _ => ⟨hw, by simpa only [Path.trans_range] using hwrange, hwtail⟩⟩
    · exact ⟨(p i).trans ((q i).subpath (u i) 1), fun h => (hi h).elim⟩
  choose w hw using hex
  refine ⟨w, fun i hi => (hw i hi).1, fun i hi => (hw i hi).2.1,
    fun i hi => (hw i hi).2.2, ?_⟩
  intro i hi j hj hij z hz
  rw [(hw i hi).2.1, (hw j hj).2.1] at hz
  rcases hz with ⟨hpi | hqi, hpj | hqj⟩
  · exact Or.inl (hpp i hi j hj hij ⟨hpi, hpj⟩)
  · exact (disjoint_left.mp (hpq i hi j hj hij) hpi hqj).elim
  · exact (disjoint_left.mp (hpq j hj i hi hij.symm) hpj hqi).elim
  · exact Or.inr (hqq i hi j hj hij ⟨hqi, hqj⟩)

end FiniteAvalanches.Electrical.StatementGeometry
