import FiniteAvalanches.Support.Plane.CrossingStarAssembly
import FiniteAvalanches.Support.Plane.CrossingStubSeparation

/-!
# Assembly of crossing stub tails

A separated family of approaches to crossing stubs yields simple crossing arms
with the prescribed terminal speed.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

private theorem subpath_injective_of_injective {X : Type*} [TopologicalSpace X]
    {x y : X} (q : Path x y) (hq : Function.Injective q)
    (u : unitInterval) (hu : u ≠ 1) :
    Function.Injective (q.subpath u 1) := by
  intro a b hab
  have h := congrArg Subtype.val (hq hab)
  simp only [Set.Icc.coe_convexComb] at h
  norm_num at h
  have hu' : (u : ℝ) ≠ 1 := fun h => hu (Subtype.ext h)
  apply Subtype.ext
  have heq : ((a : ℝ) - b) * (1 - (u : ℝ)) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right (sub_ne_zero.mpr (Ne.symm hu')))

/-- Separated paths to distinct crossing stubs assemble into separated arms
following the original stub parametrization near their endpoints. -/
theorem exists_separated_arms_of_stub_approaches {E X : Type*} [TopologicalSpace X]
    (s : Finset (E × Bool)) (q : E → unitInterval → X)
    (hq : ∀ e, Continuous (q e)) (hinj : ∀ e, Function.Injective (q e))
    (hd : ∀ e f, e ≠ f → Disjoint (range (q e)) (range (q f)))
    {r : X} (u : E × Bool → unitInterval)
    (p : ∀ i : E × Bool, Path r (midpointStub (q i.1) (hq i.1) i.2 (u i)))
    (hu : ∀ i ∈ s, u i ≠ 1) (hp : ∀ i ∈ s, Function.Injective (p i))
    (hjoin : ∀ i ∈ s, range (p i) ∩
      range ((midpointStub (q i.1) (hq i.1) i.2).subpath (u i) 1) =
        {midpointStub (q i.1) (hq i.1) i.2 (u i)})
    (hpp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (p i) ∩ range (p j) ⊆ {r})
    (hpq : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (range (p i))
      (range ((midpointStub (q j.1) (hq j.1) j.2).subpath (u j) 1))) :
    ∃ w : ∀ i : E × Bool, Path r (q i.1 ⟨1 / 2, by norm_num⟩),
      (∀ i ∈ s, Function.Injective (w i)) ∧
      (∀ i ∈ s, range (w i) = range (p i) ∪
        range ((midpointStub (q i.1) (hq i.1) i.2).subpath (u i) 1)) ∧
      (∀ i ∈ s, ∀ (t : unitInterval) (ht : ((u i : ℝ) + 1) / 2 ≤ (t : ℝ)),
        w i t = midpointStub (q i.1) (hq i.1) i.2 ⟨2 * (t : ℝ) - 1, by
          constructor
          · have := (u i).property.1
            linarith
          · linarith [t.property.2]⟩) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → range (w i) ∩ range (w j) ⊆
        {r} ∪ ({q i.1 ⟨1 / 2, by norm_num⟩} ∩ {q j.1 ⟨1 / 2, by norm_num⟩})) := by
  let stub : ∀ i : E × Bool, Path (q i.1 (crossingStubParameter i.2 0))
      (q i.1 ⟨1 / 2, by norm_num⟩) := fun i => midpointStub (q i.1) (hq i.1) i.2
  have hstub : ∀ i, Function.Injective (stub i) := fun i =>
    crossingStub_injective (q i.1) (hq i.1) (hinj i.1) i.2
  obtain ⟨w, hw, hwrange, hwtail, hwsep⟩ :=
    exists_separated_paths_with_terminal_subpaths s stub u p hu hp
      (fun i hi => subpath_injective_of_injective (stub i) (hstub i) (u i) (hu i hi))
      hjoin hpp hpq (fun i _ j _ hij => by
        simpa only [stub, Path.target] using midpointStub_subpath_inter_subset q hq hinj hd u hij)
  let w' : ∀ i : E × Bool, Path r (q i.1 ⟨1 / 2, by norm_num⟩) :=
    fun i => (w i).cast rfl (stub i).target.symm
  refine ⟨w', hw, hwrange, hwtail, ?_⟩
  intro i hi j hj hij
  simpa only [w', Path.cast_coe, Path.target] using hwsep i hi j hj hij

end FiniteAvalanches.Electrical.StatementGeometry
