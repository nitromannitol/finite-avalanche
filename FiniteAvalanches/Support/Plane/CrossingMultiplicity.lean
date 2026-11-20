import FiniteAvalanches.Support.Plane.CrossingStubSeparation

/-!
# Multiplicity of crossing endpoints

At most two crossing sides share a midpoint: they are the two sides of the
same edge copy.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two coincident crossing midpoints belong to the same edge copy. -/
theorem crossing_midpoint_edge_eq {E X : Type*} [TopologicalSpace X]
    (q : E → unitInterval → X)
    (hd : ∀ e f, e ≠ f → Disjoint (range (q e)) (range (q f)))
    {e f : E} (h : q e ⟨1 / 2, by norm_num⟩ = q f ⟨1 / 2, by norm_num⟩) : e = f := by
  by_contra hne
  exact disjoint_left.mp (hd e f hne) ⟨⟨1 / 2, by norm_num⟩, rfl⟩
    ⟨⟨1 / 2, by norm_num⟩, h.symm⟩

/-- Three distinct crossing sides cannot share one midpoint. -/
theorem not_three_crossing_sides_same_midpoint {E X : Type*} [TopologicalSpace X]
    (q : E → unitInterval → X)
    (hd : ∀ e f, e ≠ f → Disjoint (range (q e)) (range (q f)))
    {i j k : E × Bool} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ (q i.1 ⟨1 / 2, by norm_num⟩ = q j.1 ⟨1 / 2, by norm_num⟩ ∧
      q i.1 ⟨1 / 2, by norm_num⟩ = q k.1 ⟨1 / 2, by norm_num⟩) := by
  rintro ⟨hij', hik'⟩
  have heij := crossing_midpoint_edge_eq q hd hij'
  have heik := crossing_midpoint_edge_eq q hd hik'
  rcases i with ⟨e, a⟩
  rcases j with ⟨f, b⟩
  rcases k with ⟨g, c⟩
  dsimp only at heij heik
  subst f
  subst g
  cases a <;> cases b <;> cases c <;> simp_all

end FiniteAvalanches.Electrical.StatementGeometry
