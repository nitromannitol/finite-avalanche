import FiniteAvalanches.Support.Plane.BoundarySmallFamily
import FiniteAvalanches.Support.Plane.BoundaryTripleFamily

/-!
# Small indexed families of boundary arms

Families of at most three boundary accesses admit separated rooted arms when
no endpoint occurs three times.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- At most three boundary accesses admit separated arms with exact terminal
speeds when no boundary endpoint occurs three times. -/
theorem exists_boundary_arm_family_of_card_le_three
    {ι : Type*} {U S : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hUne : U.Nonempty) (s : Finset ι) (hcard : s.card ≤ 3) {x y : ι → ℝ × ℝ}
    (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U) (hS : S.Finite)
    (hobs : ∀ i ∈ s, Disjoint (range (p i)) S)
    (hmult : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, i ≠ j → i ≠ k → j ≠ k →
      ¬ (y i = y j ∧ y i = y k)) :
    ∃ r ∈ U, ∃ w : ∀ i, Path r (y i),
      (∀ i ∈ s, Function.Injective (w i)) ∧
      (∀ i ∈ s, Disjoint (range (w i)) S) ∧
      (∀ i ∈ s, range (w i) ∩ Uᶜ = {y i}) ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ z ∈ range (w i) ∩ range (w j),
        z = r ∨ z = y i ∧ y i = y j) ∧
      (∀ i ∈ s, ∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w i t = p i ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  by_cases hthree : s.card = 3
  · exact exists_boundary_arm_family_of_card_eq_three hU hconn s hthree p hp hd
      hinside hout hS hobs hmult
  · have htwo : s.card ≤ 2 := by omega
    exact exists_boundary_arm_family_of_card_le_two hU hconn hUne s htwo p hp hd
      hinside hout hS hobs

end FiniteAvalanches.Electrical.StatementGeometry
