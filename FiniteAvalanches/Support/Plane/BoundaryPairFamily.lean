import FiniteAvalanches.Support.Plane.BoundaryPairArms

/-!
# Indexed pairs of boundary arms

A pair of boundary accesses indexed by a finite set admits a uniformly
parametrized family of separated arms.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A two-element family of boundary accesses admits rooted arms with exact
terminal speed, separated except at their root and shared boundary endpoints. -/
theorem exists_boundary_arm_family_of_card_eq_two
    {ι : Type*} {U S : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) (hcard : s.card = 2) {x y : ι → ℝ × ℝ}
    (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U) (hS : S.Finite)
    (hobs : ∀ i ∈ s, Disjoint (range (p i)) S) :
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
  classical
  obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hcard
  have hi : i ∈ s := by rw [hs]; simp
  have hj : j ∈ s := by rw [hs]; simp
  obtain ⟨r, hr, v, w, hv, hw, hvS, hwS, hvw, hvU, hwU, hvt, hwt⟩ :=
    exists_two_boundary_arms_of_disjoint_inside hU hconn (p i) (p j) (hp i hi) (hp j hj)
      (hd i hi j hj hij) (hinside i hi) (hinside j hj) (hout i hi) (hout j hj)
      hS (hobs i hi) (hobs j hj)
  let arm : ∀ k, Path r (y k) := fun k =>
    if hk : k = i then hk.symm ▸ v else if hk' : k = j then hk'.symm ▸ w
    else Path.segment r (y k)
  have harmi : arm i = v := by simp [arm]
  have harmj : arm j = w := by simp [arm, hij.symm]
  have hcases : ∀ k ∈ s, k = i ∨ k = j := by
    intro k hk
    rw [hs] at hk
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hk
  refine ⟨r, hr, arm, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases hcases k hk with rfl | rfl
    · simpa only [harmi] using hv
    · simpa only [harmj] using hw
  · intro k hk
    rcases hcases k hk with rfl | rfl
    · simpa only [harmi] using hvS
    · simpa only [harmj] using hwS
  · intro k hk
    rcases hcases k hk with rfl | rfl
    · simpa only [harmi] using hvU
    · simpa only [harmj] using hwU
  · intro k hk l hl hkl z hz
    rcases hcases k hk with rfl | rfl <;> rcases hcases l hl with rfl | rfl
    · exact (hkl rfl).elim
    · exact hvw z (by simpa only [harmi, harmj] using hz)
    · have hz' : z ∈ range v ∩ range w := by
        simpa only [harmi, harmj, inter_comm] using hz
      rcases hvw z hz' with hz | ⟨hz, he⟩
      · exact Or.inl hz
      · exact Or.inr ⟨hz.trans he, he.symm⟩
    · exact (hkl rfl).elim
  · intro k hk
    rcases hcases k hk with rfl | rfl
    · simpa only [harmi] using hvt
    · simpa only [harmj] using hwt

end FiniteAvalanches.Electrical.StatementGeometry
