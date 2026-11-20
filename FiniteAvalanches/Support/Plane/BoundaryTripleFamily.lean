import FiniteAvalanches.Support.Plane.BoundaryThreeCases

/-!
# Indexed triples of boundary arms

A three-element family of boundary accesses admits separated rooted arms when
no boundary endpoint occurs three times.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A three-element family of boundary accesses admits separated arms with
exact terminal speeds if no endpoint occurs three times. -/
theorem exists_boundary_arm_family_of_card_eq_three
    {ι : Type*} {U S : Set (ℝ × ℝ)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (s : Finset ι) (hcard : s.card = 3) {x y : ι → ℝ × ℝ}
    (p : ∀ i, Path (x i) (y i)) (hp : ∀ i ∈ s, Function.Injective (p i))
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
      (∀ i ∈ s, ∃ u : unitInterval, u ≠ 1 ∧ ∀ (t : unitInterval)
        (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
        w i t = p i ⟨2 * (t : ℝ) - 1, by
          constructor <;> linarith [u.property.1, t.property.2]⟩) := by
  classical
  obtain ⟨i, j, k, hij, hik, hjk, hs⟩ := Finset.card_eq_three.mp hcard
  have hi : i ∈ s := by rw [hs]; simp
  have hj : j ∈ s := by rw [hs]; simp
  have hk : k ∈ s := by rw [hs]; simp
  obtain ⟨r, hr, v, w, z, hv, hw, hz, hvS, hwS, hzS, hvU, hwU, hzU,
      hvw, hvz, hwz, hvt, hwt, hzt⟩ :=
    exists_three_boundary_arms_of_endpoint_multiplicity_le_two hU hconn (p i) (p j) (p k)
      (hp i hi) (hp j hj) (hp k hk) (hd i hi j hj hij) (hd i hi k hk hik)
      (hd j hj k hk hjk) (hinside i hi) (hinside j hj) (hinside k hk)
      (hout i hi) (hout j hj) (hout k hk) hS (hobs i hi) (hobs j hj) (hobs k hk)
      (hmult i hi j hj k hk hij hik hjk)
  let arm : ∀ l, Path r (y l) := fun l =>
    if hli : l = i then hli.symm ▸ v else if hlj : l = j then hlj.symm ▸ w
    else if hlk : l = k then hlk.symm ▸ z else Path.segment r (y l)
  have harmi : arm i = v := by simp [arm]
  have harmj : arm j = w := by simp [arm, hij.symm]
  have harmk : arm k = z := by simp [arm, hik.symm, hjk.symm]
  have hcases : ∀ l ∈ s, l = i ∨ l = j ∨ l = k := by
    intro l hl
    rw [hs] at hl
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hl
  refine ⟨r, hr, arm, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    rcases hcases l hl with rfl | rfl | rfl
    · simpa only [harmi] using hv
    · simpa only [harmj] using hw
    · simpa only [harmk] using hz
  · intro l hl
    rcases hcases l hl with rfl | rfl | rfl
    · simpa only [harmi] using hvS
    · simpa only [harmj] using hwS
    · simpa only [harmk] using hzS
  · intro l hl
    rcases hcases l hl with rfl | rfl | rfl
    · simpa only [harmi] using hvU
    · simpa only [harmj] using hwU
    · simpa only [harmk] using hzU
  · intro l hl m hm hlm a ha
    rcases hcases l hl with rfl | rfl | rfl <;>
      rcases hcases m hm with rfl | rfl | rfl
    · exact (hlm rfl).elim
    · exact hvw a (by simpa only [harmi, harmj] using ha)
    · exact hvz a (by simpa only [harmi, harmk] using ha)
    · rcases hvw a (by simpa only [harmi, harmj, inter_comm] using ha) with h | ⟨h, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨h.trans he, he.symm⟩
    · exact (hlm rfl).elim
    · exact hwz a (by simpa only [harmj, harmk] using ha)
    · rcases hvz a (by simpa only [harmi, harmk, inter_comm] using ha) with h | ⟨h, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨h.trans he, he.symm⟩
    · rcases hwz a (by simpa only [harmj, harmk, inter_comm] using ha) with h | ⟨h, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨h.trans he, he.symm⟩
    · exact (hlm rfl).elim
  · intro l hl
    rcases hcases l hl with rfl | rfl | rfl
    · simpa only [harmi] using hvt
    · simpa only [harmj] using hwt
    · simpa only [harmk] using hzt

end FiniteAvalanches.Electrical.StatementGeometry
