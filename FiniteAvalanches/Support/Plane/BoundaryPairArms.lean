import FiniteAvalanches.Support.Plane.ParametrizedBoundaryBridge

/-!
# Pairs of boundary arms

Two boundary accesses that are disjoint inside a region admit separated arms,
including when the accesses share their boundary endpoint.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two accesses disjoint inside an open connected region admit arms with exact
terminal speed, intersecting only at their root or a shared boundary endpoint. -/
theorem exists_two_boundary_arms_of_disjoint_inside
    {U S : Set (ℝ × ℝ)} {a b c d : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Path a b) (q : Path c d) (hp : Function.Injective p)
    (hq : Function.Injective q) (hd : Disjoint (range p ∩ U) (range q))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hb : b ∉ U) (hd' : d ∉ U) (hS : S.Finite)
    (hpS : Disjoint (range p) S) (hqS : Disjoint (range q) S) :
    ∃ r ∈ U, ∃ (v : Path r b) (w : Path r d),
      Function.Injective v ∧ Function.Injective w ∧
      Disjoint (range v) S ∧ Disjoint (range w) S ∧
      (∀ z ∈ range v ∩ range w, z = r ∨ z = b ∧ b = d) ∧
      range v ∩ Uᶜ = {b} ∧ range w ∩ Uᶜ = {d} ∧
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          v t = p ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) ∧
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = q ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  by_cases hbd : b = d
  · subst d
    obtain ⟨r, hr, v, w, hv, hw, hvS, hwS, hinter, hvU, hwU, hvt, hwt⟩ :=
      exists_two_boundary_arms_common_endpoint hU hconn p q hp hq hd hpU hqU hb hS hpS hqS
    refine ⟨r, hr, v, w, hv, hw, hvS, hwS, ?_, hvU, hwU, hvt, hwt⟩
    intro z hz
    rw [hinter] at hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, rfl⟩
  · have hdis : Disjoint (range p) (range q) := by
      apply disjoint_left.mpr
      intro z hz hzq
      by_cases hzU : z ∈ U
      · exact disjoint_left.mp hd ⟨hz, hzU⟩ hzq
      · obtain ⟨t, rfl⟩ := hz
        have ht : t = 1 := by
          by_contra ht
          exact hzU (hpU t ht)
        have hzq' : b ∈ range q := by simpa only [ht, Path.target] using hzq
        obtain ⟨u, hu⟩ := hzq'
        have hu1 : u = 1 := by
          by_contra hu1
          exact hb (hu ▸ hqU u hu1)
        have heq : d = b := by simpa only [hu1, Path.target] using hu
        exact hbd heq.symm
    obtain ⟨r, hr, v, w, hv, hw, hvS, hwS, hinter, hvU, hwU, hvt, hwt⟩ :=
      exists_two_boundary_arms_with_parametrized_tails hU hconn p q hp hq hdis hpU hqU
        hb hd' hS hpS hqS
    refine ⟨r, hr, v, w, hv, hw, hvS, hwS, ?_, hvU, hwU, hvt, hwt⟩
    intro z hz
    exact Or.inl (mem_singleton_iff.mp (hinter ▸ hz))

end FiniteAvalanches.Electrical.StatementGeometry
