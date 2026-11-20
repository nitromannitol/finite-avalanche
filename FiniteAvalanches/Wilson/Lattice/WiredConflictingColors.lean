import FiniteAvalanches.Wilson.Lattice.WiredEdgeColorConsistency

/-! Finite wired observations exclude conflicting colors on selected edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The color pattern assigning opposite colors to two distinct sites. -/
def oppositeEndpointColors (x : Site 2) (c : Bool) : Site 2 → Bool :=
  fun z => if z = x then c else !c

/-- No finite wired forest selects an edge whose endpoints have opposite colors. -/
theorem wiredObservationCylinder_opposite_edge_eq_empty (R : RootPair) (B : ℕ)
    (x y : Site 2) (hxy : (lattice 2).Adj x y) (c : Bool) :
    wiredObservationCylinder R B {⟨s(x, y), hxy⟩} {x, y}
      (fun _ => true) (oppositeEndpointColors x c) = ∅ := by
  have hne : y ≠ x := by
    intro he
    subst y
    exact (lattice 2).loopless.irrefl x hxy
  ext F
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have he : finiteEdgeField R B F ⟨s(x, y), hxy⟩ = true := h.1 _ (Finset.mem_singleton_self _)
  have hx : finiteColors R B F (wiredSite B x) = c := by
    simpa only [oppositeEndpointColors, if_true] using h.2 x (Finset.mem_insert_self _ _)
  have hy : finiteColors R B F (wiredSite B y) = !c := by
    simpa only [oppositeEndpointColors, if_neg hne] using h.2 y (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  have hc := finiteForestField_edge_colors_eq R B F x y hxy he
  rw [hx, hy] at hc
  cases c <;> cases hc

/-- Opposite endpoint colors and a selected edge form a null cylinder in
every finite wired forest law. -/
theorem finiteForestLaw_opposite_edge (R : RootPair) (B : ℕ)
    (x y : Site 2) (hxy : (lattice 2).Adj x y) (c : Bool) :
    finiteForestLaw R B (jointEvent {⟨s(x, y), hxy⟩} {x, y}
      (fun _ => true) (oppositeEndpointColors x c)) = 0 := by
  rw [finiteForestLaw_jointEvent, wiredObservationCylinder_opposite_edge_eq_empty, measure_empty]

/-- Opposite endpoint colors and a selected edge form a null cylinder in the
Wilson cylinder law. -/
theorem IsWilsonCylinderLaw.opposite_edge_measure_zero (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν)
    (x y : Site 2) (hxy : (lattice 2).Adj x y) (c : Bool) :
    (ν : Measure ForestField) (jointEvent {⟨s(x, y), hxy⟩} {x, y}
      (fun _ => true) (oppositeEndpointColors x c)) = 0 := by
  let q : ℕ → Site 2 := fun i => if i = 0 then x else y
  let E : Finset LatticeEdge := {⟨s(x, y), hxy⟩}
  let D : Finset (Site 2) := {x, y}
  let pe : LatticeEdge → Bool := fun _ => true
  let pc := oppositeEndpointColors x c
  have hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < 2, q i = z := by
    intro e he z hz
    have heq : e = ⟨s(x, y), hxy⟩ := Finset.mem_singleton.mp he
    subst e
    change z ∈ s(x, y) at hz
    rcases Sym2.mem_iff.mp hz with hz | hz
    · refine ⟨0, by omega, ?_⟩
      simpa only [q, if_true] using hz.symm
    · refine ⟨1, by omega, ?_⟩
      simpa only [q, one_ne_zero, if_false] using hz.symm
  have hD : ∀ z ∈ D, ∃ i < 2, q i = z := by
    intro z hz
    simp only [D, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
  have ht := finiteForestLaw_jointEvent_tendsto R q (fun _ => 0) (fun _ _ => 0)
    2 E D pe pc hE hD
  have hz : (fun B : ℕ => finiteForestLaw R B (jointEvent E D pe pc)) = fun _ => 0 := by
    funext B
    exact finiteForestLaw_opposite_edge R B x y hxy c
  rw [hz] at ht
  have hsample := tendsto_nhds_unique ht tendsto_const_nhds
  exact (hν q 2 E D pe pc hE hD).trans hsample

/-- Almost surely, the endpoints of every selected lattice edge have the same color. -/
theorem IsWilsonCylinderLaw.ae_edge_colors (R : RootPair)
    (ν : ProbabilityMeasure ForestField) (hν : IsWilsonCylinderLaw R ν) :
    ∀ᵐ ω ∂(ν : Measure ForestField), ∀ x y (hxy : (lattice 2).Adj x y),
      ω.1 ⟨s(x, y), hxy⟩ = true → ω.2 x = ω.2 y := by
  apply ae_all_iff.mpr
  intro x
  apply ae_all_iff.mpr
  intro y
  by_cases hxy : (lattice 2).Adj x y
  · have hne : y ≠ x := by
      intro he
      subst y
      exact (lattice 2).loopless.irrefl x hxy
    have h0 := (measure_eq_zero_iff_ae_notMem).mp
      (hν.opposite_edge_measure_zero R ν x y hxy false)
    have h1 := (measure_eq_zero_iff_ae_notMem).mp
      (hν.opposite_edge_measure_zero R ν x y hxy true)
    filter_upwards [h0, h1] with ω h0ω h1ω hxy' he
    cases hx : ω.2 x <;> cases hy : ω.2 y
    · rfl
    · exfalso
      apply h0ω
      simp [jointEvent, oppositeEndpointColors, hx, hy, hne, he]
    · exfalso
      apply h1ω
      simp [jointEvent, oppositeEndpointColors, hx, hy, hne, he]
    · rfl
  · exact Filter.Eventually.of_forall (fun _ hxy' => (hxy hxy').elim)

end
end FiniteAvalanches.Wilson.Lattice
