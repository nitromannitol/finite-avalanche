import FiniteAvalanches.Trees.Lattice.ConditionalMeasurability
set_option autoImplicit false
open LatticeProb FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice
namespace IndependentConditional10

/-- Exactly the selected connecting-tree edges, finite vertex set and entire ray
are observed; proof witnesses carry no further information. -/
theorem observation_data_iff (b b' : BranchObservation) :
    b = b' ↔ b.val.1 = b'.val.1 ∧ b.val.2.sites = b'.val.2.sites ∧
      b.val.2.ray.vertex = b'.val.2.ray.vertex := by
  constructor
  · rintro rfl
    exact ⟨rfl,rfl,rfl⟩
  · intro h
    rcases b with ⟨⟨f,⟨K,r,hK,hr⟩⟩,hb⟩
    rcases b' with ⟨⟨f',⟨K',r',hK',hr'⟩⟩,hb'⟩
    dsimp only at h
    obtain ⟨rfl,rfl,hv⟩ := h
    have he := simpleRay_eq_of_vertex_eq r r' hv
    cases he
    rfl

theorem actual_observation_dictionary (S : Finset (Site 2)) (hS : S.Nonempty)
    (t t' : TreeOutcome) :
    sourceObservation S hS t = sourceObservation S hS t' ↔
      connectingBranchField S hS t = connectingBranchField S hS t' ∧
      connectingSites t.val t.property.1 t.property.2 S hS =
        connectingSites t'.val t'.property.1 t'.property.2 S hS ∧
      (orientedRay t.val t.property.1 t.property.2
        (earliestCommonAncestor t.val t.property.1 t.property.2 S hS)).vertex =
      (orientedRay t'.val t'.property.1 t'.property.2
        (earliestCommonAncestor t'.val t'.property.1 t'.property.2 S hS)).vertex :=
  observation_data_iff _ _

end IndependentConditional10