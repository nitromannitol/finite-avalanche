import FiniteAvalanches.Sandpile.Components.Incident

/-! Exact retained-direction uniqueness consumed on the full induced incident carriers. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem inner_retained_direction_unique {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : FiniteWired.Active N // FiniteWired.site x ∈ C.val})
    (e : FiniteWired.Edge N)
    (he : e ∈ inducedIncidentCopies {v | insideVertex C.val v} x.val) :
    ∃! d : {d : FiniteWired.Direction // d ∈ innerDirections C.val (FiniteWired.site x.val)},
      FiniteWired.directionEdge x.val d.val = e := by
  rw [← inner_incident_copies_eq C x] at he
  obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp he
  refine ⟨⟨d, hd⟩, hde, ?_⟩
  intro d' hd'
  apply Subtype.ext
  exact direction_edge_injective x.val (hd'.trans hde.symm)

theorem outer_retained_direction_unique {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (x : {x : FiniteWired.Active N // FiniteWired.site x ∉ C.val})
    (e : FiniteWired.Edge N)
    (he : e ∈ inducedIncidentCopies {v | outsideVertex C.val v} x.val) :
    ∃! d : {d : FiniteWired.Direction // d ∈ outerDirections C.val (FiniteWired.site x.val)},
      FiniteWired.directionEdge x.val d.val = e := by
  rw [← outer_incident_copies_eq C x] at he
  obtain ⟨d, hd, hde⟩ := Finset.mem_image.mp he
  refine ⟨⟨d, hd⟩, hde, ?_⟩
  intro d' hd'
  apply Subtype.ext
  exact direction_edge_injective x.val (hd'.trans hde.symm)

end
end FiniteAvalanches.Sandpile.Components
