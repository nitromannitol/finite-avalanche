import FiniteAvalanches.Support.Plane.DualFaceCoverage
import FiniteAvalanches.Support.Schoenflies.JordanClosed

/-!
# Finite face covers at a frontier

If finitely many sets cover a dense complement, every point in the closure of
an open set belongs to the closure of a covering set that meets the open set.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A finite cover of a dense set supplies a member incident to any boundary
point of an open set, with a point in that open set. -/
theorem exists_cover_member_at_closure {X ι : Type} [TopologicalSpace X] [Finite ι]
    (T S : Set X) (U : ι → Set X) (hdense : Dense Tᶜ)
    (hcover : Tᶜ ⊆ ⋃ i, U i) (hS : IsOpen S) {z : X} (hz : z ∈ closure S) :
    ∃ i, z ∈ closure (U i) ∧ (U i ∩ S).Nonempty := by
  let I := {i : ι | (U i ∩ S).Nonempty}
  have hsub : Tᶜ ∩ S ⊆ ⋃ i : I, U i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx.1)
    exact mem_iUnion.mpr ⟨⟨i, ⟨x, hi, hx.2⟩⟩, hi⟩
  have hz' : z ∈ closure (Tᶜ ∩ S) :=
    closure_mono (hdense.open_subset_closure_inter hS) hz |>
      (by simpa only [closure_closure, inter_comm] using ·)
  have hz'' := closure_mono hsub hz'
  rw [closure_iUnion_of_finite] at hz''
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz''
  exact ⟨i.val, hi, i.property⟩

end FiniteAvalanches.Electrical.StatementGeometry
