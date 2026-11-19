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

/-- A Jordan curve contained in a nowhere-dense trace has distinct incident
covering regions on its two sides. -/
theorem exists_distinct_cover_members_at_jordan {ι : Type} [Finite ι]
    (T C : Set Schoenflies.Plane) (U : ι → Set Schoenflies.Plane)
    (hdense : Dense Tᶜ) (hcover : Tᶜ ⊆ ⋃ i, U i)
    (hsub : ∀ i, U i ⊆ Tᶜ) (hconn : ∀ i, IsPreconnected (U i))
    (hCT : C ⊆ T) (hC : Schoenflies.IsSeparating C) {z : Schoenflies.Plane}
    (hz : z ∈ C) :
    ∃ i j, i ≠ j ∧ z ∈ closure (U i) ∧ z ∈ closure (U j) ∧
      (U i ∩ Schoenflies.inside C).Nonempty ∧
      (U j ∩ Schoenflies.outside C).Nonempty := by
  have hzi : z ∈ closure (Schoenflies.inside C) :=
    frontier_subset_closure (hC.frontier_inside.symm ▸ hz)
  have hzo : z ∈ closure (Schoenflies.outside C) :=
    frontier_subset_closure (hC.frontier_outside.symm ▸ hz)
  obtain ⟨i, hi, x, hxU, hxi⟩ :=
    exists_cover_member_at_closure T (Schoenflies.inside C) U hdense hcover hC.isOpen_inside hzi
  obtain ⟨j, hj, y, hyU, hyo⟩ :=
    exists_cover_member_at_closure T (Schoenflies.outside C) U hdense hcover hC.isOpen_outside hzo
  refine ⟨i, j, ?_, hi, hj, ⟨x, hxU, hxi⟩, ⟨y, hyU, hyo⟩⟩
  intro hij
  subst j
  have hUC : U i ⊆ Cᶜ := fun w hw hwC => hsub i hw (hCT hwC)
  have hycomp : y ∈ connectedComponentIn Cᶜ x :=
    (hconn i).subset_connectedComponentIn hxU hUC hyU
  have hyi : y ∈ Schoenflies.inside C :=
    Schoenflies.connectedComponentIn_subset_inside hxi hycomp
  exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hyi hyo

end FiniteAvalanches.Electrical.StatementGeometry
