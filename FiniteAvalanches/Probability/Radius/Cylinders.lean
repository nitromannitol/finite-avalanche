import FiniteAvalanches.Sandpile.RadiusLocality
import FiniteAvalanches.Probability.FieldCylinders

/-! Literal radius events are finite-coordinate cylinders in the actual product
of four-height spaces. The finite pattern set is their image under restriction;
there is no chosen extension, default field, or substituted confinement event. -/
namespace FiniteAvalanches.Probability
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

theorem finite_coordinate_event_eq_cylinder (F : Finset Site2) (E : Set StableField)
    (hE : ∀ η η' : StableField, (∀ x ∈ F, η' x = η x) → (η' ∈ E ↔ η ∈ E)) :
    E = cylinder F (F.restrict '' E) := by
  ext η
  constructor
  · intro hη
    exact ⟨η, hη, rfl⟩
  · rintro ⟨η', hη', heq⟩
    exact (hE η' η (fun x hx => (congrFun heq ⟨x, hx⟩).symm)).mpr hη'

theorem isClopen_finite_coordinate_event (F : Finset Site2) (E : Set StableField)
    (hE : ∀ η η' : StableField, (∀ x ∈ F, η' x = η x) → (η' ∈ E ↔ η ∈ E)) :
    IsClopen E := by
  rw [finite_coordinate_event_eq_cylinder F E hE]
  exact (isClopen_discrete _).preimage
    (continuous_pi (fun x => continuous_apply x.val))

theorem radius_le_eq_cylinder (o : Site2) (R : ℕ) :
    {η : StableField | radius η o ≤ (R : WithTop ℕ)} =
      cylinder (boxSites (siteRadius 0 o + R + 1))
        ((boxSites (siteRadius 0 o + R + 1)).restrict ''
          {η : StableField | radius η o ≤ (R : WithTop ℕ)}) :=
  finite_coordinate_event_eq_cylinder _ _ (fun _ _ => radius_le_iff_of_agree_box o R)

theorem isClopen_radius_le (o : Site2) (R : ℕ) :
    IsClopen {η : StableField | radius η o ≤ (R : WithTop ℕ)} :=
  isClopen_finite_coordinate_event _ _ (fun _ _ => radius_le_iff_of_agree_box o R)

theorem isClopen_radius_gt (o : Site2) (R : ℕ) :
    IsClopen {η : StableField | (R : WithTop ℕ) < radius η o} := by
  simpa only [Set.compl_setOf, not_le] using (isClopen_radius_le o R).compl

theorem measurableSet_radius_le_local (o : Site2) (R : ℕ) :
    MeasurableSet {η : StableField | radius η o ≤ (R : WithTop ℕ)} :=
  (isClopen_radius_le o R).isClosed.measurableSet

theorem measurableSet_radius_gt_local (o : Site2) (R : ℕ) :
    MeasurableSet {η : StableField | (R : WithTop ℕ) < radius η o} :=
  (isClopen_radius_gt o R).isClosed.measurableSet

end
end FiniteAvalanches.Probability
