import FiniteAvalanches.Wilson.Lattice.LocalComparison.OriginalContactEquiv

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

theorem originalBoundary_rawCount (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    originalBoundary D P marked F = (rawBoundaryCount D (referenceField D P marked F) : ℝ) := by
  unfold originalBoundary rawBoundaryCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  unfold boundaryWeight
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  rw [project_eq_alpha_iff]
  simp only [referenceField, decide_eq_true_eq]

/-- H counts all one-colored boundary neighbors from the entire D-complement. -/
theorem primal_boundary_contacts (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    primalBoundary D P (LocalMarkedForest.referencePrimalEquiv D P marked F) =
      (contacts (exteriorSites D) (referenceField D P marked F) : ℝ) := by
  rw [← original_boundary_eq_primal, originalBoundary_rawCount,
    rawBoundaryCount_contacts D _ (reference_field_exterior D P marked F)]

/-- The source retained-copy Y is L(A)-1+L(D-complement minus A), counting every original boundary copy. -/
theorem source_observable_identity (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) (A : Set (Site 2)) :
    ReferenceMoment.boundaryContacts D P marked F =
      (exteriorContacts D A (referenceField D P marked F) : ℝ) - 1 +
        (exteriorContacts D ((D : Set (Site 2))ᶜ \ A) (referenceField D P marked F) : ℝ) := by
  have hp : (exteriorContacts D A (referenceField D P marked F) : ℝ) +
      (exteriorContacts D ((D : Set (Site 2))ᶜ \ A) (referenceField D P marked F) : ℝ) =
      (contacts (exteriorSites D) (referenceField D P marked F) : ℝ) := by
    exact_mod_cast exterior_contacts_partition D A (referenceField D P marked F)
  rw [marked_boundary_subtract_one, originalBoundary_rawCount,
    rawBoundaryCount_contacts D _ (reference_field_exterior D P marked F)]
  linarith only [hp]

end
end LocalBoxContraction
