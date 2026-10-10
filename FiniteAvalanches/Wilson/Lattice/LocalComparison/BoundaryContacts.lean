import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoxSourceLaw
import FiniteAvalanches.Electrical.Reference.FirstMoment

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

local instance retainedDecidableEq (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : DecidableEq (Copy D P marked) := Classical.decEq _
local instance deletedDecidableEq (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : DecidableEq (LocalMarkedForest.deletedCopies D P marked) := Classical.decEq _

/-- All exterior sites adjacent to D; this is the entire finite support of exterior contacts. -/
def exteriorSites (D : Finset (Site 2)) : Finset (Site 2) :=
  (contactSites D).filter (fun x => x ∉ D)

/-- The literal source L(A), summed over its full finite contributing support. -/
def exteriorContacts (D : Finset (Site 2)) (A : Set (Site 2)) (σ : ColorField) : ℕ :=
  contacts ((exteriorSites D).filter (fun x => x ∈ A)) σ

/-- Each original alpha dart is counted, independently of whether its edge is selected. -/
def primalBoundary (D : Finset (Site 2)) (P : OneSet D) (F : PrimalForest D P) : ℝ :=
  ∑ z : Plane.Dart (PrimalCopy D P),
    if Plane.tail (primalGraph D P).left (primalGraph D P).right z = alpha D P ∧
      (primalGraph D P).reaches F.val
        (Plane.head (primalGraph D P).left (primalGraph D P).right z) (beta D P)
    then 1 else 0

theorem referencePrimal_original_ids (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    (LocalMarkedForest.referencePrimalEquiv D P marked F).val.image Subtype.val =
      F.val.image Subtype.val := by
  change (Multigraph.liftEdgeSubset (LocalMarkedForest.deletedCopies D P marked)
    (F.val.image (LocalMarkedForest.retainedCopyEquiv D P marked))).image Subtype.val = _
  simp only [Multigraph.liftEdgeSubset, Finset.image_image, Function.comp_def]
  rfl

theorem referenceEquiv_original_ids (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x) (marked : MarkedCopy D P)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N) :
    (referenceEquiv D P N hDbox marked F).val.image Subtype.val = F.val.image boxID := by
  rw [← referencePrimal_original_ids D P marked]
  change ((LocalMarkedForest.referencePrimalEquiv D P marked)
    ((LocalMarkedForest.referencePrimalEquiv D P marked).symm (forestEquiv D P N hDbox F))).val.image Subtype.val = _
  rw [Equiv.apply_symm_apply]
  exact forestEquiv_original_ids D P N hDbox F

theorem reference_field_exterior (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) (x : Site 2)
    (hx : x ∉ D) : referenceField D P marked F x = false := by
  have hproj := (project_eq_alpha_iff D P x).mpr hx
  change decide ((StatementTypes.graph D P marked).reaches F.val (project D P x) (beta D P)) = false
  rw [hproj, decide_eq_false_iff_not]
  intro h
  obtain ⟨u,_,_,hu⟩ := F.property.2 (alpha D P)
  have he : alpha D P = beta D P := (hu _ (Or.inl rfl) .refl).trans (hu _ (Or.inr rfl) h).symm
  cases he

theorem reference_field_P (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) (x : Site 2)
    (hx : x ∈ P.val.image Subtype.val) : referenceField D P marked F x = true := by
  change decide ((StatementTypes.graph D P marked).reaches F.val (project D P x) (beta D P)) = true
  rw [(project_eq_beta_iff D P x).mpr hx, decide_eq_true_eq]
  exact Relation.ReflTransGen.refl

/-- Split all exterior contacts into A and its complement, with every neighbor occurrence retained. -/
theorem exterior_contacts_partition (D : Finset (Site 2)) (A : Set (Site 2)) (σ : ColorField) :
    exteriorContacts D A σ + exteriorContacts D ((D : Set (Site 2))ᶜ \ A) σ =
      contacts (exteriorSites D) σ := by
  have h := Finset.sum_filter_add_sum_filter_not (s := exteriorSites D)
    (p := fun x => x ∈ A) (f := fun x => ∑ y ∈ nbrFinset x, if σ y then (1 : ℕ) else 0)
  unfold exteriorContacts contacts
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [Finset.sum_filter, Finset.sum_filter] at h
  calc
    _ = (∑ x ∈ exteriorSites D, if x ∈ A then (∑ y ∈ nbrFinset x, if σ y then 1 else 0) else 0) +
        ∑ x ∈ exteriorSites D, if x ∉ A then (∑ y ∈ nbrFinset x, if σ y then 1 else 0) else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hd : x ∉ D := (Finset.mem_filter.mp hx).2
      simp only [Set.mem_sdiff, Set.mem_compl_iff, Finset.mem_coe, hd, not_false_eq_true, true_and]
    _ = _ := h

end
end LocalBoxContraction
