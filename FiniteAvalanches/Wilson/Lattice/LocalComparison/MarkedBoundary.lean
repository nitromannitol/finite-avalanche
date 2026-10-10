import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoundaryContacts

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

theorem dart_tail_false {V E : Type} (a b : E → V) (e : E) : Plane.tail a b (e,false) = a e := rfl
theorem dart_tail_true {V E : Type} (a b : E → V) (e : E) : Plane.tail a b (e,true) = b e := rfl
theorem dart_head_false {V E : Type} (a b : E → V) (e : E) : Plane.head a b (e,false) = b e := rfl
theorem dart_head_true {V E : Type} (a b : E → V) (e : E) : Plane.head a b (e,true) = a e := rfl

/-- The original copied boundary summand, before either loop deletion or marked deletion. -/
def boundaryWeight (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (F : ReferenceForest D P marked) (e : OriginalCopy) : ℝ :=
  ∑ b : Bool,
    if project D P (Plane.tail originalA originalB (e,b)) = alpha D P ∧
      (StatementTypes.graph D P marked).reaches F.val
        (project D P (Plane.head originalA originalB (e,b))) (beta D P)
    then 1 else 0

/-- The boundary count includes every original copied ID incident to D. -/
def originalBoundary (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (F : ReferenceForest D P marked) : ℝ :=
  ∑ e ∈ domainCopies D, boundaryWeight D P marked F e

theorem reference_alpha_not_beta (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    ¬(StatementTypes.graph D P marked).reaches F.val (alpha D P) (beta D P) := by
  intro h
  obtain ⟨u,_,_,hu⟩ := F.property.2 (alpha D P)
  have he : alpha D P = beta D P := (hu _ (Or.inl rfl) .refl).trans (hu _ (Or.inr rfl) h).symm
  cases he

theorem boundaryWeight_loop_zero (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) (e : OriginalCopy)
    (he : project D P (originalA e) = project D P (originalB e)) :
    boundaryWeight D P marked F e = 0 := by
  have hn := reference_alpha_not_beta D P marked F
  unfold boundaryWeight
  apply Finset.sum_eq_zero
  intro b _
  cases b
  · change (if project D P (originalA e) = alpha D P ∧
      (StatementTypes.graph D P marked).reaches F.val (project D P (originalB e)) (beta D P) then (1 : ℝ) else 0) = 0
    apply if_neg
    rintro ⟨ha,hb⟩
    have hba : project D P (originalB e) = alpha D P := he.symm.trans ha
    rw [hba] at hb
    exact hn hb
  · change (if project D P (originalB e) = alpha D P ∧
      (StatementTypes.graph D P marked).reaches F.val (project D P (originalA e)) (beta D P) then (1 : ℝ) else 0) = 0
    apply if_neg
    rintro ⟨hb,ha⟩
    have hab : project D P (originalA e) = alpha D P := he.trans hb
    rw [hab] at ha
    exact hn ha

theorem boundaryWeight_marked_one (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    boundaryWeight D P marked F marked.val = 1 := by
  have hbb : (StatementTypes.graph D P marked).reaches F.val (beta D P) (beta D P) := .refl
  have hab : beta D P ≠ alpha D P := by intro h; cases h
  unfold boundaryWeight
  rw [Fintype.sum_bool]
  change (if project D P (originalB marked.val) = alpha D P ∧
      (StatementTypes.graph D P marked).reaches F.val (project D P (originalA marked.val)) (beta D P) then (1 : ℝ) else 0) +
    (if project D P (originalA marked.val) = alpha D P ∧
      (StatementTypes.graph D P marked).reaches F.val (project D P (originalB marked.val)) (beta D P) then 1 else 0) = 1
  rcases marked.property with ⟨ha,hb⟩ | ⟨ha,hb⟩
  all_goals simp only [ha,hb,hbb,hab,false_and,and_self,if_true,if_false,zero_add,add_zero]

theorem reference_boundary_sum (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    ReferenceMoment.boundaryContacts D P marked F =
      ∑ e ∈ retainedCopies D P marked, boundaryWeight D P marked F e := by
  unfold ReferenceMoment.boundaryContacts
  rw [Fintype.sum_prod_type, Finset.univ_eq_attach]
  change (∑ e ∈ (retainedCopies D P marked).attach, boundaryWeight D P marked F e.val) = _
  exact Finset.sum_attach _ _

theorem primal_boundary_sum (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    primalBoundary D P (LocalMarkedForest.referencePrimalEquiv D P marked F) =
      ∑ e ∈ primalCopies D P, boundaryWeight D P marked F e := by
  unfold primalBoundary
  rw [Fintype.sum_prod_type, Finset.univ_eq_attach]
  calc
    _ = ∑ e ∈ (primalCopies D P).attach, boundaryWeight D P marked F e.val := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro b _
      have ht : Plane.tail (primalGraph D P).left (primalGraph D P).right (e,b) =
          project D P (Plane.tail originalA originalB (e.val,b)) := by cases b <;> rfl
      have hh : Plane.head (primalGraph D P).left (primalGraph D P).right (e,b) =
          project D P (Plane.head originalA originalB (e.val,b)) := by cases b <;> rfl
      apply if_congr
      · apply and_congr
        · rw [ht]
        · exact (LocalMarkedForest.referencePrimalEquiv_reaches D P marked F _ _).trans (by rw [hh])
      · rfl
      · rfl

    _ = _ := Finset.sum_attach _ _

theorem original_boundary_eq_primal (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    originalBoundary D P marked F = primalBoundary D P (LocalMarkedForest.referencePrimalEquiv D P marked F) := by
  rw [primal_boundary_sum]
  unfold originalBoundary primalCopies
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : project D P (originalA e) = project D P (originalB e)
  · rw [if_neg (not_not.mpr he), boundaryWeight_loop_zero D P marked F e he]
  · rw [if_pos he]

/-- Deleting the distinguished exterior-to-P copy subtracts exactly one from the full boundary count. -/
theorem marked_boundary_subtract_one (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : ReferenceForest D P marked) :
    ReferenceMoment.boundaryContacts D P marked F = originalBoundary D P marked F - 1 := by
  rw [original_boundary_eq_primal, primal_boundary_sum, reference_boundary_sum,
    retainedCopies_eq_primal_erase]
  have h := Finset.sum_erase_add (s := primalCopies D P)
    (f := boundaryWeight D P marked F) (JointMarkedDeletion.marked_mem_primal D P marked)
  rw [boundaryWeight_marked_one] at h
  linarith only [h]

end
end LocalBoxContraction
