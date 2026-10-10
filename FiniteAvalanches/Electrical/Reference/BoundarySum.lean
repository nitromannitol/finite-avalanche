import FiniteAvalanches.Electrical.Reference.FirstMoment
import FiniteAvalanches.Electrical.Geometry.SourceAlphaCopies

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

/-- Enumerating the entire original alpha boundary transports the literal dart contact sum. -/
theorem source_boundary_contact_sum (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (m : ℕ) (copies : Fin m → Copy D P marked)
    (hinj : Function.Injective (fun i => (copies i).val))
    (hcoverage : ∀ e : Copy D P marked, (∃ i, copies i = e) ↔
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P)
    (F : ReferenceMoment.Forest D P marked) :
    ReferenceMoment.boundaryContacts D P marked F =
      ∑ i : Fin m, if (StatementTypes.graph D P marked).reaches F.val
        (if copyA D P marked (copies i) = alpha D P then copyB D P marked (copies i)
          else copyA D P marked (copies i)) (beta D P) then (1 : ℝ) else 0 := by
  let B := fun e : Copy D P marked => copyA D P marked e = alpha D P ∨
    copyB D P marked e = alpha D P
  let g := fun e : Copy D P marked =>
    if (StatementTypes.graph D P marked).reaches F.val
      (if copyA D P marked e = alpha D P then copyB D P marked e else copyA D P marked e)
      (beta D P) then (1 : ℝ) else 0
  let enum : Fin m ≃ {e : Copy D P marked // B e} :=
    Equiv.ofBijective (fun i => ⟨copies i, (hcoverage (copies i)).mp ⟨i, rfl⟩⟩)
      ⟨fun i j h => hinj (congrArg (fun b : {e // B e} => b.val.val) h), by
        intro e
        obtain ⟨i, hi⟩ := (hcoverage e.val).mpr e.property
        exact ⟨i, Subtype.ext hi⟩⟩
  have hs : (∑ e : {e : Copy D P marked // B e}, g e.val) = ∑ i : Fin m, g (copies i) :=
    (enum.sum_comp (fun e => g e.val)).symm
  have hf : (∑ e : {e : Copy D P marked // B e}, g e.val) =
      ∑ e : Copy D P marked, if B e then g e else 0 := by
    calc
      _ = ∑ e ∈ Finset.univ.filter B, g e :=
        (Finset.sum_subtype (p := B) (Finset.univ.filter B) (by simp) g).symm
      _ = _ := Finset.sum_filter B g
  rw [← hs, hf]
  unfold ReferenceMoment.boundaryContacts
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.sum_bool]
  have hne := copy_loopless D P marked e
  by_cases ha : copyA D P marked e = alpha D P
  · have hb : copyB D P marked e ≠ alpha D P := fun hb => hne (ha.trans hb.symm)
    simp [Plane.tail, Plane.head, Plane.reverse, B, g, ha, hb]
  · by_cases hb : copyB D P marked e = alpha D P
    · simp [Plane.tail, Plane.head, Plane.reverse, B, g, ha, hb]
    · simp [Plane.tail, Plane.head, Plane.reverse, B, g, ha, hb]
end
end FiniteAvalanches.Electrical.LatticeDrawing
