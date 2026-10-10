import FiniteAvalanches.Electrical.Reference.ColorMarginal
import FiniteAvalanches.Electrical.Plane.AuxiliaryArc

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
open LatticeProb
open scoped Classical BigOperators
noncomputable section
variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

/-- The source contact observable: all original copies leaving alpha, not selected forest edges. -/
def boundaryContacts (F : Forest D P marked) : ℝ :=
  ∑ z : Plane.Dart (Copy D P marked),
    if Plane.tail (copyA D P marked) (copyB D P marked) z = alpha D P ∧
      (StatementTypes.graph D P marked).reaches F.val
        (Plane.head (copyA D P marked) (copyB D P marked) z) (beta D P)
    then 1 else 0

/-- The genuine uniform average over the full original copied two-root forest carrier. -/
def forestMean : ℝ :=
  (∑ F : Forest D P marked, boundaryContacts D P marked F) /
    (Fintype.card (Forest D P marked) : ℝ)

theorem indicator_average_eq_colorMass (x : Vertex D P) :
    (∑ F : Forest D P marked,
      if (StatementTypes.graph D P marked).reaches F.val x (beta D P)
      then (1 : ℝ) else 0) / (Fintype.card (Forest D P marked) : ℝ) =
        vertexColorMass D P marked x := by
  unfold vertexColorMass
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  exact Finset.sum_boole _ _

theorem forestMean_eq_boundary_voltage
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) :
    forestMean D P marked = ∑ z : Plane.Dart (Copy D P marked),
      if Plane.tail (copyA D P marked) (copyB D P marked) z = alpha D P
      then Repair8.voltage D P hD marked
        (Plane.head (copyA D P marked) (copyB D P marked) z) else 0 := by
  unfold forestMean boundaryContacts
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : Plane.tail (copyA D P marked) (copyB D P marked) z = alpha D P
  · simp only [hz, true_and, if_true]
    rw [indicator_average_eq_colorMass, vertexColorMass_eq_voltage D P marked hD]
  · simp [hz]

private theorem boundary_voltage_eq_neg_laplacian {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] (a b : E → V) (phi : V → ℝ) (alpha : V)
    (h0 : phi alpha = 0) :
    (∑ z : Plane.Dart E, if Plane.tail a b z = alpha
      then phi (Plane.head a b z) else 0) = -laplacian a b phi alpha := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Plane.head, Plane.reverse, Plane.tail,
    Equiv.coe_fn_mk, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ↓reduceIte]
  rw [laplacian, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [h0]
  split_ifs <;> ring

/-- The exact source first moment on every admitted punctured lattice carrier. -/
theorem mean_eq_energy
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) :
    forestMean D P marked = energy (copyA D P marked) (copyB D P marked)
      (Repair8.voltage D P hD marked) := by
  have hs := Repair8.voltage_spec D P hD marked
  have hne : alpha D P ≠ beta D P := by intro h; cases h
  have ht := (Plane.terminal_flux_eq_energy (copyA D P marked) (copyB D P marked)
    (Repair8.voltage D P hD marked) (alpha D P) (beta D P) hne hs.1 hs.2.1 hs.2.2).1
  have hf := boundary_voltage_eq_neg_laplacian (V := Vertex D P) (E := Copy D P marked)
    (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked) (alpha D P) hs.1
  rw [ht, neg_neg] at hf
  exact (forestMean_eq_boundary_voltage D P marked hD).trans hf

/-- Literal first conjunct of el:reference-moment, with all source standing binders. -/
theorem reference_first_moment (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (_hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (_hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    let a := copyA D P marked
    let b := copyB D P marked
    let J := StatementTypes.graph D P marked
    let F := J.RootedForest ({alpha D P, beta D P} : Set (Vertex D P))
    letI : Nonempty F := Repair8.forest_nonempty D P hD marked
    let phi := Repair8.voltage D P hD marked
    let Y : F → ℝ := fun f => ∑ z : Plane.Dart (Copy D P marked),
      if Plane.tail a b z = alpha D P ∧ J.reaches f.val (Plane.head a b z) (beta D P)
      then 1 else 0
    let mean := (∑ f : F, Y f)/(Fintype.card F : ℝ)
    let M := energy a b phi
    mean = M := mean_eq_energy D P marked hD

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
