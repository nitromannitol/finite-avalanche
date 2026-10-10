import FiniteAvalanches.Electrical.SplitStep.DiagonalEnergy
import FiniteAvalanches.Electrical.SplitStep.OrderedBoundary
import FiniteAvalanches.Electrical.Reference.Voltage

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.SplitStep
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Electrical.ChordSplit
open scoped Classical BigOperators
noncomputable section

/-- The original H0 graph, with every retained original copy as its edge carrier. -/
def originalGraph (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    CopiedGraph (Vertex D P) (Copy D P marked) := ⟨copyA D P marked, copyB D P marked⟩

/-- The literal ordered split of H0 on the unchanged original copy carrier. -/
def actualSplit (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    CopiedGraph (SplitVertex (alpha D P)) (Copy D P marked) :=
  splitGraph (originalGraph D P marked) (alpha D P)
    (boundarySide (copyA D P marked) (copyB D P marked) (alpha D P) copies i)

/-- Extending the actual unique source voltage by zero at both split terminals. -/
def splitVoltage (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) : SplitVertex (alpha D P) → ℝ :=
  fun x => Repair8.voltage D P hD marked (collapse (alpha D P) x)

/-- The actual diagonal response against the two ground terminals. -/
def totalResponse (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) : ℝ :=
  responseEntry (actualSplit D P marked copies i).left
    (actualSplit D P marked copies i).right
    (splitTerminals (alpha D P) (beta D P) (by intro h; cases h))
    (split_terminal_reachable _ _ (alpha D P) (beta D P) (by intro h; cases h)
      (boundarySide _ _ (alpha D P) copies i)
      (Repair8.graph_connected D P hD marked).preconnected) 1 1

/-- The suffix current is a sum of voltages at the original opposite endpoints. -/
def suffixCurrent (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) : ℝ :=
  ∑ k : Fin m, if i ≤ k.val then
    Repair8.voltage D P hD marked
      (if copyA D P marked (copies k).val = alpha D P
       then copyB D P marked (copies k).val else copyA D P marked (copies k).val) else 0

theorem actual_copy_inflow (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (e : {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) :
    copyInflow (copyA D P marked) (copyB D P marked) (alpha D P)
      (Repair8.voltage D P hD marked) e.val =
    Repair8.voltage D P hD marked (if copyA D P marked e.val = alpha D P
      then copyB D P marked e.val else copyA D P marked e.val) := by
  have hp := (Repair8.voltage_spec D P hD marked).1
  have hloop := copy_loopless D P marked e.val
  rcases e.property with ha | hb
  · have hn : copyB D P marked e.val ≠ alpha D P := fun h => hloop (ha.trans h.symm)
    simp only [copyInflow, if_pos ha, if_neg hn, hp, sub_zero, add_zero]
  · by_cases ha : copyA D P marked e.val = alpha D P
    · exact (hloop (ha.trans hb.symm)).elim
    · simp only [copyInflow, if_neg ha, if_pos hb, hp, sub_zero, zero_add]

/-- Kirchhoff's boundary sum is derived from the actual original copy enumeration. -/
theorem actual_split_inflow (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    -laplacian (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right (splitVoltage D P hD marked) (.inr true) =
        suffixCurrent D P hD marked copies i := by
  rw [show -laplacian (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right (splitVoltage D P hD marked) (.inr true) =
      ∑ k : Fin m, if i ≤ k.val then copyInflow (copyA D P marked) (copyB D P marked)
        (alpha D P) (Repair8.voltage D P hD marked) (copies k).val else 0 from
    split_inflow_eq_boundary_suffix _ _ _ copies i _]
  simp only [suffixCurrent, actual_copy_inflow]

/-- Complete Dirichlet characterization of the actual extended source voltage. -/
theorem splitVoltage_spec (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    splitVoltage D P hD marked (.inr false) = 0 ∧
    splitVoltage D P hD marked (.inr true) = 0 ∧
    splitVoltage D P hD marked (.inl ⟨beta D P, by intro h; cases h⟩) = 1 ∧
    ∀ x, x ∉ terminalSet (splitTerminals (alpha D P) (beta D P) (by intro h; cases h)) →
      laplacian (actualSplit D P marked copies i).left
        (actualSplit D P marked copies i).right (splitVoltage D P hD marked) x = 0 := by
  have hp := Repair8.voltage_spec D P hD marked
  exact ⟨hp.1, hp.1, hp.2.1,
    Plane.split_pullback_harmonic _ _ _ _ (by intro h; cases h) _ _ hp.2.2⟩

/-- Uniqueness on the entire original split carrier follows from internally proved reachability. -/
theorem splitVoltage_unique (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ)
    (phi : SplitVertex (alpha D P) → ℝ) (hp0 : phi (.inr false) = 0)
    (hp1 : phi (.inr true) = 0)
    (hp2 : phi (.inl ⟨beta D P, by intro h; cases h⟩) = 1)
    (hh : ∀ x, x ∉ terminalSet (splitTerminals (alpha D P) (beta D P) (by intro h; cases h)) →
      laplacian (actualSplit D P marked copies i).left
        (actualSplit D P marked copies i).right phi x = 0) :
    phi = splitVoltage D P hD marked := by
  have hp := splitVoltage_spec D P hD marked copies i
  apply eq_of_harmonic_boundary (actualSplit D P marked copies i).left
    (actualSplit D P marked copies i).right
    (terminalSet (splitTerminals (alpha D P) (beta D P) (by intro h; cases h)))
    (split_terminal_reachable _ _ _ _ _ _ (Repair8.graph_connected D P hD marked).preconnected)
  · intro x hx
    obtain ⟨k, rfl⟩ := (mem_terminalSet_iff _ x).mp hx
    fin_cases k
    · exact hp0.trans hp.1.symm
    · exact hp1.trans hp.2.1.symm
    · exact hp2.trans hp.2.2.1.symm
  · exact hh
  · exact hp.2.2.2

theorem splitVoltage_energy (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    energy (actualSplit D P marked copies i).left (actualSplit D P marked copies i).right
      (splitVoltage D P hD marked) =
    energy (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked) :=
  split_energy_pullback _ _ _ _ _

/-- Exact unsymmetrized trial energy, with no prescribed value of f at beta. -/
theorem actual_split_ground_energy (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ)
    (f : SplitVertex (alpha D P) → ℝ) (hf0 : f (.inr false) = 0)
    (hf1 : f (.inr true) = 1) :
    energy (actualSplit D P marked copies i).left (actualSplit D P marked copies i).right
      (fun x => (1 - splitVoltage D P hD marked x) * f x) =
    suffixCurrent D P hD marked copies i +
      weightedEnergy (actualSplit D P marked copies i).left
        (actualSplit D P marked copies i).right (fun x => 1 - splitVoltage D P hD marked x) f := by
  have hp := splitVoltage_spec D P hD marked copies i
  have he := ground_energy_eq_current (actualSplit D P marked copies i).left
    (actualSplit D P marked copies i).right
    (splitTerminals (alpha D P) (beta D P) (by intro h; cases h))
    (splitTerminals_injective _ _ _) (splitVoltage D P hD marked) f
    hp.1 hp.2.1 hp.2.2.1 hf0 hf1 hp.2.2.2
  have hr1 : splitTerminals (alpha D P) (beta D P) (by intro h; cases h) 1 =
      Sum.inr true := rfl
  rw [hr1] at he
  rw [sub_eq_add_neg, actual_split_inflow, add_comm] at he
  exact he

/-- Closed actual-source analytic Step 1 with the literal suffix current. -/
theorem actual_split_total_response_bound (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ)
    (f : SplitVertex (alpha D P) → ℝ) (hf0 : f (.inr false) = 0)
    (hf1 : f (.inr true) = 1) :
    totalResponse D P hD marked copies i - suffixCurrent D P hD marked copies i ≤
      ∑ e : Copy D P marked,
        (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i).left e)) *
        (1 - splitVoltage D P hD marked ((actualSplit D P marked copies i).right e)) *
        (f ((actualSplit D P marked copies i).left e) -
          f ((actualSplit D P marked copies i).right e)) ^ 2 := by
  have hp := Repair8.voltage_spec D P hD marked
  have h := total_response_sub_current_le_weightedEnergy _ _
    (alpha D P) (beta D P) (by intro h; cases h) (boundarySide _ _ _ copies i)
    (Repair8.graph_connected D P hD marked).preconnected
    (Repair8.voltage D P hD marked) hp.1 hp.2.1 hp.2.2 f hf0 hf1
  change totalResponse D P hD marked copies i -
    (-laplacian (actualSplit D P marked copies i).left
      (actualSplit D P marked copies i).right (splitVoltage D P hD marked) (.inr true)) ≤ _ at h
  rw [actual_split_inflow] at h
  exact h

/-- The actual identified-ground energy is the total R11, retaining all original IDs. -/
theorem actual_identified_energy_eq_totalResponse (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) {m : ℕ} (copies : Fin m ≃ {e : Copy D P marked //
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P}) (i : ℕ) :
    let K := groundedSplitGraph (originalGraph D P marked) (alpha D P) (beta D P)
      (boundarySide _ _ _ copies i)
    energy K.left K.right
      (identifiedVoltage (originalGraph D P marked) (alpha D P) (beta D P)
        (boundarySide _ _ _ copies i) (Repair8.graph_connected D P hD marked).preconnected) =
      totalResponse D P hD marked copies i := by
  exact identified_energy_eq_total_response (originalGraph D P marked)
    (alpha D P) (beta D P) (by intro h; cases h) _
    (Repair8.graph_connected D P hD marked).preconnected

end
end FiniteAvalanches.Electrical.SplitStep
