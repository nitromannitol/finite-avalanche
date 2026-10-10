import FiniteAvalanches.Electrical.Reference.Connected

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.Repair8
open LatticeProb
open scoped Classical BigOperators
noncomputable section

/-- The source zero/one voltage exists uniquely on every actual punctured lattice network. -/
theorem existsUnique_voltage (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    ∃! phi : Vertex D P → ℝ,
      phi (alpha D P) = 0 ∧ phi (beta D P) = 1 ∧
        ∀ x, x ≠ alpha D P → x ≠ beta D P →
          laplacian (copyA D P marked) (copyB D P marked) phi x = 0 := by
  have hne : alpha D P ≠ beta D P := by intro h; cases h
  have hB : ∀ x, ∃ y ∈ ({alpha D P, beta D P} : Finset (Vertex D P)),
      (supportGraph (copyA D P marked) (copyB D P marked)).Reachable x y :=
    fun x => ⟨alpha D P, by simp, (graph_connected D P hD marked).preconnected x _⟩
  obtain ⟨f, hf, huni⟩ := existsUnique_harmonic_extension
    (copyA D P marked) (copyB D P marked) {alpha D P, beta D P} hB
    (fun x => if x = beta D P then (1 : ℝ) else 0)
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [if_neg hne] using hf.1 (alpha D P) (by simp)
  · simpa using hf.1 (beta D P) (by simp)
  · intro x ha hb
    exact hf.2 x (by simp [ha, hb])
  · intro g hg
    apply huni g
    constructor
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa only [if_neg hne] using hg.1
      · simpa using hg.2.1
    · intro x hx
      exact hg.2.2 x (by intro h; exact hx (by simp [h]))
        (by intro h; exact hx (by simp [h]))

/-- Choice is made only from the proved unique source voltage. -/
def voltage (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) : Vertex D P → ℝ :=
  (existsUnique_voltage D P hD marked).choose

/-- Complete source characterization, including every free vertex and both terminal values. -/
theorem voltage_spec (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    voltage D P hD marked (alpha D P) = 0 ∧
      voltage D P hD marked (beta D P) = 1 ∧
        ∀ x, x ≠ alpha D P → x ≠ beta D P →
          laplacian (copyA D P marked) (copyB D P marked) (voltage D P hD marked) x = 0 :=
  (existsUnique_voltage D P hD marked).choose_spec.1

/-- Every characterized field equals the actual source voltage; no extension value is arbitrary. -/
theorem voltage_unique (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (f : Vertex D P → ℝ)
    (hf : f (alpha D P) = 0 ∧ f (beta D P) = 1 ∧
      ∀ x, x ≠ alpha D P → x ≠ beta D P →
        laplacian (copyA D P marked) (copyB D P marked) f x = 0) :
    f = voltage D P hD marked :=
  (existsUnique_voltage D P hD marked).choose_spec.2 f hf

/-- The literal once-per-copy source energy is strictly positive. -/
theorem voltage_energy_pos (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    0 < energy (copyA D P marked) (copyB D P marked) (voltage D P hD marked) := by
  have hs := voltage_spec D P hD marked
  have hn := energy_nonneg (copyA D P marked) (copyB D P marked) (voltage D P hD marked)
  by_contra hpos
  have hz : energy (copyA D P marked) (copyB D P marked) (voltage D P hD marked) = 0 :=
    le_antisymm (le_of_not_gt hpos) hn
  have heq := eq_of_reachable (copyA D P marked) (copyB D P marked)
    (voltage D P hD marked) ((energy_eq_zero_iff _ _ _).mp hz)
    ((graph_connected D P hD marked).preconnected (alpha D P) (beta D P))
  rw [hs.1, hs.2.1] at heq
  norm_num at heq

/-- The full original forest-count denominator gives a genuine uniform probability mass. -/
theorem forest_uniform_mass_sum (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    (∑ _f : (StatementTypes.graph D P marked).RootedForest
      ({alpha D P, beta D P} : Set (Vertex D P)),
      (Fintype.card ((StatementTypes.graph D P marked).RootedForest
        ({alpha D P, beta D P} : Set (Vertex D P))) : ℝ)⁻¹) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply mul_inv_cancel₀
  exact_mod_cast Nat.ne_of_gt (forest_card_pos D P hD marked)

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.Repair8
