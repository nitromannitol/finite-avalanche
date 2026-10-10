import FiniteAvalanches.Electrical.Reference.Voltage
import FiniteAvalanches.Electrical.Reference.NoBridges

set_option autoImplicit false
namespace LocalEnergyUpper
open LatticeProb FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical BigOperators
noncomputable section

/-- A trial voltage with value one at every vertex except the zero terminal. -/
def trial (D : Finset (Site 2)) (P : OneSet D) (x : Vertex D P) : ℝ :=
  if x = alpha D P then 0 else 1

theorem marked_mem_exits (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) : marked.val ∈ latticeExits D := by
  rw [mem_latticeExits]
  rcases marked.property with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · right
    refine ⟨?_, (project_eq_alpha_iff D P _).mp ha⟩
    obtain ⟨x,_,he⟩ := Finset.mem_image.mp ((project_eq_beta_iff D P _).mp hb)
    exact he ▸ x.property
  · left
    refine ⟨?_, (project_eq_alpha_iff D P _).mp hb⟩
    obtain ⟨x,_,he⟩ := Finset.mem_image.mp ((project_eq_beta_iff D P _).mp ha)
    exact he ▸ x.property

theorem exit_project (D : Finset (Site 2)) (P : OneSet D) (e : OriginalCopy) :
    e ∈ latticeExits D ↔
      (project D P (originalA e) = alpha D P ∧ project D P (originalB e) ≠ alpha D P) ∨
      (project D P (originalB e) = alpha D P ∧ project D P (originalA e) ≠ alpha D P) := by
  simp only [mem_latticeExits, ne_eq, project_eq_alpha_iff, not_not]
  tauto

/-- Every surviving alpha incidence retains its original physical edge ID. -/
def alphaCopiesEquiv (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    {e : Copy D P marked // copyA D P marked e = alpha D P ∨
      copyB D P marked e = alpha D P} ≃ ↥((latticeExits D).erase marked.val) where
  toFun e := ⟨e.val.val, by
    apply Finset.mem_erase.mpr
    refine ⟨(mem_retainedCopies D P marked _).mp e.val.property |>.2.2, ?_⟩
    apply (exit_project D P _).mpr
    rcases e.property with ha | hb
    · exact Or.inl ⟨ha, fun hb => copy_loopless D P marked e.val (ha.trans hb.symm)⟩
    · exact Or.inr ⟨hb, fun ha => copy_loopless D P marked e.val (ha.trans hb.symm)⟩⟩
  invFun e := ⟨⟨e.val, by
    obtain ⟨hne,hex⟩ := Finset.mem_erase.mp e.property
    refine (mem_retainedCopies D P marked _).mpr ⟨?_, ?_, hne⟩
    · exact ((mem_latticeExits D _).mp hex).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    · rcases (exit_project D P _).mp hex with ⟨ha,hb⟩ | ⟨hb,ha⟩
      · exact fun he => hb (he ▸ ha)
      · exact fun he => ha (he.symm ▸ hb)⟩, by
    rcases (exit_project D P _).mp (Finset.mem_erase.mp e.property).2 with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem alpha_copies_card (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    Fintype.card {e : Copy D P marked // copyA D P marked e = alpha D P ∨
      copyB D P marked e = alpha D P} = (latticeExits D).card - 1 := by
  rw [Fintype.card_congr (alphaCopiesEquiv D P marked), Fintype.card_coe,
    Finset.card_erase_of_mem (marked_mem_exits D P marked)]

theorem trial_energy (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    energy (copyA D P marked) (copyB D P marked) (trial D P) =
      ((latticeExits D).card - 1 : ℕ) := by
  have he (e : Copy D P marked) :
      (trial D P (copyA D P marked e) - trial D P (copyB D P marked e))^2 =
        if copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P
        then (1 : ℝ) else 0 := by
    by_cases ha : copyA D P marked e = alpha D P
    · have hb : copyB D P marked e ≠ alpha D P :=
        fun hb => copy_loopless D P marked e (ha.trans hb.symm)
      norm_num [trial, ha, hb]
    · by_cases hb : copyB D P marked e = alpha D P
      · norm_num [trial, ha, hb]
      · simp [trial, ha, hb]
  unfold energy
  simp_rw [he]
  rw [Finset.sum_boole]
  have hc : (Finset.univ.filter fun e : Copy D P marked =>
      copyA D P marked e = alpha D P ∨ copyB D P marked e = alpha D P).card =
      Fintype.card {e : Copy D P marked // copyA D P marked e = alpha D P ∨
        copyB D P marked e = alpha D P} := by
    exact (Fintype.card_subtype _).symm
  rw [hc, alpha_copies_card]

/-- Dirichlet minimization gives the upper bound with the original exit multiplicity. -/
theorem voltage_energy_le_original_exits (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (D : Set (Site 2))).Connected) (marked : MarkedCopy D P) :
    energy (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked) ≤
      ((latticeExits D).card - 1 : ℕ) := by
  have hs := Repair8.voltage_spec D P hD marked
  have hf : ∀ x ∈ ({alpha D P,beta D P} : Finset (Vertex D P)),
      trial D P x = Repair8.voltage D P hD marked x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [hs.1]; simp only [trial, ↓reduceIte]
    · rw [hs.2.1]; simp only [trial, beta, alpha, Sum.inl.injEq, Bool.true_eq_false,
        if_false]
  have hh : ∀ x, x ∉ ({alpha D P,beta D P} : Finset (Vertex D P)) →
      laplacian (copyA D P marked) (copyB D P marked) (Repair8.voltage D P hD marked) x = 0 := by
    intro x hx
    exact hs.2.2 x (fun he => hx (by simp only [he, Finset.mem_insert_self]))
      (fun he => hx (by simp only [he, Finset.mem_insert, Finset.mem_singleton, or_true]))
  have hm := energy_eq_add_energy_sub_of_harmonic (copyA D P marked) (copyB D P marked)
    {alpha D P,beta D P} (trial D P) (Repair8.voltage D P hD marked) hf hh
  have hl := le_add_of_nonneg_right (a := energy (copyA D P marked) (copyB D P marked)
    (Repair8.voltage D P hD marked))
    (energy_nonneg (copyA D P marked) (copyB D P marked) (trial D P - Repair8.voltage D P hD marked))
  rw [← hm, trial_energy] at hl
  exact hl

end
end LocalEnergyUpper
