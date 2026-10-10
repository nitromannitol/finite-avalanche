import FiniteAvalanches.Electrical.Reference.Voltage
import FiniteAvalanches.Electrical.Geometry.CellPath
import FiniteAvalanches.Electrical.LocalHarnack

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CellVoltage10
open LatticeProb
open FiniteAvalanches.Electrical.LatticeCell
open scoped Classical BigOperators
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D)
variable (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
local notation "φ" => Repair8.voltage D P hD marked

/-- The actual copied voltage obeys both boundary bounds. -/
theorem voltage_bounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1 :=
  LocalHarnack.voltage_bounds (copyA D P marked) (copyB D P marked) (alpha D P) (beta D P) φ
    (by
      intro x
      exact ⟨beta D P, by simp,
        (Repair8.graph_connected D P hD marked).preconnected x (beta D P)⟩)
    (Repair8.voltage_spec D P hD marked).1 (Repair8.voltage_spec D P hD marked).2.1
    (Repair8.voltage_spec D P hD marked).2.2

/-- Every admitted lattice site of D projects away from the zero terminal. -/
theorem project_ne_alpha {x : Site 2} (hx : x ∈ D) : project D P x ≠ alpha D P := by
  intro he
  exact ((project_eq_alpha_iff D P x).mp he) hx

/-- Original free degree is four, counting all individual parallel physical copies. -/
theorem free_copy_degree (x : {x : D // x ∉ P.val}) :
    Geometry.degree (copyA D P marked) (copyB D P marked) (.inr x) = 4 :=
  free_degree D P marked x

/-- An internal lattice step is a retained original copied edge, or a collapsed P step. -/
theorem internal_adj_projection {x y : Site 2} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : (lattice 2).Adj x y) :
    project D P x = project D P y ∨
      (supportGraph (copyA D P marked) (copyB D P marked)).Adj (project D P x) (project D P y) := by
  by_cases hq : project D P x = project D P y
  · exact Or.inl hq
  right
  obtain ⟨i,h | h⟩ := hxy
  · let e : OriginalCopy := (x,i)
    have he : e ∈ retainedCopies D P marked := by
      apply (mem_retainedCopies D P marked e).mpr
      refine ⟨Or.inl hx,?_,Repair8.internal_ne_marked D P marked e hx ?_⟩
      · simpa [e,originalA,originalB,← h] using hq
      · simpa [e,originalB,← h] using hy
    refine ⟨hq,⟨e,he⟩,Or.inl ⟨rfl,?_⟩⟩
    change project D P (x+unit i) = project D P y
    rw [← h]
  · let e : OriginalCopy := (y,i)
    have he : e ∈ retainedCopies D P marked := by
      apply (mem_retainedCopies D P marked e).mpr
      refine ⟨Or.inl hy,?_,Repair8.internal_ne_marked D P marked e hy ?_⟩
      · simpa [e,originalA,originalB,← h] using Ne.symm hq
      · simpa [e,originalB,← h] using hx
    refine ⟨hq,⟨e,he⟩,Or.inr ⟨?_,rfl⟩⟩
    change project D P (y+unit i) = project D P x
    rw [← h]

/-- The original lattice step has the factor-four bound even when it contracts to a loop. -/
theorem internal_step_bound {x y : Site 2} (hx : x ∈ D) (hy : y ∈ D)
    (hxy : (lattice 2).Adj x y) : φ (project D P y) ≤ 4 * φ (project D P x) := by
  rcases internal_adj_projection D P marked hx hy hxy with he | he
  · rw [← he]
    have hn := (voltage_bounds D P hD marked (project D P x)).1
    linarith
  · exact LocalHarnack.phi_le_four_mul_of_adj_voltage (copyA D P marked) (copyB D P marked)
      (alpha D P) (beta D P) φ (by
      intro x
      exact ⟨beta D P, by simp,
        (Repair8.graph_connected D P hD marked).preconnected x (beta D P)⟩)
      (Repair8.voltage_spec D P hD marked).1 (Repair8.voltage_spec D P hD marked).2.1
      (Repair8.voltage_spec D P hD marked).2.2 (source_free_degree_bound D P marked)
      (project_ne_alpha D P hx) he

/-- Actual connectedness to a nonempty P makes the voltage strictly positive everywhere in D. -/
theorem voltage_pos_on_D {x : Site 2} (hx : x ∈ D) : 0 < φ (project D P x) := by
  by_contra hpos
  have hz : φ (project D P x) = 0 :=
    le_antisymm (le_of_not_gt hpos) (voltage_bounds D P hD marked (project D P x)).1
  obtain ⟨p,hp⟩ := P.property
  have path := induced_reaches (↑D : Set (Site 2)) hD x p.val hx p.property
  have propagate {u v : Site 2}
      (hr : Relation.ReflTransGen (fun a b => a ∈ D ∧ b ∈ D ∧ (lattice 2).Adj a b) u v)
      (hu : φ (project D P u) = 0) : φ (project D P v) = 0 := by
    induction hr with
    | refl => exact hu
    | @tail v w _ hstep ih =>
      have hle := internal_step_bound D P hD marked hstep.1 hstep.2.1 hstep.2.2
      rw [ih] at hle
      exact le_antisymm (by linarith) (voltage_bounds D P hD marked (project D P w)).1
  have hpzero := propagate path hz
  have hb : project D P p.val = beta D P :=
    (project_eq_beta_iff D P _).mpr (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  rw [hb,(Repair8.voltage_spec D P hD marked).2.1] at hpzero
  norm_num at hpzero

include hD in
/-- The proved cell route survives actual contraction, shortening when a P step collapses. -/
theorem cell_projected_near
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (o : Site 2) (i j : Fin 4) (hi : corner o i ∈ D) (hj : corner o j ∈ D) :
    project D P (corner o j) = project D P (corner o i) ∨
      (supportGraph (copyA D P marked) (copyB D P marked)).Adj
        (project D P (corner o i)) (project D P (corner o j)) ∨
      ∃ w, w ≠ alpha D P ∧
        (supportGraph (copyA D P marked) (copyB D P marked)).Adj (project D P (corner o i)) w ∧
        (supportGraph (copyA D P marked) (copyB D P marked)).Adj w (project D P (corner o j)) := by
  rcases two_step_cell_path D hD hDc o i j hi hj with he | he | ⟨w,hw,_hc,hiw,hwj⟩
  · exact Or.inl (congrArg (project D P) he.symm)
  · rcases internal_adj_projection D P marked hi hj he with he | he
    · exact Or.inl he.symm
    · exact Or.inr (Or.inl he)
  · rcases internal_adj_projection D P marked hi hw hiw with h1 | h1 <;>
      rcases internal_adj_projection D P marked hw hj hwj with h2 | h2
    · exact Or.inl (h1.trans h2).symm
    · exact Or.inr (Or.inl (by rwa [← h1] at h2))
    · exact Or.inr (Or.inl (by rwa [h2] at h1))
    · exact Or.inr (Or.inr ⟨project D P w,project_ne_alpha D P hw,h1,h2⟩)

/-- Actual corner voltages in every translated cell are positive and mutually within factor sixteen. -/
theorem cell_voltage_comparison
    (hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
    (_hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
    (o : Site 2) (i j : Fin 4) (hi : corner o i ∈ D) (hj : corner o j ∈ D) :
    0 < φ (project D P (corner o i)) ∧ 0 < φ (project D P (corner o j)) ∧
    φ (project D P (corner o j)) ≤ 16 * φ (project D P (corner o i)) ∧
    φ (project D P (corner o i)) ≤ 16 * φ (project D P (corner o j)) ∧
    (1/16 : ℝ) ≤ φ (project D P (corner o j)) / φ (project D P (corner o i)) ∧
    φ (project D P (corner o j)) / φ (project D P (corner o i)) ≤ 16 := by
  have hpi := voltage_pos_on_D D P hD marked hi
  have hpj := voltage_pos_on_D D P hD marked hj
  have ratios := LocalHarnack.ratio_bounds_of_near (copyA D P marked) (copyB D P marked)
    (alpha D P) (beta D P) φ (by
      intro x
      exact ⟨beta D P, by simp,
        (Repair8.graph_connected D P hD marked).preconnected x (beta D P)⟩)
    (Repair8.voltage_spec D P hD marked).1 (Repair8.voltage_spec D P hD marked).2.1
    (Repair8.voltage_spec D P hD marked).2.2 (source_free_degree_bound D P marked)
    (project_ne_alpha D P hi) (project_ne_alpha D P hj) hpi hpj
    (cell_projected_near D P hD marked hDc o i j hi hj)
  have hup := (div_le_iff₀ hpi).mp ratios.2
  have hlow := (le_div_iff₀ hpi).mp ratios.1
  exact ⟨hpi,hpj,hup,by linarith,ratios⟩

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CellVoltage10
