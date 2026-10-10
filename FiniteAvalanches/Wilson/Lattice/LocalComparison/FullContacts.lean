import FiniteAvalanches.Wilson.Lattice.LocalComparison.SourceNetwork
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ZeroExteriorLaw
import FiniteAvalanches.Wilson.Lattice.ContactFirstExit
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
namespace LocalFullContacts
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.Lattice MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- The full original lattice-incidence count, allowing an infinite zero set. -/
def full (A : Set (Site 2)) (σ : ColorField) : ℝ≥0∞ :=
  ∑' x : Site 2, if x ∈ A then
    ∑ y ∈ nbrFinset x, if σ y = true then (1 : ℝ≥0∞) else 0 else 0

theorem measurable_full (A : Set (Site 2)) : Measurable (full A) := by
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ A
  · simp only [if_pos hx]
    apply Finset.measurable_sum
    intro y _
    exact Measurable.ite
      ((isClosed_eq (continuous_apply y : Continuous (fun σ : ColorField => σ y))
        continuous_const).measurableSet) measurable_const measurable_const
  · simp only [if_neg hx]
    exact measurable_const

theorem cast_contacts (K : Finset (Site 2)) (σ : ColorField) :
    (contacts K σ : ℝ≥0∞) =
      ∑ x ∈ K, ∑ y ∈ nbrFinset x, if σ y = true then (1 : ℝ≥0∞) else 0 := by
  simp only [contacts, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  cases σ y <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, Nat.cast_one]

/-- The actual Wilson law is supported on fields whose one sites lie in D. -/
theorem ae_support (D : Finset (Site 2)) (P : FiniteAvalanches.Electrical.Plane.SourceLattice.OneSet D) :
    ∀ᵐ σ ∂wilsonColorLaw (LocalZeroExterior.domainRoots D P),
      ∀ x ∉ D, σ x = false := by
  let R := LocalZeroExterior.domainRoots D P
  have hm : MeasurableSet {σ : ColorField | ∀ x ∉ D, σ x = false} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro x
    by_cases hx : x ∈ D
    · simp only [hx, not_true_eq_false, IsEmpty.forall_iff, Set.setOf_true]
      exact MeasurableSet.univ
    · simp only [hx, not_false_eq_true, forall_true_left]
      exact (isClosed_eq (continuous_apply x : Continuous (fun σ : ColorField => σ x))
        continuous_const).measurableSet
  apply (ae_map_iff measurable_snd.aemeasurable hm).mpr
  filter_upwards [wilsonLaw_ae_root_colors R] with ω hω
  exact hω.2

theorem window_zero (N : ℕ) : window 0 N = boxSites N := by
  ext x
  simp only [window, Finset.mem_image, zero_add, exists_eq_right]

theorem neighbor_box (N : ℕ) (x y : Site 2) (hy : y ∈ boxSites N)
    (hxy : y ∈ nbrFinset x) : x ∈ boxSites (N+1) := by
  have ha := (FiniteWired.mem_neighbors_iff x y).mp hxy
  have ht := JointMetricGeometry.radius_triangle 0 y x
  have hs := JointMetricGeometry.radius_adj_le_one y x ha.symm
  have hyr : siteRadius 0 y ≤ N := by
    rw [← mem_window 0 y N]
    simpa only [window_zero] using hy
  have hxr : siteRadius 0 x ≤ N+1 := ht.trans (Nat.add_le_add hyr hs)
  apply (mem_box_sites _ _).mpr
  intro i
  simpa only [Pi.zero_apply,sub_zero,abs_le] using (siteRadius_le_iff 0 x (N+1)).mp hxr i

/-- Finiteness is proved for the full count, without changing its observable. -/
theorem full_eq_window (D : Finset (Site 2)) (A : Set (Site 2)) (N : ℕ)
    (hD : (D : Set (Site 2)) ⊆ (boxSites N : Set (Site 2)))
    (σ : ColorField) (hσ : ∀ x ∉ D, σ x = false) :
    full A σ = (localContacts A 0 (N+1) σ : ℝ≥0∞) := by
  have hz (x : Site 2) (hx : x ∉ (window 0 (N+1)).filter (fun x => x ∈ A)) :
      (if x ∈ A then ∑ y ∈ nbrFinset x,
        if σ y = true then (1 : ℝ≥0∞) else 0 else 0) = 0 := by
    by_cases hxA : x ∈ A
    · rw [if_pos hxA]
      apply Finset.sum_eq_zero
      intro y hy
      have hyD : y ∉ D := by
        intro hyD
        apply hx
        refine Finset.mem_filter.mpr ⟨?_,hxA⟩
        simpa only [window_zero] using neighbor_box N x y (hD hyD) hy
      rw [hσ y hyD]
      rfl
    · exact if_neg hxA
  rw [full, tsum_eq_sum hz, localContacts, cast_contacts]
  apply Finset.sum_congr rfl
  intro x hx
  rw [if_pos (Finset.mem_filter.mp hx).2]

/-- Every unwanted nonzero original incidence has its exterior endpoint beyond B_N. -/
theorem unwanted_endpoint (N : ℕ) (A : Set (Site 2))
    (b : (boxSites N).filter (fun x => x ∉ A)) (x y : Site 2)
    (hx : x ∈ (JointFiniteComponent.componentSites
      ((boxSites N).filter (fun x => x ∉ A)) b : Set (Site 2))ᶜ \ A)
    (hy : y ∈ JointFiniteComponent.componentSites ((boxSites N).filter (fun x => x ∉ A)) b)
    (hxy : y ∈ nbrFinset x) : x ∉ boxSites N := by
  exact JointFiniteComponent.unwanted_neighbor_outside N A b y x hy hx.1 hx.2
    ((FiniteWired.mem_neighbors_iff x y).mp hxy).symm

end
end LocalFullContacts
