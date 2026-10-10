import FiniteAvalanches.Wilson.Lattice.ContactFirstExit
import FiniteAvalanches.External.KilledWiredVoltage
import FiniteAvalanches.RevealedRoots.FiniteContactLoss

set_option autoImplicit false
namespace FiniteAvalanches.RevealedRoots
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile.FiniteWired FiniteAvalanches.Needle
open scoped Classical ENNReal
noncomputable section

/-- The standard voltage representation on the actual wired lattice-site carrier. -/
theorem hitting_eq_potential (N : ℕ) (S : Finset (Active N)) (x : Site 2) :
    walkLaw (hitBefore (↑(S.image site) : Set (Site 2)) (box 2 N)ᶜ x) =
      ENNReal.ofReal (potential N S x) := by
  exact FiniteAvalanches.External.wired_srw_firstHit_voltage N S x

private theorem enlargedZero_sites_subset (h L : ℕ) (p : InBoxVertices h L)
    (K : Finset Point) (R : RootPair) (hR : R.zero = ↑(K ∪ target h L p.val)) :
    (↑((enlargedZero h L p K).image site) : Set (Site 2)) ⊆ R.zero := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  rw [hR]
  rcases Finset.mem_union.mp hx with hz | hk
  · exact Finset.mem_union_right K (Finset.mem_filter.mp hz).2
  · exact Finset.mem_union_left _ (Finset.mem_filter.mp hk).2

/-- Genuine Wilson color probability is bounded by the finite enlarged-zero voltage. -/
theorem one_probability_le_enlarged_potential (h L : ℕ) (p : InBoxVertices h L)
    (K : Finset Point) (R : RootPair) (hR : R.zero = ↑(K ∪ target h L p.val))
    (hC : R.one ⊆ (box 2 (2*h))ᶜ) (y : Site 2) :
    wilsonColorLaw R {σ | σ y = true} ≤
      ENNReal.ofReal (potential (2*h) (enlargedZero h L p K) y) := by
  rw [wilsonColorLaw_single_vertex, ← hitting_eq_potential]
  apply measure_mono
  rintro w ⟨n, hn, ha⟩
  exact ⟨n, hC hn, fun m hm hz =>
    ha m hm (enlargedZero_sites_subset h L p K R hR hz)⟩

/-- The paper's actual added-root expectation, using every original NN edge. -/
theorem expected_added_contacts_le_finite_sum (h L : ℕ) (p : InBoxVertices h L)
    (K : Finset Point) (R : RootPair) (hR : R.zero = ↑(K ∪ target h L p.val))
    (hC : R.one ⊆ (box 2 (2*h))ᶜ) :
    (∫⁻ σ, ∑ x ∈ target h L p.val \ K, ∑ y ∈ nbrFinset x,
      if σ y = true then (1 : ℝ≥0∞) else 0 ∂wilsonColorLaw R) ≤
      ENNReal.ofReal (∑ x ∈ target h L p.val \ K, ∑ y ∈ nbrFinset x,
        potential (2*h) (enlargedZero h L p K) y) := by
  rw [contact_expectation_eq_hitting,
    ENNReal.ofReal_sum_of_nonneg (fun x _ =>
      Finset.sum_nonneg (fun y _ => potential_nonneg _ _ y))]
  apply Finset.sum_le_sum
  intro x hx
  rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => potential_nonneg _ _ y)]
  apply Finset.sum_le_sum
  intro y hy
  rw [← wilsonColorLaw_single_vertex]
  exact one_probability_le_enlarged_potential h L p K R hR hC y

/-- A single geometric needle bounds the genuine expected added-root loss,
uniformly over the original connecting set and every admissible outgoing-root set. -/
theorem exists_needle_expected_added_contact_bound (h : ℕ) (hh : 10 ≤ h) (z : Point)
    (hz : Needle.radius z = 2*h) (K : Finset Point) :
    ∃ (L : ℕ) (p : InBoxVertices h L),
      Function.Injective p.val ∧ p.val ⟨0, by omega⟩ ∈ box 2 h ∧
      p.val ⟨L, by omega⟩ = z ∧
      (∀ t : Fin L, (lattice 2).Adj (p.val ⟨t.val, by omega⟩) (p.val ⟨t.val+1, by omega⟩)) ∧
      ∀ R : RootPair, R.zero = ↑(K ∪ target h L p.val) →
        R.one ⊆ (box 2 (2*h))ᶜ →
        (∫⁻ σ, ∑ x ∈ target h L p.val \ K, ∑ y ∈ nbrFinset x,
          if σ y = true then (1 : ℝ≥0∞) else 0 ∂wilsonColorLaw R) ≤
            ENNReal.ofReal (3840*Real.log (h+2)) := by
  obtain ⟨L,p,hi,hb,he,ha,hbound⟩ := exists_needle_added_contact_bound h hh z hz K
  refine ⟨L,p,hi,hb,he,ha,?_⟩
  intro R hR hC
  exact (expected_added_contacts_le_finite_sum h L p K R hR hC).trans
    (ENNReal.ofReal_le_ofReal hbound)

end
end FiniteAvalanches.RevealedRoots
