import FiniteAvalanches.Wilson.Lattice.LocalComparison.MomentLaw
import FiniteAvalanches.Wilson.Lattice.LocalComparison.FullContacts

set_option autoImplicit false
namespace LocalContactSupport
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.Plane.SourceLattice MeasureTheory
open scoped Classical BigOperators ENNReal
noncomputable section

theorem full_eq_exterior (D : Finset (Site 2)) (A : Set (Site 2))
    (hA : A ⊆ (D : Set (Site 2))ᶜ) (σ : ColorField)
    (hσ : ∀ x ∉ D, σ x = false) :
    LocalFullContacts.full A σ = (LocalBoxContraction.exteriorContacts D A σ : ℝ≥0∞) := by
  let K := (LocalBoxContraction.exteriorSites D).filter (fun x => x ∈ A)
  have hz (x : Site 2) (hx : x ∉ K) :
      (if x ∈ A then ∑ y ∈ nbrFinset x,
        if σ y = true then (1 : ℝ≥0∞) else 0 else 0) = 0 := by
    by_cases hxA : x ∈ A
    · rw [if_pos hxA]
      apply Finset.sum_eq_zero
      intro y hy
      have hyD : y ∉ D := by
        intro hyD
        apply hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hA hxA⟩, hxA⟩
        exact Finset.mem_biUnion.mpr ⟨y, hyD,
          (FiniteWired.mem_neighbors_iff y x).mpr ((FiniteWired.mem_neighbors_iff x y).mp hy).symm⟩
      rw [hσ y hyD]
      rfl
    · exact if_neg hxA
  rw [LocalFullContacts.full, tsum_eq_sum hz]
  change (∑ x ∈ K, _) = (contacts K σ : ℝ≥0∞)
  rw [LocalFullContacts.cast_contacts]
  apply Finset.sum_congr rfl
  intro x hx
  rw [if_pos (Finset.mem_filter.mp hx).2]

theorem exterior_eq_window (r : ℕ) (hr : 1 ≤ r) (D : Finset (Site 2))
    (hDB : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2)))
    (A : Set (Site 2)) (hA : A ⊆ (D : Set (Site 2))ᶜ)
    (σ : ColorField) (hσ : ∀ x ∉ D, σ x = false) :
    LocalBoxContraction.exteriorContacts D A σ = localContacts A 0 (2*r) σ := by
  have h := (full_eq_exterior D A hA σ hσ).symm.trans
    (LocalFullContacts.full_eq_window D A (2*r-1) hDB σ hσ)
  have he : 2*r-1+1 = 2*r := by omega
  rw [he] at h
  exact_mod_cast h

/-- The marked origin incidence makes the source PZ observable nonnegative on every actual forest. -/
theorem exterior_at_least_one (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (F : LocalBoxContraction.ReferenceForest D P marked)
    (A : Set (Site 2)) (h0 : (0 : Site 2) ∈ A) (h0D : (0 : Site 2) ∉ D)
    (b : Site 2) (hbP : b ∈ P.val.image Subtype.val) (hadj : (lattice 2).Adj 0 b) :
    1 ≤ LocalBoxContraction.exteriorContacts D A (LocalBoxContraction.referenceField D P marked F) := by
  have hbD : b ∈ D := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hbP
    exact x.property
  have h0K : (0 : Site 2) ∈ (LocalBoxContraction.exteriorSites D).filter (fun x => x ∈ A) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_,h0D⟩,h0⟩
    exact Finset.mem_biUnion.mpr ⟨b,hbD,(FiniteWired.mem_neighbors_iff b 0).mpr hadj.symm⟩
  have hbN : b ∈ nbrFinset (0 : Site 2) := (FiniteWired.mem_neighbors_iff 0 b).mpr hadj
  have hbTrue := LocalBoxContraction.reference_field_P D P marked F b hbP
  unfold LocalBoxContraction.exteriorContacts contacts
  have hn := Finset.single_le_sum (s := nbrFinset (0 : Site 2))
    (f := fun y => if LocalBoxContraction.referenceField D P marked F y then (1 : ℕ) else 0)
    (fun y _ => Nat.zero_le _) hbN
  simp only [hbTrue, ↓reduceIte] at hn
  exact hn.trans (Finset.single_le_sum
    (f := fun x => ∑ y ∈ nbrFinset x, if LocalBoxContraction.referenceField D P marked F y then (1 : ℕ) else 0)
    (fun x _ => Nat.zero_le _) h0K)

end
end LocalContactSupport
