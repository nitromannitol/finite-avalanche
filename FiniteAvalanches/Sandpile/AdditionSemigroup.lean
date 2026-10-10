import FiniteAvalanches.Sandpile.Sequential

set_option autoImplicit false
namespace FiniteAvalanches.Sandpile
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Transport of a stabilization domain along an equality of additions. -/
def domainCast {ξ ξ' : Counts} (h : ξ = ξ') (η : StabilizationDomain ξ) :
    StabilizationDomain ξ' :=
  ⟨η.val, by subst h; exact η.property⟩

theorem odometer_domainCast {ξ ξ' : Counts} (h : ξ = ξ') (η : StabilizationDomain ξ) :
    odometer ξ' (domainCast h η) = odometer ξ η := by
  subst h
  rfl

theorem addition_domainCast {ξ ξ' : Counts} (h : ξ = ξ') (η : StabilizationDomain ξ) :
    addition ξ' (domainCast h η) = addition ξ η := by
  subst h
  rfl

/-- The odometer of one field depends on the addition only through its value. -/
theorem odometer_congr {ξ ξ' : Counts} (h : ξ = ξ') (η : StableField)
    (h₁ : ∃ w, Stabilizes η ξ w) (h₂ : ∃ w, Stabilizes η ξ' w) :
    odometer ξ ⟨η, h₁⟩ = odometer ξ' ⟨η, h₂⟩ := by
  subst h
  rfl

theorem addition_congr {ξ ξ' : Counts} (h : ξ = ξ') (η : StableField)
    (h₁ : ∃ w, Stabilizes η ξ w) (h₂ : ∃ w, Stabilizes η ξ' w) :
    addition ξ ⟨η, h₁⟩ = addition ξ' ⟨η, h₂⟩ := by
  subst h
  rfl

/-- Equal input fields give equal outputs, whatever the stabilization proofs. -/
theorem addition_congr_field (ρ : Counts) {a b : StableField} (hab : a = b)
    (h₁ : ∃ w, Stabilizes a ρ w) (h₂ : ∃ w, Stabilizes b ρ w) :
    addition ρ ⟨a, h₁⟩ = addition ρ ⟨b, h₂⟩ := by
  subst hab
  rfl

/-- The zero addition is the identity with zero odometer. -/
theorem addition_zero (η : StableField) (h : ∃ w, Stabilizes η 0 w) :
    odometer 0 ⟨η, h⟩ = 0 ∧ addition 0 ⟨η, h⟩ = η := by
  have hoe : odometer 0 ⟨η, h⟩ = listCounts [] :=
    odometer_eq_counts 0 ⟨η, h⟩ (stabilizes_nil_zero η)
  have ho : odometer 0 ⟨η, h⟩ = 0 := by
    rw [hoe]
    ext x
    simp [listCounts_apply]
  refine ⟨ho, ?_⟩
  funext x
  apply Fin.ext
  have hx : ((addition 0 ⟨η, h⟩ x).val : ℤ) =
      initial η 0 x + lap (fun y => (odometer 0 ⟨η, h⟩ y : ℤ)) x :=
    addition_eq 0 ⟨η, h⟩ x
  rw [hoe] at hx
  have hn : initial η 0 x + lap (fun y => (listCounts ([] : List Site2) y : ℤ)) x =
      initial η 0 x := congrFun (height_after_nil (initial η 0)) x
  have hi : initial η 0 x = ((η x).val : ℤ) := by simp [initial]
  rw [hn, hi] at hx
  exact_mod_cast hx

/-- If both orders of two additions stabilize successively, the outputs and the
total odometers agree. -/
theorem addition_comm_of_sequential (ξ ζ : Counts) (η : StableField)
    (h₁ : ∃ w, Stabilizes η ξ w) (h₂ : ∃ w, Stabilizes η ζ w)
    (hζ : ∃ v, Stabilizes (addition ξ ⟨η, h₁⟩) ζ v)
    (hξ : ∃ v, Stabilizes (addition ζ ⟨η, h₂⟩) ξ v) :
    addition ζ ⟨addition ξ ⟨η, h₁⟩, hζ⟩ = addition ξ ⟨addition ζ ⟨η, h₂⟩, hξ⟩ ∧
      odometer ξ ⟨η, h₁⟩ + odometer ζ ⟨addition ξ ⟨η, h₁⟩, hζ⟩ =
        odometer ζ ⟨η, h₂⟩ + odometer ξ ⟨addition ζ ⟨η, h₂⟩, hξ⟩ := by
  have s₁ := exists_stabilization_add_of_sequential ξ ζ ⟨η, h₁⟩ hζ
  have s₂ := exists_stabilization_add_of_sequential ζ ξ ⟨η, h₂⟩ hξ
  have ca := addition_congr (add_comm ξ ζ) η s₁ s₂
  have co := odometer_congr (add_comm ξ ζ) η s₁ s₂
  exact ⟨(addition_add_of_sequential ξ ζ ⟨η, h₁⟩ hζ).symm.trans
      (ca.trans (addition_add_of_sequential ζ ξ ⟨η, h₂⟩ hξ)),
    (odometer_add_of_sequential ξ ζ ⟨η, h₁⟩ hζ).symm.trans
      (co.trans (odometer_add_of_sequential ζ ξ ⟨η, h₂⟩ hξ))⟩

/-- On a set of stable fields where every addition stabilizes and which every addition
preserves, additions compose, commute, and their odometers form a cocycle. -/
theorem addition_semigroup_on (Ω : Set StableField)
    (hst : ∀ η : StableField, η ∈ Ω → ∀ ξ : Counts, ∃ w, Stabilizes η ξ w)
    (hinv : ∀ η : StableField, ∀ hη : η ∈ Ω, ∀ ξ : Counts,
      addition ξ ⟨η, hst η hη ξ⟩ ∈ Ω)
    (η : StableField) (hη : η ∈ Ω) (ξ ζ : Counts) :
    addition (ξ + ζ) ⟨η, hst η hη (ξ + ζ)⟩ =
        addition ζ ⟨addition ξ ⟨η, hst η hη ξ⟩, hst _ (hinv η hη ξ) ζ⟩ ∧
    addition (ξ + ζ) ⟨η, hst η hη (ξ + ζ)⟩ =
        addition ξ ⟨addition ζ ⟨η, hst η hη ζ⟩, hst _ (hinv η hη ζ) ξ⟩ ∧
    odometer (ξ + ζ) ⟨η, hst η hη (ξ + ζ)⟩ =
        odometer ξ ⟨η, hst η hη ξ⟩ +
          odometer ζ ⟨addition ξ ⟨η, hst η hη ξ⟩, hst _ (hinv η hη ξ) ζ⟩ ∧
    odometer ξ ⟨η, hst η hη ξ⟩ +
        odometer ζ ⟨addition ξ ⟨η, hst η hη ξ⟩, hst _ (hinv η hη ξ) ζ⟩ =
      odometer ζ ⟨η, hst η hη ζ⟩ +
        odometer ξ ⟨addition ζ ⟨η, hst η hη ζ⟩, hst _ (hinv η hη ζ) ξ⟩ := by
  have c₁ : addition (ξ + ζ) ⟨η, hst η hη (ξ + ζ)⟩ =
      addition ζ ⟨addition ξ ⟨η, hst η hη ξ⟩, hst _ (hinv η hη ξ) ζ⟩ :=
    addition_add_of_sequential ξ ζ ⟨η, hst η hη ξ⟩ (hst _ (hinv η hη ξ) ζ)
  have c₃ : odometer (ξ + ζ) ⟨η, hst η hη (ξ + ζ)⟩ =
      odometer ξ ⟨η, hst η hη ξ⟩ +
        odometer ζ ⟨addition ξ ⟨η, hst η hη ξ⟩, hst _ (hinv η hη ξ) ζ⟩ :=
    odometer_add_of_sequential ξ ζ ⟨η, hst η hη ξ⟩ (hst _ (hinv η hη ξ) ζ)
  obtain ⟨ha, ho⟩ := addition_comm_of_sequential ξ ζ η (hst η hη ξ) (hst η hη ζ)
    (hst _ (hinv η hη ξ) ζ) (hst _ (hinv η hη ζ) ξ)
  exact ⟨c₁, c₁.trans ha, c₃, ho⟩

#print axioms FiniteAvalanches.Sandpile.domainCast
#print axioms FiniteAvalanches.Sandpile.odometer_domainCast
#print axioms FiniteAvalanches.Sandpile.addition_domainCast
#print axioms FiniteAvalanches.Sandpile.odometer_congr
#print axioms FiniteAvalanches.Sandpile.addition_congr
#print axioms FiniteAvalanches.Sandpile.addition_congr_field
#print axioms FiniteAvalanches.Sandpile.addition_zero
#print axioms FiniteAvalanches.Sandpile.addition_comm_of_sequential
#print axioms FiniteAvalanches.Sandpile.addition_semigroup_on

end
end FiniteAvalanches.Sandpile
