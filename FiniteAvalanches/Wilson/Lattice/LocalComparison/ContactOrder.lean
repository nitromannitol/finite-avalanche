import FiniteAvalanches.Paper.Revision480.LatticeColorMonotonicity
import FiniteAvalanches.Wilson.Lattice.ForestEvents
import FiniteAvalanches.Sandpile.Observables

set_option autoImplicit false
namespace JointContactOrder
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile
open FiniteAvalanches (siteRadius)
open scoped Classical BigOperators
noncomputable section

theorem contacts_mono (F : Finset (Site 2)) (p q : ColorField)
    (hpq : ∀ x, p x = true → q x = true) : contacts F p ≤ contacts F q := by
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  by_cases hp : p y = true
  · simp only [hp, hpq y hp, ↓reduceIte, le_refl]
  · simp only [hp]
    exact Nat.zero_le _

theorem contacts_subset (F G : Finset (Site 2)) (hFG : F ⊆ G) (p : ColorField) :
    contacts F p ≤ contacts G p :=
  Finset.sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => Nat.zero_le _)

theorem local_event_mono_cofinite (R Q : RootPair)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (A : Set (Site 2)) (a : Site 2) (r : ℕ) (t : ℝ) :
    (wilsonColorLaw Q).real (localContactEvent A a r t) ≤
      (wilsonColorLaw R).real (localContactEvent A a r t) := by
  apply FiniteAvalanches.Paper.Revision480.color_event_mono_cofinite
    R Q hR hQ hzero hone _ (isClopen_localContactEvent A a r t).isClosed.measurableSet
  intro p hp q hpq
  change t ≤ (contacts ((window a r).filter (fun x => x ∈ A)) p : ℝ) at hp
  change t ≤ (contacts ((window a r).filter (fun x => x ∈ A)) q : ℝ)
  exact hp.trans (Nat.cast_le.mpr (contacts_mono _ p q hpq))

theorem k_event_mono_cofinite (R Q : RootPair)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (K : Finset (Site 2)) (r t : ℝ) :
    (wilsonColorLaw Q).real (kContactEvent K r t) ≤
      (wilsonColorLaw R).real (kContactEvent K r t) := by
  apply FiniteAvalanches.Paper.Revision480.color_event_mono_cofinite
    R Q hR hQ hzero hone _ (isClopen_kContactEvent K r t).isClosed.measurableSet
  intro p hp q hpq
  change t ≤ (contacts (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ r)) p : ℝ) at hp
  change t ≤ (contacts (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ r)) q : ℝ)
  exact hp.trans (Nat.cast_le.mpr (contacts_mono _ p q hpq))

theorem union_roots_cofinite (R : RootPair) (γ : Set (Site 2))
    (hγ : γᶜ.Finite) (hγR : γ ⊆ R.one) : (R.zero ∪ R.one)ᶜ.Finite := by
  apply hγ.subset
  intro x hx hmem
  exact hx (Or.inr (hγR hmem))

theorem contacts_union_le (K Z F : Finset (Site 2))
    (hF : F ⊆ K ∪ Z) (σ : ColorField) :
    contacts F σ ≤ contacts (F ∩ K) σ + contacts (Z \ K) σ := by
  have hs : F ⊆ (F ∩ K) ∪ (Z \ K) := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxK⟩)
    · have hxZ := (Finset.mem_union.mp (hF hx)).resolve_left hxK
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxZ, hxK⟩)
  have hd : Disjoint (F ∩ K) (Z \ K) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
  exact (contacts_subset _ _ hs σ).trans_eq (Finset.sum_union hd)

end
end JointContactOrder
