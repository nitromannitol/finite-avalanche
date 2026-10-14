import FiniteAvalanches.Wilson.Lattice.ColoredForests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.CurrentRootChanges
open LatticeProb
open scoped Classical

/-- The current source's intermediate roots after removing precisely the
one roots outside the union of the final roots. -/
def intermediate (R Q : RootPair) (hone : Q.one ⊆ R.one) : RootPair where
  zero := R.zero
  one := R.one ∩ (Q.zero ∪ Q.one)
  disjoint := R.disjoint.mono_right Set.inter_subset_left
  zero_nonempty := R.zero_nonempty
  one_nonempty := by
    obtain ⟨x, hx⟩ := Q.one_nonempty
    exact ⟨x, hone hx, Or.inr hx⟩

theorem removed_one_roots (R Q : RootPair) (hone : Q.one ⊆ R.one) :
    R.one \ (intermediate R Q hone).one = R.one \ (Q.zero ∪ Q.one) := by
  ext x
  simp only [intermediate, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union]
  tauto

/-- Both actual source domain conditions imply the intermediate domain condition. -/
theorem intermediate_union_cofinite (R Q : RootPair) (hone : Q.one ⊆ R.one)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite) :
    ((intermediate R Q hone).zero ∪ (intermediate R Q hone).one)ᶜ.Finite := by
  apply (hR.union hQ).subset
  intro x hx
  by_cases hR0 : x ∈ R.zero
  · exact (hx (Or.inl hR0)).elim
  · by_cases hR1 : x ∈ R.one
    · right
      intro hQx
      exact hx (Or.inr ⟨hR1, hQx⟩)
    · left
      exact fun h => h.elim hR0 hR1

theorem intermediate_subset_final_roots (R Q : RootPair)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one) :
    (intermediate R Q hone).zero ∪ (intermediate R Q hone).one ⊆ Q.zero ∪ Q.one := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (hzero hx)
  · exact hx.2

/-- The current Step2 adds exactly Aprime outside the original total roots. -/
theorem added_final_roots (R Q : RootPair) (hone : Q.one ⊆ R.one) :
    (Q.zero ∪ Q.one) \ ((intermediate R Q hone).zero ∪ (intermediate R Q hone).one) =
      Q.zero \ (R.zero ∪ R.one) := by
  ext x
  simp only [intermediate, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union]
  constructor
  · rintro ⟨hxQ, hnot⟩
    have hxQ0 : x ∈ Q.zero := hxQ.resolve_right (fun hxQ1 =>
      hnot (Or.inr ⟨hone hxQ1, Or.inr hxQ1⟩))
    refine ⟨hxQ0, ?_⟩
    rintro (hxR0 | hxR1)
    · exact hnot (Or.inl hxR0)
    · exact hnot (Or.inr ⟨hxR1, Or.inl hxQ0⟩)
  · rintro ⟨hxQ0, hnot⟩
    refine ⟨Or.inl hxQ0, ?_⟩
    rintro (hxR0 | hxM1)
    · exact hnot (Or.inl hxR0)
    · exact hnot (Or.inr hxM1.1)

/-- The retained original one-roots that change label are exactly Gamma intersect Aprime. -/
theorem reclassified_one_roots (R Q : RootPair) (hone : Q.one ⊆ R.one) :
    (intermediate R Q hone).one ∩ Q.zero = R.one ∩ Q.zero := by
  ext x
  simp only [intermediate, Set.mem_inter_iff, Set.mem_union]
  tauto

end FiniteAvalanches.Wilson.Lattice.CurrentRootChanges
