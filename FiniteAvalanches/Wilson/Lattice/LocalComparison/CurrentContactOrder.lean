import FiniteAvalanches.Paper.Current.DFRootOperations
import FiniteAvalanches.Wilson.Lattice.LocalComparison.ContactOrder

                                                                           
                                                                               
set_option autoImplicit false
namespace JointCurrentContactOrder
open LatticeProb MeasureTheory FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile
open FiniteAvalanches (siteRadius)
open scoped Classical
noncomputable section

theorem local_event_mono_cofinite (R Q : RootPair)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (A : Set (Site 2)) (a : Site 2) (r : ℕ) (t : ℝ) :
    (wilsonColorLaw Q).real (localContactEvent A a r t) ≤
      (wilsonColorLaw R).real (localContactEvent A a r t) := by
  apply FiniteAvalanches.Paper.CurrentDF176.source_four_sets_global_mono
    R.zero Q.zero R.one Q.one R.zero_nonempty Q.one_nonempty hzero hone
    R.disjoint Q.disjoint hR hQ _
    (isClopen_localContactEvent A a r t).isClosed.measurableSet
  intro p hp q hpq
  change t ≤ (contacts ((window a r).filter (fun x => x ∈ A)) p : ℝ) at hp
  change t ≤ (contacts ((window a r).filter (fun x => x ∈ A)) q : ℝ)
  exact hp.trans (Nat.cast_le.mpr (JointContactOrder.contacts_mono _ p q hpq))

theorem k_event_mono_cofinite (R Q : RootPair)
    (hR : (R.zero ∪ R.one)ᶜ.Finite) (hQ : (Q.zero ∪ Q.one)ᶜ.Finite)
    (hzero : R.zero ⊆ Q.zero) (hone : Q.one ⊆ R.one)
    (K : Finset (Site 2)) (r t : ℝ) :
    (wilsonColorLaw Q).real (kContactEvent K r t) ≤
      (wilsonColorLaw R).real (kContactEvent K r t) := by
  apply FiniteAvalanches.Paper.CurrentDF176.source_four_sets_global_mono
    R.zero Q.zero R.one Q.one R.zero_nonempty Q.one_nonempty hzero hone
    R.disjoint Q.disjoint hR hQ _
    (isClopen_kContactEvent K r t).isClosed.measurableSet
  intro p hp q hpq
  change t ≤ (contacts (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ r)) p : ℝ) at hp
  change t ≤ (contacts (K.filter (fun x => (siteRadius 0 x : ℝ) ≤ r)) q : ℝ)
  exact hp.trans (Nat.cast_le.mpr (JointContactOrder.contacts_mono _ p q hpq))

end
end JointCurrentContactOrder

open Lean Elab Command in
run_cmd do
  for (old, current) in [
      (`JointContactOrder.local_event_mono_cofinite,
        `JointCurrentContactOrder.local_event_mono_cofinite),
      (`JointContactOrder.k_event_mono_cofinite,
        `JointCurrentContactOrder.k_event_mono_cofinite)] do
    let before ← getConstInfo old
    let after ← getConstInfo current
    unless before.type == after.type do
      throwError "Current consumer type mismatch: {old}"
  logInfo "EXACT_LOCAL_AND_REVEALED_CONSUMER_TYPES: structurally identical"

#print axioms JointCurrentContactOrder.local_event_mono_cofinite
#print axioms JointCurrentContactOrder.k_event_mono_cofinite
