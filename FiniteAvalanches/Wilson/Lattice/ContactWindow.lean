import FiniteAvalanches.Trees.Lattice.FiniteContactStatistic
import FiniteAvalanches.Wilson.Lattice.ColorMonotonicity

/-! The count event is exactly a finite color-window event; no geometry or
probability law is supplied to this deterministic dictionary. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

/-- The literal projection of a contact event onto all neighbor colors used
by the count. -/
def contactWindowEvent (K : Finset (Site 2)) (D : Set ℕ) :
    Set (contactSites K → Bool) :=
  {p | ∃ σ : ColorField, contacts K σ ∈ D ∧ ∀ y : contactSites K, σ y.val = p y}

theorem contactWindowEvent_eq (K : Finset (Site 2)) (D : Set ℕ) :
    windowColorEvent (contactSites K) (contactWindowEvent K D) =
      {σ | contacts K σ ∈ D} := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, hagree⟩
    have he := contacts_of_agree K (σ := τ) (τ := σ)
      (fun y hy => hagree ⟨y, hy⟩)
    change contacts K σ ∈ D
    rw [← he]
    exact hτ
  · intro hσ
    exact ⟨σ, hσ, fun _ => rfl⟩

theorem measurableSet_contact_count_event (K : Finset (Site 2)) (D : Set ℕ) :
    MeasurableSet {σ : ColorField | contacts K σ ∈ D} := by
  rw [← contactWindowEvent_eq]
  exact (isClopen_windowColorEvent _ _).isClosed.measurableSet

end
end FiniteAvalanches.ConditioningConsumer
