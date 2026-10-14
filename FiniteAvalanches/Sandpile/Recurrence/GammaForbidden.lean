import FiniteAvalanches.Sandpile.Recurrence.GammaDegrees
import FiniteAvalanches.Sandpile.Recurrence.RawIntegerCarrier

/-! Literal finite-subset reindexing, including the empty Gamma carrier. -/
namespace FiniteAvalanches.Sandpile.RawInteger
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem no_fsc_subtype_iff {Γ : Finset Site2} (η : Field Γ) : NoFSC η ↔
    ∀ S : Finset Γ, ¬(S.Nonempty ∧ ∀ x ∈ S,
      η x < (Waves.degree (S.image Subtype.val) x.val : ℤ)) := by
  constructor
  · intro h S hf
    have hS : S.image Subtype.val ⊆ Γ := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
      exact x.property
    apply h (S.image Subtype.val) hS
    refine ⟨hf.1.image _, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hf.2 x hx
  · intro h A hA hf
    let S : Finset Γ := Finset.univ.filter fun x => x.val ∈ A
    have hi : S.image Subtype.val = A := by
      ext y
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hy; exact ⟨⟨y, hA hy⟩, hy, rfl⟩
    apply h S
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hf.1
      exact ⟨⟨x, hA hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    · intro x hx
      rw [hi]
      exact hf.2 x.val (Finset.mem_filter.mp hx).2

end
end FiniteAvalanches.Sandpile.RawInteger
