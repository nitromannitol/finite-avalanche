module

public import FiniteAvalanches.Sandpile.Burning.Restriction

@[expose] public section

/-! Two-phase forbidden-set characterization for every stable copied-edge field.
The converse proves both absence of forbidden sets and the exact operational
stopping set. It does not assume either conclusion. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (U : Finset V)

theorem active_degree_le_sdiff_add (H A : Finset (InducedVertex U)) (x : InducedVertex U) :
    activeDegree G U H x ≤ activeDegree G U (H \ A) x + activeDegree G U A x := by
  have hsub : H ⊆ (H \ A) ∪ A := by intro y hy; by_cases ha : y ∈ A <;> simp_all
  exact (active_degree_mono G U hsub x).trans (by
    rw [active_degree_union G U Finset.sdiff_disjoint])

theorem held_field_iff (h : Heights G U) (B A : Finset (InducedVertex U)) (hBA : B ⊆ A) :
    (noForbidden G U h ∧ heldBurning G U h B = A) ↔
      (∀ x ∈ A, x ∉ B → (h x).val < activeDegree G U A x) ∧
      (∀ H ⊆ A, ¬(H.Nonempty ∧ ∀ x ∈ H, (h x).val < activeDegree G U H x)) ∧
      (∀ x ∉ A, activeDegree G U A x ≤ (h x).val) ∧
      (∀ H ⊆ Finset.univ \ A, ¬(H.Nonempty ∧ ∀ x ∈ H,
        (h x).val - activeDegree G U A x < activeDegree G U H x)) := by
  constructor
  · rintro ⟨hn, rfl⟩
    exact ⟨(held_burning_largest G U h B).1.2, fun H _ => hn H,
      height_ge_active_degree_outside G U h B, outer_shift_no_forbidden G U h B⟩
  · rintro ⟨hi, hnA, hlo, hnD⟩
    have hpart : ∀ H : Finset (InducedVertex U),
        (∀ x ∈ H, (h x).val < activeDegree G U H x) → H ⊆ A := by
      intro H hf
      by_contra hnot
      apply hnD (H \ A)
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
      · refine ⟨Finset.sdiff_nonempty.mpr hnot, ?_⟩
        intro x hx
        have hh := hf x (Finset.mem_sdiff.mp hx).1
        have hl := hlo x (Finset.mem_sdiff.mp hx).2
        have hd := active_degree_le_sdiff_add G U H A x
        omega
    refine ⟨?_, (held_burning_eq_iff G U h B A).mpr ⟨⟨hBA, hi⟩, ?_⟩⟩
    · intro H hf
      exact hnA H (hpart H hf.2) hf
    · intro D hd
      by_contra hnot
      apply hnD (D \ A)
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
      · refine ⟨Finset.sdiff_nonempty.mpr hnot, ?_⟩
        intro x hx
        have hxD := (Finset.mem_sdiff.mp hx).1
        have hxA := (Finset.mem_sdiff.mp hx).2
        have hxB : x ∉ B := fun hb => hxA (hBA hb)
        have hh := hd.2 x hxD hxB
        have hl := hlo x hxA
        have hdeg := active_degree_le_sdiff_add G U D A x
        omega

end
end FiniteAvalanches.Sandpile.Burning
