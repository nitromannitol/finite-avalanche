import FiniteAvalanches.Sandpile.Law.FiniteVolume

/-! Integer stable sandpiles retain negative heights until NoFSC excludes them. -/
namespace FiniteAvalanches.Sandpile.RawInteger
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

abbrev Field (Γ : Finset Site2) := Γ → ℤ
def Stable {Γ : Finset Site2} (η : Field Γ) : Prop := ∀ x, η x < 4
abbrev StableState (Γ : Finset Site2) := {η : Field Γ // Stable η}

def NoFSC {Γ : Finset Site2} (η : Field Γ) : Prop :=
  ∀ (A : Finset Site2) (hA : A ⊆ Γ),
    ¬(A.Nonempty ∧ ∀ (x : Site2) (hx : x ∈ A), η ⟨x, hA hx⟩ < (Waves.degree A x : ℤ))

/-- Auxiliary zero extension records the finite source domain explicitly. -/
def extend {Γ : Finset Site2} (η : Field Γ) (x : Site2) : ℤ :=
  if hx : x ∈ Γ then η ⟨x, hx⟩ else 0

theorem extend_site {Γ : Finset Site2} (η : Field Γ) (x : Γ) : extend η x.val = η x := by
  simp only [extend, dif_pos x.property]

theorem no_fsc_iff_allowed {Γ : Finset Site2} (η : Field Γ) :
    NoFSC η ↔ Waves.allowed Γ (extend η) := by
  constructor <;> intro h A hA hf <;> apply h A hA
  · exact ⟨hf.1, fun x hx => by
      have ht := hf.2 x hx
      simpa only [extend, dif_pos (hA hx)] using ht⟩
  · exact ⟨hf.1, fun x hx => by
      simpa only [extend, dif_pos (hA hx)] using hf.2 x hx⟩

theorem no_fsc_nonnegative {Γ : Finset Site2} {η : Field Γ} (h : NoFSC η) :
    ∀ x, 0 ≤ η x := by
  intro x
  by_contra hn
  apply h {x.val} (by simpa only [Finset.singleton_subset_iff] using x.property)
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  intro y hy
  have he : y = x.val := Finset.mem_singleton.mp hy
  subst y
  have hd : Waves.degree {x.val} x.val = 0 := by
    simp only [Waves.degree,
      Finset.inter_singleton_of_notMem (Waves.not_mem_neighbors_self x.val), Finset.card_empty]
  rw [hd]
  change η x < (0 : ℤ)
  omega

/-- The finite-height representative is constructed only after its nonnegativity proof. -/
def boundedHeights {Γ : Finset Site2} (η : StableState Γ)
    (hn : ∀ x, 0 ≤ η.val x) : Γ → Fin 4 := fun x =>
  ⟨(η.val x).toNat, by have hs := η.property x; have hp := hn x; omega⟩

theorem bounded_heights_value {Γ : Finset Site2} (η : StableState Γ)
    (hn : ∀ x, 0 ≤ η.val x) (x : Γ) :
    ((boundedHeights η hn x).val : ℤ) = η.val x := Int.toNat_of_nonneg (hn x)

theorem bounded_heights_unique {Γ : Finset Site2} (η : StableState Γ)
    (hn : ∀ x, 0 ≤ η.val x) (f : Γ → Fin 4)
    (hf : ∀ x, ((f x).val : ℤ) = η.val x) : f = boundedHeights η hn := by
  funext x
  apply Fin.ext
  have he := (hf x).trans (bounded_heights_value η hn x).symm
  exact_mod_cast he

abbrev AllowedState (Γ : Finset Site2) := {η : StableState Γ // NoFSC η.val}

def allowedEmbedding {Γ : Finset Site2} (η : AllowedState Γ) : StableField :=
  fun x => if hx : x ∈ Γ then boundedHeights η.val (no_fsc_nonnegative η.property) ⟨x, hx⟩
    else 0

theorem allowed_embedding_value {Γ : Finset Site2} (η : AllowedState Γ) (x : Γ) :
    ((allowedEmbedding η x.val).val : ℤ) = η.val.val x := by
  simp only [allowedEmbedding, dif_pos x.property]
  exact bounded_heights_value _ _ x

theorem allowed_embedding_mem {Γ : Finset Site2} (η : AllowedState Γ) :
    allowedEmbedding η ∈ FiniteAvalanches.External.SandpileLimit.allowedFields Γ := by
  refine ⟨fun x hx => by simp only [allowedEmbedding, dif_neg hx], ?_⟩
  apply (Waves.allowed_congr (h := extend η.val.val) ?_).mp
    ((no_fsc_iff_allowed η.val.val).mp η.property)
  intro x hx
  exact (extend_site η.val.val ⟨x, hx⟩).trans (allowed_embedding_value η ⟨x, hx⟩).symm

def allowedRestriction (Γ : Finset Site2)
    (ζ : FiniteAvalanches.External.SandpileLimit.allowedFields Γ) : AllowedState Γ :=
  ⟨⟨fun x => (ζ.val x.val).val, fun x => by
      change ((ζ.val x.val).val : ℤ) < 4
      exact_mod_cast (ζ.val x.val).isLt⟩,
    (no_fsc_iff_allowed _).mpr ((Waves.allowed_congr (h := fun x => ((ζ.val x).val : ℤ))
      (fun x hx => (extend_site (fun y : Γ => ((ζ.val y.val).val : ℤ)) ⟨x, hx⟩).symm)).mp
      ζ.property.2)⟩

def allowedFieldEquiv (Γ : Finset Site2) :
    AllowedState Γ ≃ FiniteAvalanches.External.SandpileLimit.allowedFields Γ where
  toFun η := ⟨allowedEmbedding η, allowed_embedding_mem η⟩
  invFun := allowedRestriction Γ
  left_inv η := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact allowed_embedding_value η x
  right_inv ζ := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ Γ
    · apply Fin.ext
      have he := allowed_embedding_value (allowedRestriction Γ ζ) ⟨x, hx⟩
      change ((allowedEmbedding (allowedRestriction Γ ζ) x).val : ℤ) =
        ((ζ.val x).val : ℤ) at he
      change (allowedEmbedding (allowedRestriction Γ ζ) x).val = (ζ.val x).val
      exact_mod_cast he
    · exact (show allowedEmbedding (allowedRestriction Γ ζ) x = 0 from by
        simp only [allowedEmbedding, dif_neg hx]).trans (ζ.property.1 x hx).symm

instance (Γ : Finset Site2) : Fintype (AllowedState Γ) :=
  Fintype.ofEquiv _ (allowedFieldEquiv Γ).symm
instance (Γ : Finset Site2) : Nonempty (AllowedState Γ) :=
  Nonempty.map (allowedFieldEquiv Γ).symm inferInstance

end
end FiniteAvalanches.Sandpile.RawInteger
