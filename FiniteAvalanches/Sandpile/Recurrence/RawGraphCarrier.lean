import FiniteAvalanches.Sandpile.Burning.SourceFields

/-! Raw stable integer heights on a finite loopless multigraph with one sink. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

abbrev Field := Burning.SourceVertex s → ℤ
def Stable (η : Field s) : Prop := ∀ x, η x < (Burning.degree G x.val : ℤ)
abbrev StableState := {η : Field s // Stable G s η}
def NoFSC (η : Field s) : Prop :=
  ∀ A : Finset (Burning.SourceVertex s),
    ¬(A.Nonempty ∧ ∀ x ∈ A, η x <
      (Burning.activeDegree G (Finset.univ.erase s) A x : ℤ))

theorem no_fsc_nonnegative {η : Field s} (h : NoFSC G s η) : ∀ x, 0 ≤ η x := by
  intro x
  by_contra hn
  apply h {x}
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  intro y hy
  have he : y = x := Finset.mem_singleton.mp hy
  subst y
  have hd : Burning.activeDegree G (Finset.univ.erase s) {x} x = 0 := by
    simp only [Burning.activeDegree, Finset.image_singleton, Burning.degree_into_self]
  rw [hd]
  omega

abbrev AllowedState := {η : StableState G s // NoFSC G s η.val}

def boundedHeights (η : AllowedState G s) : Burning.SourceHeights G s :=
  fun x => ⟨(η.val.val x).toNat, by
    have hs := η.val.property x
    have hn := no_fsc_nonnegative G s η.property x
    omega⟩

theorem bounded_heights_value (η : AllowedState G s) (x : Burning.SourceVertex s) :
    ((boundedHeights G s η x).val : ℤ) = η.val.val x :=
  Int.toNat_of_nonneg (no_fsc_nonnegative G s η.property x)

theorem bounded_heights_unique (η : AllowedState G s) (f : Burning.SourceHeights G s)
    (hf : ∀ x, ((f x).val : ℤ) = η.val.val x) : f = boundedHeights G s η := by
  funext x
  apply Fin.ext
  exact_mod_cast (hf x).trans (bounded_heights_value G s η x).symm

def allowedFieldEquiv : AllowedState G s ≃
    {h : Burning.SourceHeights G s // Burning.noForbidden G (Finset.univ.erase s) h} where
  toFun η := ⟨boundedHeights G s η, by
    intro A hf
    apply η.property A
    refine ⟨hf.1, ?_⟩
    intro x hx
    rw [← bounded_heights_value G s η x]
    exact_mod_cast hf.2 x hx⟩
  invFun h := ⟨⟨fun x => (h.val x).val, fun x => by
    change ((h.val x).val : ℤ) < (Burning.degree G x.val : ℤ)
    exact_mod_cast (h.val x).isLt⟩, by
    intro A hf
    apply h.property A
    refine ⟨hf.1, ?_⟩
    intro x hx
    have ht := hf.2 x hx
    change ((h.val x).val : ℤ) <
      (Burning.activeDegree G (Finset.univ.erase s) A x : ℤ) at ht
    exact_mod_cast ht⟩
  left_inv η := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact bounded_heights_value G s η x
  right_inv h := by
    apply Subtype.ext
    funext x
    apply Fin.ext
    exact Int.toNat_natCast (h.val x).val

end
end FiniteAvalanches.Sandpile.RawGraph
