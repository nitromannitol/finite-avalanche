import FiniteAvalanches.Wilson.Lattice.LocalComparison.ColorSwapLaw
import FiniteAvalanches.RevealedRoots.ExpectedContactLoss

set_option autoImplicit false
namespace LocalAnnulusHitting
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile.FiniteWired
open FiniteAvalanches.Needle FiniteAvalanches.RevealedRoots
open FiniteAvalanches.Wilson.Lattice MeasureTheory
open scoped Classical ENNReal
noncomputable section

/-- Inner-zero/exterior-one roots on the actual copied wired box. -/
def roots (N : ℕ) (S : Finset (Active N)) (hS : S.Nonempty) : RootPair where
  zero := S.image site
  one := (box 2 N)ᶜ
  disjoint := Set.disjoint_left.mpr (by
    intro x hx he
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact he ((inBox_iff N (site y)).mp (fun i => (y i).property)))
  zero_nonempty := by obtain ⟨y,hy⟩ := hS; exact ⟨site y,Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩
  one_nonempty := by
    obtain ⟨x,hx⟩ := (FiniteAvalanches.Sandpile.boxSites N).exists_notMem
    exact ⟨x,fun he => hx ((FiniteAvalanches.Sandpile.mem_box_sites N x).mpr
      ((inBox_iff N x).mpr he))⟩

/-- Hitting the inner one roots before exterior zero is the complemented voltage.
The color exchange is consumed as a proved law identity. -/
theorem reverse_hitting (N : ℕ) (S : Finset (Active N)) (hS : S.Nonempty) (x : Site 2) :
    walkLaw (hitBefore (box 2 N)ᶜ (S.image site) x) =
      ENNReal.ofReal (1-potential N S x) := by
  let R := roots N S hS
  have hm : MeasurableSet {σ : ColorField | σ x = true} :=
    (isClosed_eq (continuous_apply x : Continuous (fun σ : ColorField => σ x))
      continuous_const).measurableSet
  have he : LocalColorSwap.colors ⁻¹' {σ : ColorField | σ x = true} =
      ({σ : ColorField | σ x = true} : Set ColorField)ᶜ := by
    ext σ
    cases h : σ x <;> simp [LocalColorSwap.colors,h]
  calc
    _ = wilsonColorLaw (LocalColorSwap.roots R) {σ | σ x = true} :=
      (wilsonColorLaw_single_vertex _ x).symm
    _ = wilsonColorLaw R (LocalColorSwap.colors ⁻¹' {σ | σ x = true}) :=
      LocalColorSwap.probability_preimage R _ hm
    _ = 1-wilsonColorLaw R {σ | σ x = true} := by
      rw [he,measure_compl hm (measure_ne_top _ _),measure_univ]
    _ = 1-ENNReal.ofReal (potential N S x) := by
      rw [wilsonColorLaw_single_vertex]
      exact congrArg (fun z : ℝ≥0∞ => 1-z) (hitting_eq_potential N S x)
    _ = ENNReal.ofReal (1-potential N S x) := by
      rw [ENNReal.ofReal_sub _ (potential_nonneg N S x),ENNReal.ofReal_one]

/-- Enlarging one roots and reducing zero roots increases the ordered hitting event. -/
theorem hitting_mono (A C A' C' : Set (Site 2))
    (hA : A' ⊆ A) (hC : C ⊆ C') (x : Site 2) :
    hitBefore A C x ⊆ hitBefore A' C' x := by
  rintro w ⟨n,hn,ha⟩
  exact ⟨n,hC hn,fun m hm hz => ha m hm (hA hz)⟩

end
end LocalAnnulusHitting
