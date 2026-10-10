import FiniteAvalanches.Wilson.Lattice.TranslationExpectation
import FiniteAvalanches.Wilson.Lattice.ReciprocalContactMonotonicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CofiniteReciprocalGeometry
open LatticeProb FiniteAvalanches Sandpile MeasureTheory Translation
open scoped Classical
noncomputable section

/-- The contact statistic retains all original incidences and is finite and measurable. -/
theorem actual_contacts_finite_measurable (K : Finset (Site 2)) :
    (∀ σ : ColorField, contacts K σ ≤ 4 * K.card) ∧ Measurable (contacts K) :=
  ⟨contacts_le_four_mul_card K, (continuous_contacts K).measurable⟩

/-- The literal neighboring one-root supplies one counted original incidence. -/
theorem actual_contacts_pos (K : Finset (Site 2)) (γ : Set (Site 2))
    (h0 : (0 : Site 2) ∈ K) (hb : ∃ b ∈ γ, (lattice 2).Adj 0 b)
    (R : RootPair) (hone : R.one = γ) :
    ∀ᵐ σ ∂wilsonColorLaw R, 1 ≤ contacts K σ := by
  obtain ⟨b, hb, hadj⟩ := hb
  exact contacts_ge_one_ae_of_adjacent_one_root R K 0 b h0 (hone.symm ▸ hb) hadj

/-- Translation preserves induced connectedness of the entire set. -/
theorem connected_set_translate (A : Set (Site 2)) (z : Site 2)
    (h : ((lattice 2).induce A).Connected) :
    ((lattice 2).induce {x | x - z ∈ A}).Connected := by
  let φ : (lattice 2).induce A →g (lattice 2).induce {x | x - z ∈ A} := {
    toFun := fun x => ⟨x.val + z, by change x.val + z - z ∈ A; simpa only [add_sub_cancel_right] using x.property⟩
    map_rel' := fun hxy => (adjacency_add _ _ z).mpr hxy }
  apply SimpleGraph.Connected.map φ _ h
  intro x
  refine ⟨⟨x.val - z, x.property⟩, ?_⟩
  exact Subtype.ext (sub_add_cancel x.val z)

/-- The entire translated gamma remains cofinite. -/
theorem cofinite_set_translate (A : Set (Site 2)) (z : Site 2) (h : Aᶜ.Finite) :
    ({x : Site 2 | x - z ∈ A}ᶜ).Finite :=
  Set.Finite.preimage (fun _ _ _ _ he => by
    have hm := congrArg (fun v : Site 2 => v + z) he
    simpa only [sub_add_cancel] using hm) h

/-- Literal source-root identities survive whole-site translation. -/
theorem roots_translate_source (R : RootPair) (K : Finset (Site 2)) (γ : Set (Site 2))
    (z : Site 2) (hzero : R.zero = (K : Set (Site 2))) (hone : R.one = γ) :
    (roots R z).zero = (finiteSet K z : Set (Site 2)) ∧
      (roots R z).one = {x | x - z ∈ γ} := by
  constructor
  · ext x
    change (x - z ∈ R.zero) ↔ x ∈ finiteSet K z
    rw [hzero, mem_finiteSet]
    rfl
  · ext x
    change (x - z ∈ R.one) ↔ x - z ∈ γ
    rw [hone]

end
end FiniteAvalanches.Wilson.Lattice.CofiniteReciprocalGeometry
