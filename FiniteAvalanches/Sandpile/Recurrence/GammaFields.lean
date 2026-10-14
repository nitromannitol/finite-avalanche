import FiniteAvalanches.Sandpile.Recurrence.GammaForbidden
import FiniteAvalanches.Sandpile.Recurrence.RawIntegerDynamics

/-! Exact raw integer fields and one-step transport. No lower height bound is
part of this equivalence or any grain/toppling transport theorem. -/
namespace FiniteAvalanches.Sandpile.GammaGraph
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

def fieldEquiv (Γ : Finset Site2) : RawInteger.Field Γ ≃
    (Burning.SourceVertex (none : Vertex Γ) → ℤ) where
  toFun η := fun v => η ((vertexEquiv Γ).symm v)
  invFun θ := fun x => θ (vertexEquiv Γ x)
  left_inv η := by funext x; simp only [Equiv.symm_apply_apply]
  right_inv θ := by funext v; simp only [Equiv.apply_symm_apply]

theorem field_equiv_value {Γ : Finset Site2} (η : RawInteger.Field Γ) (x : Γ) :
    fieldEquiv Γ η (vertexEquiv Γ x) = η x := by
  change η ((vertexEquiv Γ).symm (vertexEquiv Γ x)) = _
  rw [Equiv.symm_apply_apply]

theorem stable_iff {Γ : Finset Site2} (η : RawInteger.Field Γ) : RawInteger.Stable η ↔
    ∀ v, fieldEquiv Γ η v < (Burning.degree (graph Γ) v.val : ℤ) := by
  constructor
  · intro h v
    obtain ⟨x, rfl⟩ := (vertexEquiv Γ).surjective v
    rw [field_equiv_value, degree_four]
    exact h x
  · intro h x
    have hx := h (vertexEquiv Γ x)
    rw [field_equiv_value, degree_four] at hx
    exact hx

theorem no_fsc_iff {Γ : Finset Site2} (η : RawInteger.Field Γ) : RawInteger.NoFSC η ↔
    ∀ T : Finset (Burning.SourceVertex (none : Vertex Γ)), ¬(T.Nonempty ∧ ∀ v ∈ T,
      fieldEquiv Γ η v < (Burning.activeDegree (graph Γ) (Finset.univ.erase none) T v : ℤ)) := by
  rw [RawInteger.no_fsc_subtype_iff]
  constructor
  · intro h T hf
    let S := T.image (vertexEquiv Γ).symm
    have hi : S.image (vertexEquiv Γ) = T := by
      simp only [S, Finset.image_image, Function.comp_def, Equiv.apply_symm_apply]
      exact Finset.image_id
    apply h S
    refine ⟨hf.1.image _, ?_⟩
    intro x hx
    have hv : vertexEquiv Γ x ∈ T := hi ▸ Finset.mem_image_of_mem _ hx
    have ht := hf.2 _ hv
    rw [field_equiv_value, ← hi, subset_degree S x hx] at ht
    exact ht
  · intro h S hf
    apply h (S.image (vertexEquiv Γ))
    refine ⟨hf.1.image _, ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    rw [field_equiv_value, subset_degree S x hx]
    exact hf.2 x hx

theorem copies_to_site {Γ : Finset Site2} (x o : Γ) :
    Burning.degreeInto (graph Γ) {(vertexEquiv Γ o).val} (vertexEquiv Γ x).val =
      if o.val ∈ LatticeProb.nbrFinset x.val then 1 else 0 := by
  have hd := subset_degree_all ({o} : Finset Γ) x
  simp only [Burning.activeDegree, Finset.image_singleton] at hd
  rw [hd]
  unfold Waves.degree
  by_cases ho : o.val ∈ LatticeProb.nbrFinset x.val
  · rw [Finset.inter_singleton_of_mem ho, Finset.card_singleton, if_pos ho]
  · rw [Finset.inter_singleton_of_notMem ho, Finset.card_empty, if_neg ho]

theorem grain_transport {Γ : Finset Site2} (η : RawInteger.Field Γ) (o : Γ) :
    fieldEquiv Γ (RawInteger.addGrain η o) =
      Function.update (fieldEquiv Γ η) (vertexEquiv Γ o) (fieldEquiv Γ η (vertexEquiv Γ o) + 1) := by
  funext v
  obtain ⟨x, rfl⟩ := (vertexEquiv Γ).surjective v
  rw [field_equiv_value, field_equiv_value]
  by_cases hx : x = o
  · subst x; simp only [RawInteger.addGrain, Function.update_self]
  · have hv : vertexEquiv Γ x ≠ vertexEquiv Γ o := fun he => hx ((vertexEquiv Γ).injective he)
    simp only [RawInteger.addGrain, Function.update_of_ne hx, Function.update_of_ne hv,
      field_equiv_value]

theorem topple_transport {Γ : Finset Site2} (η : RawInteger.Field Γ) (o : Γ) :
    fieldEquiv Γ (RawInteger.topple η o) = fun v =>
      if v = vertexEquiv Γ o then fieldEquiv Γ η v - (Burning.degree (graph Γ) (vertexEquiv Γ o).val : ℤ)
      else fieldEquiv Γ η v + (Burning.degreeInto (graph Γ) {(vertexEquiv Γ o).val} v.val : ℤ) := by
  funext v
  obtain ⟨x, rfl⟩ := (vertexEquiv Γ).surjective v
  rw [field_equiv_value]
  by_cases hx : x = o
  · subst x
    rw [if_pos (Eq.refl (vertexEquiv Γ o)), field_equiv_value, degree_four]
    change η o + lap (dirac o.val) o.val = η o - 4
    rw [lap_dirac_self]
    omega
  · have hv : vertexEquiv Γ x ≠ vertexEquiv Γ o := fun he => hx ((vertexEquiv Γ).injective he)
    have hv' : x.val ≠ o.val := fun he => hx (Subtype.ext he)
    rw [if_neg hv, field_equiv_value, copies_to_site]
    simp only [RawInteger.topple, Waves.lap_dirac_off o.val x.val hv']
    split_ifs <;> norm_num

end
end FiniteAvalanches.Sandpile.GammaGraph
