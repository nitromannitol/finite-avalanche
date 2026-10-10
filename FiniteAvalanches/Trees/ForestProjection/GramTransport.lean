import FiniteAvalanches.Trees.ForestProjection.GramCount

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.Trees.Multigraph
variable {V W E : Type} [Fintype V] [Fintype W] [Fintype E] (G : Multigraph V E)

/-- Relabel only vertices; every original edge-copy identity remains fixed. -/
def relabelVertices (ρ : V ≃ W) : Multigraph W E where
  left e := ρ (G.left e)
  right e := ρ (G.right e)
  loopless e := fun h => G.loopless e (ρ.injective h)

theorem relabelVertices_reaches_iff (ρ : V ≃ W) (F : Finset E) (x y : V) :
    (G.relabelVertices ρ).reaches F (ρ x) (ρ y) ↔ G.reaches F x y := by
  constructor
  · intro h
    have h' : G.reaches F (ρ.symm (ρ x)) (ρ.symm (ρ y)) := Relation.ReflTransGen.lift' ρ.symm (fun u v hadj => by
      obtain ⟨e, he, hxy | hxy⟩ := hadj
      · exact .single ⟨e, he, Or.inl ⟨by simpa only [relabelVertices, Equiv.symm_apply_apply] using congrArg ρ.symm hxy.1,
          by simpa only [relabelVertices, Equiv.symm_apply_apply] using congrArg ρ.symm hxy.2⟩⟩
      · exact .single ⟨e, he, Or.inr ⟨by simpa only [relabelVertices, Equiv.symm_apply_apply] using congrArg ρ.symm hxy.1,
          by simpa only [relabelVertices, Equiv.symm_apply_apply] using congrArg ρ.symm hxy.2⟩⟩) _ _ h
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h
    exact Relation.ReflTransGen.lift' ρ (fun _ _ hadj => by
      obtain ⟨e, he, hxy | hxy⟩ := hadj
      · exact .single ⟨e, he, Or.inl ⟨congrArg ρ hxy.1, congrArg ρ hxy.2⟩⟩
      · exact .single ⟨e, he, Or.inr ⟨congrArg ρ hxy.1, congrArg ρ hxy.2⟩⟩) _ _ h

theorem relabelVertices_forest_iff (ρ : V ≃ W) (F : Finset E) :
    (G.relabelVertices ρ).is_forest F ↔ G.is_forest F := by
  constructor
  · intro h e he hpath
    exact h e he ((G.relabelVertices_reaches_iff ρ (F.erase e) _ _).mpr hpath)
  · intro h e he hpath
    exact h e he ((G.relabelVertices_reaches_iff ρ (F.erase e) _ _).mp hpath)

theorem relabelVertices_rootedForest_iff (ρ : V ≃ W) (R : Finset V) (F : Finset E) :
    (G.relabelVertices ρ).is_rooted_forest (R.map ρ.toEmbedding : Set W) F ↔
      G.is_rooted_forest (R : Set V) F := by
  constructor
  · rintro ⟨hf, hroots⟩
    refine ⟨(G.relabelVertices_forest_iff ρ F).mp hf, ?_⟩
    intro x
    obtain ⟨r, hr, hxr, hu⟩ := hroots (ρ x)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hr
    refine ⟨a, ha, (G.relabelVertices_reaches_iff ρ F x a).mp hxr, ?_⟩
    intro b hb hxb
    exact ρ.injective (hu (ρ b) (Finset.mem_map.mpr ⟨b, hb, rfl⟩)
      ((G.relabelVertices_reaches_iff ρ F x b).mpr hxb))
  · rintro ⟨hf, hroots⟩
    refine ⟨(G.relabelVertices_forest_iff ρ F).mpr hf, ?_⟩
    intro w
    obtain ⟨a, ha, hwa, hu⟩ := hroots (ρ.symm w)
    refine ⟨ρ a, Finset.mem_map.mpr ⟨a, ha, rfl⟩, ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using
        (G.relabelVertices_reaches_iff ρ F (ρ.symm w) a).mpr hwa
    · intro b hb hwb
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
      apply congrArg ρ
      apply hu v hv
      apply (G.relabelVertices_reaches_iff ρ F (ρ.symm w) v).mp
      simpa only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using hwb

def nonrootRelabel (ρ : V ≃ W) (R : Finset V) :
    {v : V // v ∉ R} ≃ {w : W // w ∉ R.map ρ.toEmbedding} where
  toFun v := ⟨ρ v.val, by simpa using v.property⟩
  invFun w := ⟨ρ.symm w.val, by
    intro hr
    exact w.property (Finset.mem_map.mpr ⟨ρ.symm w.val, hr, ρ.apply_symm_apply _⟩)⟩
  left_inv v := Subtype.ext (ρ.symm_apply_apply _)
  right_inv w := Subtype.ext (ρ.apply_symm_apply _)

theorem relabelVertices_gram (ρ : V ≃ W) (R : Finset V) :
    (G.relabelVertices ρ).rootGram (R.map ρ.toEmbedding) =
      (G.rootGram R).submatrix (nonrootRelabel ρ R).symm (nonrootRelabel ρ R).symm := by
  ext x y
  have hv (w : {w : W // w ∉ R.map ρ.toEmbedding}) :
      ((nonrootRelabel ρ R).symm w).val = ρ.symm w.val := rfl
  simp only [rootGram, Matrix.mul_apply, Matrix.transpose_apply, rootIncidence_apply,
    relabelVertices, Matrix.submatrix_apply, hv, Equiv.apply_eq_iff_eq_symm_apply]

/-- The standard principal all-minors normalizer is consumed on arbitrary finite vertex carriers. -/
theorem rootGram_det_eq_original_forest_count (R : Finset V) (hR : R.Nonempty) :
    (G.rootGram R).det = (Nat.card (G.RootedForest (R : Set V)) : ℝ) := by
  let ρ := Fintype.equivFin V
  have hR' : (R.map ρ.toEmbedding).Nonempty := hR.map
  have h := FiniteAvalanches.ForestGramCounting.gram_det_eq_original_forest_count
    (G.relabelVertices ρ) (R.map ρ.toEmbedding) hR'
  rw [G.relabelVertices_gram, Matrix.det_submatrix_equiv_self] at h
  have he : (G.relabelVertices ρ).RootedForest (R.map ρ.toEmbedding : Set (Fin (Fintype.card V))) ≃
      G.RootedForest (R : Set V) :=
    Equiv.subtypeEquivRight (G.relabelVertices_rootedForest_iff ρ R)
  rw [Nat.card_congr he] at h
  exact h

end FiniteAvalanches.Trees.Multigraph
