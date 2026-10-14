import FiniteAvalanches.Trees.RootedForests

/-! Relabeling roots retains every selected original edge copy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Trees.Multigraph
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

theorem oneVertices_subset_of_one_roots_subset (F : Finset E) (C C' : Set V)
    (hC : C' ⊆ C) : G.oneVertices F C' ⊆ G.oneVertices F C := by
  rintro x ⟨r, hr, hxr⟩
  exact ⟨r, hC hr, hxr⟩

/-- The identity on original edge copies is an equivalence when only root labels change. -/
def rootRecoloringEquiv (A C A' C' : Set V) (h : A ∪ C = A' ∪ C') :
    G.RootedForest (A ∪ C) ≃ G.RootedForest (A' ∪ C') where
  toFun F := ⟨F.val, h ▸ F.property⟩
  invFun F := ⟨F.val, h.symm ▸ F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rootRecoloringEquiv_preserves_copies (A C A' C' : Set V)
    (h : A ∪ C = A' ∪ C') (F : G.RootedForest (A ∪ C)) :
    (G.rootRecoloringEquiv A C A' C' h F).val = F.val := rfl

/-- On the very same uniformly counted forests, relabeling one roots as zero
decreases every increasing event. No connectivity or positive denominator is needed. -/
theorem finite_root_recoloring_mono (A C A' C' : Set V)
    (htotal : A ∪ C = A' ∪ C') (hC : C' ⊆ C)
    (H : Set (Set V))
    (hH : ∀ U ∈ H, ∀ W : Set V, U ⊆ W → W ∈ H) :
    (Nat.card {F : G.RootedForest (A' ∪ C') | G.oneVertices F.val C' ∈ H} : ℝ) /
        Nat.card (G.RootedForest (A' ∪ C')) ≤
      (Nat.card {F : G.RootedForest (A ∪ C) | G.oneVertices F.val C ∈ H} : ℝ) /
        Nat.card (G.RootedForest (A ∪ C)) := by
  rw [htotal]
  let inclusion : {F : G.RootedForest (A' ∪ C') | G.oneVertices F.val C' ∈ H} →
      {F : G.RootedForest (A' ∪ C') | G.oneVertices F.val C ∈ H} :=
    fun F => ⟨F.val, hH _ F.property _
      (G.oneVertices_subset_of_one_roots_subset F.val.val C C' hC)⟩
  have hinj : Function.Injective inclusion := by
    intro F F' he
    have hv : (inclusion F).val = (inclusion F').val := congrArg
      (fun z : {f : G.RootedForest (A' ∪ C') | G.oneVertices f.val C ∈ H} => z.val) he
    exact Subtype.ext hv
  have hcard := Nat.card_le_card_of_injective inclusion hinj
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hcard) (Nat.cast_nonneg _)

end
end FiniteAvalanches.Trees.Multigraph
