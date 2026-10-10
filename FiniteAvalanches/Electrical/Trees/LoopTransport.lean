import FiniteAvalanches.Electrical.Reference.CopyTransport
import FiniteAvalanches.Trees.RootedForests

/-! Selectable trees and rooted forests are unchanged by deleting only loop copies. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

local instance nonloopCopyDec (J : CopiedGraph V E) :
    DecidableEq {e : E // J.left e ≠ J.right e} := Classical.decEq _

/-- The actual nonloop copies, with their original IDs and endpoints. -/
def nonloopGraph (J : CopiedGraph V E) : Multigraph V {e : E // J.left e ≠ J.right e} :=
  ⟨fun e => J.left e.val, fun e => J.right e.val, fun e => e.property⟩

/-- Selection of the nonloop copies in an arbitrary original subset. -/
def nonloopSelection (J : CopiedGraph V E) (S : Finset E) :
    Finset {e : E // J.left e ≠ J.right e} := Finset.univ.filter (fun e => e.val ∈ S)

omit [Fintype V] in
theorem mem_nonloopSelection (J : CopiedGraph V E) (S : Finset E)
    (e : {e : E // J.left e ≠ J.right e}) : e ∈ J.nonloopSelection S ↔ e.val ∈ S := by
  simp only [nonloopSelection, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype V] in
theorem nonloopSelection_image (J : CopiedGraph V E) (S : Finset E)
    (hS : ∀ e ∈ S, J.left e ≠ J.right e) :
    (J.nonloopSelection S).image Subtype.val = S := by
  ext e
  constructor
  · rintro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact (mem_nonloopSelection J S f).mp hf
  · intro he
    exact Finset.mem_image.mpr ⟨⟨e, hS e he⟩,
      (mem_nonloopSelection J S _).mpr he, rfl⟩

omit [Fintype V] in
theorem nonloopSelection_image_selection (J : CopiedGraph V E)
    (S : Finset {e : E // J.left e ≠ J.right e}) :
    J.nonloopSelection (S.image Subtype.val) = S := by
  ext e
  rw [mem_nonloopSelection]
  constructor
  · intro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    exact (Subtype.coe_injective hfe) ▸ hf
  · exact Finset.mem_image_of_mem Subtype.val

/-- The two existing tree predicates agree on a loopless copied graph. -/
theorem multigraph_tree_iff (G : Multigraph V E) (S : Finset E) :
    G.is_tree Set.univ S ↔
      ((Set.univ : Set V).Nonempty ∧
        (∀ x y, (⟨G.left, G.right⟩ : CopiedGraph V E).reaches S x y) ∧
        ∀ e ∈ S, ¬(⟨G.left, G.right⟩ : CopiedGraph V E).reaches (S.erase e)
          (G.left e) (G.right e)) := by
  constructor
  · rintro ⟨hne, _, hc, hf⟩
    exact ⟨hne, fun x y => hc x (Set.mem_univ x) y (Set.mem_univ y), hf⟩
  · rintro ⟨hne, hc, hf⟩
    exact ⟨hne, fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩,
      fun x _ y _ => hc x y, hf⟩

/-- Inclusion into the full carrier preserves the exact selectable-tree predicate. -/
theorem nonloop_tree_image_iff (J : CopiedGraph V E)
    (S : Finset {e : E // J.left e ≠ J.right e}) :
    ((Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches (S.image Subtype.val) x y) ∧
      ∀ e ∈ S.image Subtype.val,
        ¬J.reaches ((S.image Subtype.val).erase e) (J.left e) (J.right e)) ↔
      J.nonloopGraph.is_tree Set.univ S := by
  exact (tree_image_iff J
    (⟨J.nonloopGraph.left, J.nonloopGraph.right⟩ : CopiedGraph V _)
    Subtype.val Subtype.coe_injective (fun _ => rfl) (fun _ => rfl) S).trans
      (multigraph_tree_iff J.nonloopGraph S).symm

/-- Deleting loops gives a bijection of trees; lifting recovers the exact original subset. -/
def nonloopTreeEquiv (J : CopiedGraph V E) :
    J.SpanningTree ≃ J.nonloopGraph.ComponentTree Set.univ where
  toFun T := ⟨J.nonloopSelection T.val, by
    apply (nonloop_tree_image_iff J _).mp
    rw [nonloopSelection_image J T.val (fun e he h => loop_not_mem J T e h he)]
    exact T.property⟩
  invFun T := ⟨T.val.image Subtype.val, (nonloop_tree_image_iff J T.val).mpr T.property⟩
  left_inv T := Subtype.ext
    (nonloopSelection_image J T.val (fun e he h => loop_not_mem J T e h he))
  right_inv T := Subtype.ext (nonloopSelection_image_selection J T.val)

theorem nonloopTreeEquiv_lift (J : CopiedGraph V E) (T : J.SpanningTree) :
    (J.nonloopTreeEquiv T).val.image Subtype.val = T.val :=
  nonloopSelection_image J T.val (fun e he h => loop_not_mem J T e h he)

/-- A copied rooted forest spans the whole carrier with exactly one root per component. -/
abbrev RootedForest (J : CopiedGraph V E) (R : Set V) := {F : Finset E //
  (∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)) ∧
    ∀ x, ∃ r ∈ R, J.reaches F x r ∧ ∀ r' ∈ R, J.reaches F x r' → r' = r}

omit [Fintype V] [Fintype E] in
theorem rootedForest_loop_not_mem (J : CopiedGraph V E) (R : Set V)
    (F : J.RootedForest R) (e : E) (hloop : J.left e = J.right e) : e ∉ F.val := by
  intro he
  apply F.property.1 e he
  rw [hloop]
  exact .refl

/-- Root coverage and uniqueness, as well as acyclicity, are preserved by inclusion of IDs. -/
theorem nonloop_rooted_forest_image_iff (J : CopiedGraph V E) (R : Set V)
    (S : Finset {e : E // J.left e ≠ J.right e}) :
    ((∀ e ∈ S.image Subtype.val,
        ¬J.reaches ((S.image Subtype.val).erase e) (J.left e) (J.right e)) ∧
      ∀ x, ∃ r ∈ R, J.reaches (S.image Subtype.val) x r ∧
        ∀ r' ∈ R, J.reaches (S.image Subtype.val) x r' → r' = r) ↔
      J.nonloopGraph.is_rooted_forest R S := by
  let K : CopiedGraph V {e : E // J.left e ≠ J.right e} :=
    ⟨J.nonloopGraph.left, J.nonloopGraph.right⟩
  have reach := reaches_image_iff J K Subtype.val (fun _ => rfl) (fun _ => rfl)
  constructor
  · rintro ⟨hf, hc⟩
    refine ⟨?_, ?_⟩
    · intro e he h
      apply hf e.val (Finset.mem_image_of_mem Subtype.val he)
      rw [← Finset.image_erase Subtype.coe_injective]
      exact (reach (S.erase e) _ _).mpr h
    · intro x
      obtain ⟨r, hr, hx, hu⟩ := hc x
      exact ⟨r, hr, (reach S x r).mp hx,
        fun r' hr' hx' => hu r' hr' ((reach S x r').mpr hx')⟩
  · rintro ⟨hf, hc⟩
    refine ⟨?_, ?_⟩
    · intro e he h
      obtain ⟨f, hfS, rfl⟩ := Finset.mem_image.mp he
      apply hf f hfS
      rw [← Finset.image_erase Subtype.coe_injective] at h
      exact (reach (S.erase f) _ _).mp h
    · intro x
      obtain ⟨r, hr, hx, hu⟩ := hc x
      exact ⟨r, hr, (reach S x r).mpr hx,
        fun r' hr' hx' => hu r' hr' ((reach S x r').mp hx')⟩

/-- All original rooted forests biject with the nonloop all-minors carrier. -/
def nonloopRootedForestEquiv (J : CopiedGraph V E) (R : Set V) :
    J.RootedForest R ≃ J.nonloopGraph.RootedForest R where
  toFun F := ⟨J.nonloopSelection F.val, by
    apply (nonloop_rooted_forest_image_iff J R _).mp
    rw [nonloopSelection_image J F.val
      (fun e he h => rootedForest_loop_not_mem J R F e h he)]
    exact F.property⟩
  invFun F := ⟨F.val.image Subtype.val,
    (nonloop_rooted_forest_image_iff J R F.val).mpr F.property⟩
  left_inv F := Subtype.ext (nonloopSelection_image J F.val
    (fun e he h => rootedForest_loop_not_mem J R F e h he))
  right_inv F := Subtype.ext (nonloopSelection_image_selection J F.val)

theorem nonloopRootedForestEquiv_lift (J : CopiedGraph V E) (R : Set V)
    (F : J.RootedForest R) :
    (J.nonloopRootedForestEquiv R F).val.image Subtype.val = F.val :=
  nonloopSelection_image J F.val (fun e he h => rootedForest_loop_not_mem J R F e h he)

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
