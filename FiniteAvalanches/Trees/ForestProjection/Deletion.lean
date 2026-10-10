import FiniteAvalanches.Trees.ForestProjection.Incidence
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.Trees.Multigraph
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
local instance edgeSubsetDecidableEq (S : Finset E) : DecidableEq S := Classical.decEq _

/-- Deleting edges retains each surviving original copy and every original vertex. -/
def edgeSubgraph (S : Finset E) : Multigraph V S where
  left e := G.left e.val
  right e := G.right e.val
  loopless e := G.loopless e.val

/-- Inclusion of actual selected copied subsets into their original edge carrier. -/
def liftEdgeSubset (S : Finset E) (t : Finset S) : Finset E := t.image Subtype.val

theorem edgeSubgraph_reaches_iff (S : Finset E) (t : Finset S) (x y : V) :
    (G.edgeSubgraph S).reaches t x y ↔ G.reaches (liftEdgeSubset S t) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      obtain ⟨e, he, hxy⟩ := hadj
      exact ih.tail ⟨e.val, Finset.mem_image_of_mem Subtype.val he, hxy⟩
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      obtain ⟨e, he, hxy⟩ := hadj
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact ih.tail ⟨f, hf, hxy⟩

omit [Fintype E] in
theorem liftEdgeSubset_erase (S : Finset E) (t : Finset S) (e : S) :
    liftEdgeSubset S (t.erase e) = (liftEdgeSubset S t).erase e.val :=
  Finset.image_erase Subtype.val_injective t e

theorem edgeSubgraph_forest_iff (S : Finset E) (t : Finset S) :
    (G.edgeSubgraph S).is_forest t ↔ G.is_forest (liftEdgeSubset S t) := by
  constructor
  · intro ht e he hr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    apply ht f hf
    apply (G.edgeSubgraph_reaches_iff S (t.erase f) _ _).mpr
    rw [liftEdgeSubset_erase]
    exact hr
  · intro ht e he hr
    apply ht e.val (Finset.mem_image_of_mem Subtype.val he)
    rw [← liftEdgeSubset_erase]
    exact (G.edgeSubgraph_reaches_iff S (t.erase e) _ _).mp hr

theorem edgeSubgraph_rootedForest_iff (S : Finset E) (R : Set V) (t : Finset S) :
    (G.edgeSubgraph S).is_rooted_forest R t ↔ G.is_rooted_forest R (liftEdgeSubset S t) := by
  simp only [is_rooted_forest, G.edgeSubgraph_forest_iff, G.edgeSubgraph_reaches_iff]

def restrictEdgeSubset (S F : Finset E) (hF : F ⊆ S) : Finset S :=
  F.attach.image (fun e => ⟨e.val, hF e.property⟩)

omit [Fintype E] in
theorem lift_restrictEdgeSubset (S F : Finset E) (hF : F ⊆ S) :
    liftEdgeSubset S (restrictEdgeSubset S F hF) = F := by
  unfold liftEdgeSubset restrictEdgeSubset
  rw [Finset.image_image]
  exact Finset.attach_image_val

omit [Fintype E] in
theorem liftEdgeSubset_subset (S : Finset E) (t : Finset S) : liftEdgeSubset S t ⊆ S := by
  intro e he
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
  exact f.property

/-- Edge deletion transports the actual original forest carrier, not a renormalized law. -/
def edgeSubgraphRootedForestEquiv (S : Finset E) (R : Set V) :
    (G.edgeSubgraph S).RootedForest R ≃ {F : G.RootedForest R // F.val ⊆ S} where
  toFun t := ⟨⟨liftEdgeSubset S t.val,
    (G.edgeSubgraph_rootedForest_iff S R t.val).mp t.property⟩, liftEdgeSubset_subset S t.val⟩
  invFun F := ⟨restrictEdgeSubset S F.val.val F.property, by
    apply (G.edgeSubgraph_rootedForest_iff S R _).mpr
    rw [lift_restrictEdgeSubset]
    exact F.val.property⟩
  left_inv t := by
    apply Subtype.ext
    apply Finset.image_injective Subtype.val_injective
    exact lift_restrictEdgeSubset S (liftEdgeSubset S t.val) (liftEdgeSubset_subset S t.val)
  right_inv F := by
    apply Subtype.ext
    exact Subtype.ext (lift_restrictEdgeSubset S F.val.val F.property)

theorem edgeSubgraph_forest_count (S : Finset E) (R : Set V) :
    Nat.card ((G.edgeSubgraph S).RootedForest R) =
      Nat.card {F : G.RootedForest R // F.val ⊆ S} :=
  Nat.card_congr (G.edgeSubgraphRootedForestEquiv S R)

attribute [-instance] edgeSubsetDecidableEq

/-- The smaller Gram matrix is obtained by deleting precisely the original edge rows. -/
theorem edgeSubgraph_gram_deletion (R : Finset V) (A : Finset E) :
    (G.edgeSubgraph Aᶜ).rootGram R = G.rootGram R -
      ((G.rootIncidence R).submatrix (Subtype.val : A → E) id).transpose *
        (G.rootIncidence R).submatrix (Subtype.val : A → E) id := by
  ext x y
  simp only [rootGram, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    rootIncidence_apply, edgeSubgraph, Matrix.submatrix_apply, id_eq]
  let f := fun e : E =>
    ((if G.left e = x.val then (1 : ℝ) else 0) - (if G.right e = x.val then 1 else 0)) *
      ((if G.left e = y.val then (1 : ℝ) else 0) - (if G.right e = y.val then 1 else 0))
  change (∑ e : (Aᶜ : Finset E), f e.val) = (∑ e : E, f e) - ∑ e : A, f e.val
  rw [Finset.sum_coe_sort, Finset.sum_coe_sort]
  exact eq_sub_of_add_eq (Finset.sum_compl_add_sum A f)

/-- Complementary projection minors are the actual edge-deletion determinant ratios. -/
theorem rootProjection_avoidance_minor_det (R : Finset V) (hR : R.Nonempty)
    (hc : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected)
    (A : Finset E) :
    (((1 : Matrix E E ℝ) - G.rootProjection R hR hc).submatrix
      (Subtype.val : A → E) Subtype.val).det =
      ((G.edgeSubgraph Aᶜ).rootGram R).det / (G.rootGram R).det := by
  let B := (G.rootIncidence R).submatrix (Subtype.val : A → E) id
  have hu : IsUnit (G.rootGram R).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.rootGram_det_pos R hR hc))
  have hminor : (((1 : Matrix E E ℝ) - G.rootProjection R hR hc).submatrix
      (Subtype.val : A → E) Subtype.val) =
      (1 : Matrix A A ℝ) + B * (G.rootGram R)⁻¹ * (-B.transpose) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, rootProjection, Matrix.add_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.neg_apply, B, id_eq,
      Matrix.one_apply, Subtype.ext_iff]
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  have hdet := Matrix.det_add_mul (-B.transpose) B hu
  have hdelete : (G.edgeSubgraph Aᶜ).rootGram R = G.rootGram R + (-B.transpose) * B := by
    rw [G.edgeSubgraph_gram_deletion]
    simp only [B, Matrix.neg_mul, sub_eq_add_neg]
  rw [← hminor, ← hdelete] at hdet
  have hne := ne_of_gt (G.rootGram_det_pos R hR hc)
  exact (eq_div_iff hne).mpr (by simpa only [mul_comm] using hdet.symm)

end FiniteAvalanches.Trees.Multigraph
