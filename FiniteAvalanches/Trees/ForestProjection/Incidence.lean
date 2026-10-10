import FiniteAvalanches.Trees.RootedForests
import FiniteAvalanches.Electrical.Plane.Incidence
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace FiniteAvalanches.Trees.Multigraph
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.Plane
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The copied gradient of a potential extended by zero on the prescribed roots. -/
def rootGradientMap (R : Finset V) : ({v : V // v ∉ R} → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun u := copyGradient G.left G.right (zeroExtend R u)
  map_add' u v := by
    funext e
    simp only [copyGradient, zeroExtend, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c u := by
    funext e
    simp only [copyGradient, zeroExtend, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The original copied incidence matrix, with only nonroot vertex columns. -/
def rootIncidence (R : Finset V) : Matrix E {v : V // v ∉ R} ℝ :=
  LinearMap.toMatrix' (G.rootGradientMap R)

theorem rootIncidence_mulVec (R : Finset V) (u : {v : V // v ∉ R} → ℝ) :
    G.rootIncidence R *ᵥ u = G.rootGradientMap R u :=
  LinearMap.toMatrix'_mulVec _ _

theorem rootIncidence_apply (R : Finset V) (e : E) (v : {v : V // v ∉ R}) :
    G.rootIncidence R e v =
      (if G.left e = v.val then 1 else 0) - (if G.right e = v.val then 1 else 0) := by
  have hsingle (x : V) : zeroExtend R (Pi.single v (1 : ℝ)) x =
      if x = v.val then 1 else 0 := by
    by_cases hx : x ∈ R
    · have hne : x ≠ v.val := fun h => v.property (h ▸ hx)
      simp [zeroExtend, hx, hne]
    · simp only [zeroExtend, dif_neg hx, Pi.single_apply]
      have he : (⟨x, hx⟩ : {v : V // v ∉ R}) = v ↔ x = v.val := Subtype.ext_iff
      simp only [he]
  change copyGradient G.left G.right (zeroExtend R (Pi.single v 1)) e = _
  simp only [copyGradient, hsingle]

/-- All gradients of vertex potentials vanishing on the entire root set. -/
def rootGradientSpace (R : Finset V) : Submodule ℝ (E → ℝ) :=
  LinearMap.range (G.rootGradientMap R)

theorem mem_rootGradientSpace_iff (R : Finset V) (j : E → ℝ) :
    j ∈ G.rootGradientSpace R ↔
      ∃ q : V → ℝ, (∀ r ∈ R, q r = 0) ∧ copyGradient G.left G.right q = j := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨zeroExtend R u, (by intro r hr; simp [zeroExtend, hr]), rfl⟩
  · rintro ⟨q, hq, hj⟩
    refine ⟨fun v => q v.val, ?_⟩
    have he : zeroExtend R (fun v : {v : V // v ∉ R} => q v.val) = q := by
      funext x
      by_cases hx : x ∈ R
      · simp [zeroExtend, hx, hq x hx]
      · simp [zeroExtend, hx]
    change copyGradient G.left G.right (zeroExtend R _) = j
    rw [he, hj]

/-- Adding roots shrinks the actual gradient subspace in the original edge coordinates. -/
theorem rootGradientSpace_antitone {R S : Finset V} (hRS : R ⊆ S) :
    G.rootGradientSpace S ≤ G.rootGradientSpace R := by
  intro j hj
  obtain ⟨q, hq, hgrad⟩ := (G.mem_rootGradientSpace_iff S j).mp hj
  exact (G.mem_rootGradientSpace_iff R j).mpr ⟨q, fun r hr => hq r (hRS hr), hgrad⟩

theorem rootGradientMap_injective (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) :
    Function.Injective (G.rootGradientMap R) := by
  obtain ⟨r, hr⟩ := hR
  intro u v huv
  apply dirichletMap_injective G.left G.right R (fun x => ⟨r, hr, hc x r⟩)
  funext x
  change laplacian G.left G.right (zeroExtend R u) x.val =
    laplacian G.left G.right (zeroExtend R v) x.val
  rw [← copyBoundary_gradient, ← copyBoundary_gradient]
  exact congrArg (fun j => copyBoundary G.left G.right j x.val) huv

/-- Positive Dirichlet Gram matrix, counting every original edge once. -/
def rootGram (R : Finset V) : Matrix {v : V // v ∉ R} {v : V // v ∉ R} ℝ :=
  (G.rootIncidence R).transpose * G.rootIncidence R

theorem rootIncidence_transpose_mulVec (R : Finset V) (j : E → ℝ) :
    (G.rootIncidence R).transpose *ᵥ j =
      fun v : {v : V // v ∉ R} => copyBoundary G.left G.right j v.val := by
  funext v
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    G.rootIncidence_apply, copyBoundary]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

/-- The Gram matrix is exactly the positive Dirichlet Laplacian already used electrically. -/
theorem rootGram_eq_dirichletMatrix (R : Finset V) :
    G.rootGram R = LinearMap.toMatrix' (dirichletMap G.left G.right R) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro u
  rw [Matrix.toLin'_toMatrix']
  change G.rootGram R *ᵥ u = dirichletMap G.left G.right R u
  rw [rootGram, ← Matrix.mulVec_mulVec, G.rootIncidence_mulVec,
    G.rootIncidence_transpose_mulVec]
  funext v
  exact copyBoundary_gradient G.left G.right (zeroExtend R u) v.val

/-- Contracted root-root edges have zero rows, while they retain their original copy index. -/
theorem rootIncidence_root_root_zero (R : Finset V) (e : E)
    (hl : G.left e ∈ R) (hr : G.right e ∈ R) : G.rootIncidence R e = 0 := by
  funext v
  have hleft : G.left e ≠ v.val := fun h => v.property (h ▸ hl)
  have hright : G.right e ≠ v.val := fun h => v.property (h ▸ hr)
  simp only [G.rootIncidence_apply, if_neg hleft, if_neg hright, sub_self, Pi.zero_apply]

/-- Parallel copies have equal incidence rows but remain distinct coordinates. -/
theorem rootIncidence_parallel_rows (R : Finset V) (e f : E)
    (hl : G.left e = G.left f) (hr : G.right e = G.right f) :
    G.rootIncidence R e = G.rootIncidence R f := by
  funext v
  simp only [G.rootIncidence_apply, hl, hr]

theorem rootGram_posDef (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) : (G.rootGram R).PosDef := by
  have hi : Function.Injective (G.rootIncidence R).mulVec := by
    intro u v h
    apply G.rootGradientMap_injective R hR hc
    simpa only [G.rootIncidence_mulVec] using h
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, rootGram] using
    Matrix.PosDef.conjTranspose_mul_self (G.rootIncidence R) hi

theorem rootGram_det_pos (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) : 0 < (G.rootGram R).det :=
  (G.rootGram_posDef R hR hc).det_pos

/-- The projection onto gradients with zero values at a nonempty set of roots. -/
def rootProjection (R : Finset V) (_hR : R.Nonempty)
    (_hc : (supportGraph G.left G.right).Preconnected) : Matrix E E ℝ :=
  G.rootIncidence R * (G.rootGram R)⁻¹ * (G.rootIncidence R).transpose

theorem rootProjection_fixes_gradient (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) (u : {v : V // v ∉ R} → ℝ) :
    G.rootProjection R hR hc *ᵥ G.rootGradientMap R u = G.rootGradientMap R u := by
  have hu : IsUnit (G.rootGram R).det := isUnit_iff_ne_zero.mpr (ne_of_gt (G.rootGram_det_pos R hR hc))
  rw [← G.rootIncidence_mulVec, rootProjection, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, show
      (G.rootIncidence R).transpose * G.rootIncidence R = G.rootGram R from rfl,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

/-- The inverse formula has precisely the source gradient space as its image. -/
theorem range_rootProjection (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) :
    LinearMap.range (G.rootProjection R hR hc).mulVecLin = G.rootGradientSpace R := by
  apply le_antisymm
  · rintro j ⟨x, rfl⟩
    refine ⟨(G.rootGram R)⁻¹ *ᵥ ((G.rootIncidence R).transpose *ᵥ x), ?_⟩
    change G.rootGradientMap R _ = G.rootProjection R hR hc *ᵥ x
    rw [← G.rootIncidence_mulVec, rootProjection, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · rintro j ⟨u, rfl⟩
    exact ⟨G.rootGradientMap R u, G.rootProjection_fixes_gradient R hR hc u⟩

theorem rootProjection_transpose (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) :
    (G.rootProjection R hR hc).transpose = G.rootProjection R hR hc := by
  have hg : (G.rootGram R).transpose = G.rootGram R := by
    simp only [rootGram, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [rootProjection, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hg, Matrix.mul_assoc]

theorem rootProjection_idempotent (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) :
    G.rootProjection R hR hc * G.rootProjection R hR hc = G.rootProjection R hR hc := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (G.rootProjection R hR hc * G.rootProjection R hR hc) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec]
  have hx : G.rootProjection R hR hc *ᵥ x ∈ G.rootGradientSpace R := by
    rw [← G.range_rootProjection R hR hc]
    exact ⟨x, rfl⟩
  obtain ⟨u, hu⟩ := hx
  rw [← hu, G.rootProjection_fixes_gradient]
  exact hu

/-- Orthogonality uses the Euclidean copied-edge pairing, summing each copy once. -/
theorem rootProjection_residual_orthogonal (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) (x j : E → ℝ)
    (hj : j ∈ G.rootGradientSpace R) :
    (x - G.rootProjection R hR hc *ᵥ x) ⬝ᵥ j = 0 := by
  obtain ⟨u, rfl⟩ := hj
  have hj := G.rootProjection_fixes_gradient R hR hc u
  have hs := G.rootProjection_transpose R hR hc
  rw [sub_dotProduct, dotProduct_comm (G.rootProjection R hR hc *ᵥ x)]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, hj,
    dotProduct_comm, sub_self]

/-- Both source root changes give nested projection images on the same copied edges. -/
theorem range_rootProjection_antitone {R S : Finset V} (hRS : R ⊆ S)
    (hR : R.Nonempty) (hS : S.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) :
    LinearMap.range (G.rootProjection S hS hc).mulVecLin ≤
      LinearMap.range (G.rootProjection R hR hc).mulVecLin := by
  rw [G.range_rootProjection, G.range_rootProjection]
  exact G.rootGradientSpace_antitone hRS

/-- A full-size principal projection minor has the normalized squared incidence minor. -/
theorem rootProjection_minor_det (R : Finset V) (hR : R.Nonempty)
    (hc : (supportGraph G.left G.right).Preconnected) (i : {v : V // v ∉ R} → E) :
    ((G.rootProjection R hR hc).submatrix i i).det =
      ((G.rootIncidence R).submatrix i id).det ^ 2 / (G.rootGram R).det := by
  have hsub : (G.rootProjection R hR hc).submatrix i i =
      (G.rootIncidence R).submatrix i id * (G.rootGram R)⁻¹ *
        ((G.rootIncidence R).submatrix i id).transpose := by
    ext x y
    simp only [rootProjection, Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.transpose_apply, id_eq]
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv]
  simp only [Ring.inverse_eq_inv]
  ring

/-- The two root changes used in color comparison give opposite gradient inclusions. -/
theorem mixedRootGradientSpace_inclusions (A A' C C' : Finset V)
    (hA : A ⊆ A') (hC : C' ⊆ C) :
    G.rootGradientSpace (A' ∪ C) ≤ G.rootGradientSpace (A ∪ C) ∧
      G.rootGradientSpace (A ∪ C) ≤ G.rootGradientSpace (A ∪ C') := by
  exact ⟨G.rootGradientSpace_antitone (Finset.union_subset_union hA (by rfl)),
    G.rootGradientSpace_antitone (Finset.union_subset_union (by rfl) hC)⟩

end FiniteAvalanches.Trees.Multigraph
