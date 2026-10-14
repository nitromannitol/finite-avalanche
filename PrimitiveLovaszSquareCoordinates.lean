import FiniteAvalanches.Electrical.Geometry.BSST
import Mathlib.Topology.MetricSpace.Isometry

/-! Coordinate transport for the author's Lovasz construction.
This file does not construct a tiling or assume nonoverlap/coverage. The voltage-vertical
face-coordinate rectangles below must still be identified with the actual sweep output.
The transport keeps every original copy and applies equally to point rectangles. -/

namespace FiniteAvalanches.Electrical.LovaszCoordinates
open StatementGeometry BSST Source
open scoped Classical
noncomputable section

/-- The same face-coordinate rectangle with voltage vertical, as in Lovasz's sweep. -/
def voltageVerticalSquare {V E W : Type} (J : CopiedGraph V E) (phi : V → ℝ)
    (psi : W → ℝ) (face0 face1 : E → W) (e : E) : Set (ℝ × ℝ) :=
  Set.Icc (min (psi (face0 e)) (psi (face1 e)))
    (max (psi (face0 e)) (psi (face1 e))) ×ˢ
  Set.Icc (min (phi (J.left e)) (phi (J.right e)))
    (max (phi (J.left e)) (phi (J.right e)))

/-- Swap voltage to the horizontal axis, with the actual global sign and gauge. -/
def squareToPaper (sigma gauge : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, sigma * (z.1 - gauge))

/-- The coordinate change is globally invertible, without any positive-current restriction. -/
def squareHomeomorph (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := squareToPaper sigma gauge
  invFun := fun z => (sigma * z.2 + gauge, z.1)
  left_inv z := by
    rcases hsigma with rfl | rfl <;> rcases z with ⟨x,y⟩ <;> simp [squareToPaper]
  right_inv z := by
    rcases hsigma with rfl | rfl <;> rcases z with ⟨x,y⟩ <;> simp [squareToPaper]
  continuous_toFun := continuous_snd.prodMk
    (continuous_const.mul (continuous_fst.sub continuous_const))
  continuous_invFun := ((continuous_const.mul continuous_snd).add continuous_const).prodMk
    continuous_fst

/-- The source plane's product metric is preserved. -/
theorem squareToPaper_isometry (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    Isometry (squareToPaper sigma gauge) := by
  apply Isometry.of_dist_eq
  intro z w
  have hs : |sigma| = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  have h : sigma * (z.1 - gauge) - sigma * (w.1 - gauge) = sigma * (z.1 - w.1) := by ring
  simp only [Prod.dist_eq, Real.dist_eq, squareToPaper, h, abs_mul, hs, one_mul]
  exact max_comm _ _

/-- Euclidean squared distance is also preserved; the assertion is not limited to the
supremum product metric used by the angular estimates. -/
theorem squareToPaper_euclidean_sq (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (z w : ℝ × ℝ) :
    ((squareToPaper sigma gauge z).1 - (squareToPaper sigma gauge w).1)^2 +
      ((squareToPaper sigma gauge z).2 - (squareToPaper sigma gauge w).2)^2 =
    (z.1 - w.1)^2 + (z.2 - w.2)^2 := by
  rcases hsigma with rfl | rfl <;> dsimp only [squareToPaper] <;> ring

/-- Exact membership dictionary at each original ID, including equal interval endpoints. -/
theorem squareToPaper_mem_copiedSquare {V E W : Type} (J : CopiedGraph V E)
    (phi : V → ℝ) (psi : W → ℝ) (face0 face1 : E → W)
    (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) (e : E) (z : ℝ × ℝ) :
    squareToPaper sigma gauge z ∈ copiedSquare J phi (fun F => sigma * (psi F - gauge))
      face0 face1 e ↔ z ∈ voltageVerticalSquare J phi psi face0 face1 e := by
  rcases hsigma with rfl | rfl
  · simp only [copiedSquare, voltageVerticalSquare, squareToPaper, one_mul, sub_eq_add_neg,
      Set.mem_prod, Set.mem_Icc, min_add_add_right, max_add_add_right, add_le_add_iff_right]
    tauto
  · simp only [copiedSquare, voltageVerticalSquare, squareToPaper, neg_one_mul, sub_eq_add_neg,
      Set.mem_prod, Set.mem_Icc, min_neg_neg, max_neg_neg, min_add_add_right,
      max_add_add_right, neg_le_neg_iff, add_le_add_iff_right]
    tauto

/-- One global coordinate map takes the complete closed original-copy rectangle exactly
onto the source square. No auxiliary edge or positive-current filtering changes the IDs. -/
theorem copiedSquare_eq_image {V E W : Type} (J : CopiedGraph V E)
    (phi : V → ℝ) (psi : W → ℝ) (face0 face1 : E → W)
    (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) (e : E) :
    copiedSquare J phi (fun F => sigma * (psi F - gauge)) face0 face1 e =
      squareToPaper sigma gauge '' voltageVerticalSquare J phi psi face0 face1 e := by
  let T := squareHomeomorph sigma gauge hsigma
  ext z
  constructor
  · intro hz
    refine ⟨T.symm z, ?_, T.apply_symm_apply z⟩
    apply (squareToPaper_mem_copiedSquare J phi psi face0 face1 sigma gauge hsigma e (T.symm z)).mp
    change T (T.symm z) ∈ _
    rwa [T.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    exact (squareToPaper_mem_copiedSquare J phi psi face0 face1 sigma gauge hsigma e w).mpr hw

/-- Disjoint interiors are equivalent under the proved coordinate dictionary. This is an
iff between explicit sets, not an assumed tiling or packing property. -/
theorem copiedSquare_interiors_disjoint_iff {V E W : Type} (J : CopiedGraph V E)
    (phi : V → ℝ) (psi : W → ℝ) (face0 face1 : E → W)
    (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) (e f : E) :
    Disjoint (interior (copiedSquare J phi (fun F => sigma * (psi F - gauge)) face0 face1 e))
      (interior (copiedSquare J phi (fun F => sigma * (psi F - gauge)) face0 face1 f)) ↔
    Disjoint (interior (voltageVerticalSquare J phi psi face0 face1 e))
      (interior (voltageVerticalSquare J phi psi face0 face1 f)) := by
  let T := squareHomeomorph sigma gauge hsigma
  rw [copiedSquare_eq_image J phi psi face0 face1 sigma gauge hsigma e,
    copiedSquare_eq_image J phi psi face0 face1 sigma gauge hsigma f]
  change Disjoint (interior (T '' _)) (interior (T '' _)) ↔ _
  rw [← T.image_interior, ← T.image_interior]
  exact Set.disjoint_image_iff T.injective

/-- Physical source squares use the same actual augmented complement faces and original IDs. -/
theorem source_edgeSquare_eq_image {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (B : PlaneEmbedding J) (alpha beta : V)
    (A : OuterArc B alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) (e : E) :
    edgeSquare B alpha beta A phi (fun F => sigma * (psi F - gauge)) e =
      squareToPaper sigma gauge '' voltageVerticalSquare J phi psi
        (fun e => A.embedding.leftFace (.inl e)) (fun e => A.embedding.rightFace (.inl e)) e := by
  simpa only [Source.edgeSquare, BSST.copiedSquare] using
    copiedSquare_eq_image J phi psi (fun e => A.embedding.leftFace (.inl e))
      (fun e => A.embedding.rightFace (.inl e)) sigma gauge hsigma e

/-- Zero-current copied edges keep their actual common face/voltage point. -/
theorem source_zero_current_point {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (B : PlaneEmbedding J) (alpha beta : V)
    (A : OuterArc B alpha beta) (phi : V → ℝ) (psi : A.embedding.Face → ℝ)
    (hstream : Source.stream_spec B alpha beta A phi psi) (sigma gauge : ℝ)
    (e : E) (hzero : phi (J.left e) = phi (J.right e)) :
    edgeSquare B alpha beta A phi (fun F => sigma * (psi F - gauge)) e =
      {(phi (J.left e), sigma * (psi (A.embedding.leftFace (.inl e)) - gauge))} := by
  have hpsi : psi (A.embedding.leftFace (.inl e)) = psi (A.embedding.rightFace (.inl e)) := by
    apply sub_eq_zero.mp
    rw [hstream.1 e, hzero, sub_self]
  simp only [Source.edgeSquare, hzero, hpsi, min_self, max_self, Set.Icc_self,
    Set.singleton_prod_singleton]

end
end FiniteAvalanches.Electrical.LovaszCoordinates
