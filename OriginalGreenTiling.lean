import OriginalGreenNormalization
import PrimitiveLovaszSquareCoordinates
import LovaszQuarterTurn

namespace FiniteAvalanches.Electrical.LovaszApplication
open LatticeProb StatementGeometry Source BSST Plane.SourceLattice LatticeDrawing SplitStep
open LovaszStream LovaszCoordinates
open scoped Classical BigOperators
noncomputable section

/-- One vertical reflection/translation acts on the full physical tiling. -/
def verticalMap (sigma gauge : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, sigma * (z.2 - gauge))

/-- This uses the already proved swap/sign/gauge homeomorph twice. -/
def verticalHomeomorph (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (squareHomeomorph 1 0 (Or.inl rfl)).trans (squareHomeomorph sigma gauge hsigma)

theorem verticalHomeomorph_apply (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (z : ℝ × ℝ) : verticalHomeomorph sigma gauge hsigma z = verticalMap sigma gauge z := by
  change (1 * (z.1 - 0), sigma * (z.2 - gauge)) = verticalMap sigma gauge z
  simp only [verticalMap, sub_zero, one_mul]

theorem verticalMap_isometry (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    Isometry (verticalMap sigma gauge) := by
  have h := (squareToPaper_isometry sigma gauge hsigma).comp
    (squareToPaper_isometry 1 0 (Or.inl rfl))
  have heq : squareToPaper sigma gauge ∘ squareToPaper 1 0 = verticalMap sigma gauge := by
    funext z
    change (1 * (z.1 - 0), sigma * (z.2 - gauge)) = verticalMap sigma gauge z
    simp only [verticalMap, sub_zero, one_mul]
  rw [heq] at h
  exact h

/-- Exact global set transport, retaining every original label and degenerate interval. -/
theorem signed_copiedSquare_image {V E W : Type} (J : CopiedGraph V E)
    (phi : V → ℝ) (eta : W → ℝ) (face0 face1 : E → W)
    (sigma gauge : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) (e : E) :
    copiedSquare J phi (fun F => sigma * (eta F - gauge)) face0 face1 e =
      verticalMap sigma gauge '' copiedSquare J phi eta face0 face1 e := by
  let T := verticalHomeomorph sigma gauge hsigma
  have hm (z : ℝ × ℝ) : T z ∈ copiedSquare J phi
      (fun F => sigma * (eta F - gauge)) face0 face1 e ↔
      z ∈ copiedSquare J phi eta face0 face1 e := by
    have h := squareToPaper_mem_copiedSquare J phi eta face0 face1 sigma gauge hsigma e
      (z.2, z.1)
    simpa only [T, verticalHomeomorph_apply, verticalMap, squareToPaper,
      voltageVerticalSquare, copiedSquare, Set.mem_prod, and_comm] using h
  ext z
  constructor
  · intro hz
    refine ⟨T.symm z, ?_, ?_⟩
    · exact (hm _).mp (by rwa [T.apply_symm_apply])
    · rw [← verticalHomeomorph_apply sigma gauge hsigma]
      exact T.apply_symm_apply z
  · rintro ⟨w, hw, rfl⟩
    rw [← verticalHomeomorph_apply sigma gauge hsigma]
    exact (hm w).mpr hw

/-- Both checked pole orders take the same closed strip to its negative-Green range. -/
theorem verticalMap_image_rectangle (sigma gauge M : ℝ)
    (hmode : (sigma = 1 ∧ gauge = M) ∨ (sigma = -1 ∧ gauge = 0)) :
    verticalMap sigma gauge '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 M) =
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-M) 0 := by
  rcases hmode with ⟨hs, hg⟩ | ⟨hs, hg⟩
  · rw [hs, hg]
    ext z
    constructor
    · rintro ⟨w, ⟨hx, hy⟩, rfl⟩
      exact ⟨hx, by dsimp [verticalMap]; constructor <;> linarith only [hy.1, hy.2]⟩
    · rintro ⟨hx, hy⟩
      refine ⟨(z.1, z.2 + M), ⟨hx, ?_⟩, ?_⟩
      · constructor <;> linarith only [hy.1, hy.2]
      · dsimp [verticalMap]
        congr 1
        ring
  · rw [hs, hg]
    ext z
    constructor
    · rintro ⟨w, ⟨hx, hy⟩, rfl⟩
      exact ⟨hx, by dsimp [verticalMap]; constructor <;> linarith only [hy.1, hy.2]⟩
    · rintro ⟨hx, hy⟩
      refine ⟨(z.1, -z.2), ⟨hx, ?_⟩, ?_⟩
      · constructor <;> linarith only [hy.1, hy.2]
      · simp only [verticalMap, sub_zero, neg_one_mul, neg_neg, Prod.mk.eta]

/-- Actual original side equations identify each unswitched copy with the same
physical stream witness; the chart dual stores its sides in reversed order. -/
theorem original_stream_square_eq_physical (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    (B : PlaneEmbedding (originalGraph D P marked)) (A : OuterArc B (alpha D P) (beta D P))
    (faces : Face Q ≃ A.embedding.Face)
    (hfaces : ∀ e : Copy D P marked,
      faces ((sourceDeletedDualGraph D P marked Q charts).left e) = A.embedding.rightFace (.inl e) ∧
      faces ((sourceDeletedDualGraph D P marked Q charts).right e) = A.embedding.leftFace (.inl e))
    (psi : A.embedding.Face → ℝ)
    (heq : originalStream D P hD marked Q charts = psi ∘ faces) (e : Copy D P marked) :
    copiedSquare (originalGraph D P marked) (Repair8.voltage D P hD marked)
      (originalStream D P hD marked Q charts)
      (sourceDeletedDualGraph D P marked Q charts).left
      (sourceDeletedDualGraph D P marked Q charts).right e =
    edgeSquare B (alpha D P) (beta D P) A (Repair8.voltage D P hD marked) psi e := by
  simp only [copiedSquare, edgeSquare, heq, Function.comp_apply,
    (hfaces e).1, (hfaces e).2]
  rw [min_comm (psi (A.embedding.rightFace (.inl e))),
    max_comm (psi (A.embedding.rightFace (.inl e)))]

/-- The literal actual Green family has all original-copy currents, disjoint
interiors and closed coverage. No stream, packing or face-equivalence premise is taken. -/
theorem constructed_original_green_tiling (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (marked : MarkedCopy D P)
    (Q : Drawing (LatticeDrawing.primalGraph D P)) (charts : ∀ e, EdgeChart Q e)
    [Fintype (Face Q)] (v0 vm : Face Q)
    (hc : (supportGraph (sourceDeletedDualGraph D P marked Q charts).left
      (sourceDeletedDualGraph D P marked Q charts).right).Preconnected)
    (hmarked :
      ((sourceDualGraph D P Q charts).left (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).right (markedPrimal D P marked) = vm) ∨
      ((sourceDualGraph D P Q charts).right (markedPrimal D P marked) = v0 ∧
        (sourceDualGraph D P Q charts).left (markedPrimal D P marked) = vm)) :
    let J := originalGraph D P marked
    let K := sourceDeletedDualGraph D P marked Q charts
    let phi := Repair8.voltage D P hD marked
    let G := groundedGreen K.left K.right vm hc v0
    let S := copiedSquare J phi (fun F => -G F) K.left K.right
    (∀ e : Copy D P marked, |(-G (K.left e)) - (-G (K.right e))| =
      |phi (J.left e) - phi (J.right e)|) ∧
    (∀ e f : Copy D P marked, e ≠ f → Disjoint (interior (S e)) (interior (S f))) ∧
    (⋃ e : Copy D P marked, S e) = Set.Icc 0 1 ×ˢ Set.Icc (-mass J phi) 0 ∧
    (∀ e : Copy D P marked, phi (J.left e) = phi (J.right e) →
      S e = {(phi (J.left e), -G (K.left e))}) ∧
    (∀ e : Copy D P marked, S e = GeometryReview.quarterTurn ''
      voltageVerticalSquare J phi G K.left K.right e) := by
  dsimp only
  let J := originalGraph D P marked
  let K := sourceDeletedDualGraph D P marked Q charts
  let phi := Repair8.voltage D P hD marked
  let eta := originalStream D P hD marked Q charts
  let G := groundedGreen K.left K.right vm hc v0
  let M := mass J phi
  obtain ⟨B, A, faces, hfaces, _hmarkedSides, psi, _hpsi, heq, _hbalance, _hbounds, hd, hcover⟩ :=
    original_stream_tiling_witness D P hD marked Q charts
  obtain ⟨sigma, hsigma, hfield, _hdiag, _hground, hmode⟩ :=
    constructed_original_green_normalization D P hD marked Q charts v0 vm hc hmarked
  have hg : (fun F => sigma * (eta F - eta vm)) = (fun F => -G F) := funext hfield
  have hbase (e : Copy D P marked) : copiedSquare J phi eta K.left K.right e =
      edgeSquare B (alpha D P) (beta D P) A phi psi e :=
    original_stream_square_eq_physical D P hD marked Q charts B A faces hfaces psi heq e
  let T := verticalHomeomorph sigma (eta vm) hsigma
  have hsquare (e : Copy D P marked) : copiedSquare J phi (fun F => -G F) K.left K.right e =
      T '' edgeSquare B (alpha D P) (beta D P) A phi psi e := by
    rw [← hg, signed_copiedSquare_image J phi eta K.left K.right sigma (eta vm) hsigma e, hbase]
    congr 1
    exact (funext (verticalHomeomorph_apply sigma (eta vm) hsigma)).symm
  have hlength (e : Copy D P marked) : |(-G (K.left e)) - (-G (K.right e))| =
      |phi (J.left e) - phi (J.right e)| := by
    have hs := (originalStream_spec D P hD marked Q charts).1 e
    change eta (K.right e) - eta (K.left e) = phi (J.left e) - phi (J.right e) at hs
    have h0 := hfield (K.left e)
    have h1 := hfield (K.right e)
    change sigma * (eta (K.left e) - eta vm) = -G (K.left e) at h0
    change sigma * (eta (K.right e) - eta vm) = -G (K.right e) at h1
    rw [← h0, ← h1]
    have hh : sigma * (eta (K.left e) - eta vm) - sigma * (eta (K.right e) - eta vm) =
        -sigma * (phi (J.left e) - phi (J.right e)) := by rw [← hs]; ring
    rw [hh, abs_mul]
    rcases hsigma with h | h <;> rw [h] <;> norm_num
  refine ⟨hlength, ?_, ?_, ?_, ?_⟩
  · intro e f hef
    rw [hsquare e, hsquare f, ← T.image_interior, ← T.image_interior]
    exact (Set.disjoint_image_iff T.injective).mpr (hd e f hef)
  · change (⋃ e : Copy D P marked, copiedSquare J phi (fun F => -G F) K.left K.right e) =
      Set.Icc 0 1 ×ˢ Set.Icc (-M) 0
    simp_rw [hsquare]
    rw [← Set.image_iUnion, hcover]
    have hm : (sigma = 1 ∧ eta vm = M) ∨ (sigma = -1 ∧ eta vm = 0) := by
      rcases hmode with ⟨h, _, hm⟩ | ⟨h, _, hm⟩
      · exact Or.inl ⟨h, hm⟩
      · exact Or.inr ⟨h, hm⟩
    have hT : (T : (ℝ × ℝ) → ℝ × ℝ) = verticalMap sigma (eta vm) :=
      funext (verticalHomeomorph_apply sigma (eta vm) hsigma)
    rw [hT]
    exact verticalMap_image_rectangle sigma (eta vm) M hm
  · intro e hzero
    exact zero_current_square J phi (fun F => -G F) K.left K.right e hzero (hlength e)
  · intro e
    exact (GeometryReview.quarterTurn_image_book_square J phi G K.left K.right e).symm

end
end FiniteAvalanches.Electrical.LovaszApplication

#print axioms FiniteAvalanches.Electrical.LovaszApplication.signed_copiedSquare_image
#print axioms FiniteAvalanches.Electrical.LovaszApplication.constructed_original_green_tiling
