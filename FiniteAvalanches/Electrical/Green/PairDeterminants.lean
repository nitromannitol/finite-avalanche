import FiniteAvalanches.Electrical.Green.PairTelescoping
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The two literal two-by-two Green determinants and their expanded pair expression. -/
namespace FiniteAvalanches.Electrical

/-- Pure determinant algebra; no forest count or probability identity is an input. -/
theorem boundaryPairKernel_eq_det_sub_det {m : ℕ}
    (G : Fin (m+1) → Fin (m+1) → ℝ) (hs : ∀ i j, G i j = G j i) (i j : Fin m) :
    boundaryPairKernel G i j =
      Matrix.det !![G 0 i.castSucc-G 0 j.succ, G 0 j.castSucc-G 0 j.succ;
        G i.succ i.castSucc-G i.succ j.succ, G i.succ j.castSucc-G i.succ j.succ] -
      Matrix.det !![G 0 i.succ-G 0 j.succ, G 0 j.castSucc-G 0 j.succ;
        G i.castSucc i.succ-G i.castSucc j.succ, G i.castSucc j.castSucc-G i.castSucc j.succ] := by
  rw [Matrix.det_fin_two_of,Matrix.det_fin_two_of,hs i.succ i.castSucc]
  unfold boundaryPairKernel
  ring

end FiniteAvalanches.Electrical
