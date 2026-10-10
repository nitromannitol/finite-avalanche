import FiniteAvalanches.Electrical.Plane.TrialResponse
import FiniteAvalanches.Electrical.Geometry.Dirichlet
import FiniteAvalanches.Electrical.Geometry.Logarithm

/-! The logarithmic angular sum is consumed on the constructed electrical square family. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.Geometry

theorem alpha_current_eq_square_side {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (hpa : phi alpha = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z)
    (i : Fin (incidenceCount a b alpha))
    (hi : 0 ≤ alphaCurrentSequence R alpha beta hne da db ha hb phi i) :
    alphaCurrentSequence R alpha beta hne da db ha hb phi i =
      (incrementSquare R da db phi psi (alphaEnumeration R alpha beta hne da db ha hb i).val
        (hp (.inl (alphaEnumeration R alpha beta hne da db ha hb i).val))).side := by
  dsimp only [incrementSquare,current]
  rw [(alphaEnumeration R alpha beta hne da db ha hb i).property,hpa,zero_sub,abs_neg]
  exact (abs_of_nonneg hi).symm

/-- Epsilon and both adjacent currents have the actual source normalization. -/
theorem split_epsilon_bounds {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0)
    (hs : ∀ i, 0 < alphaCurrentSequence R alpha beta hne da db ha hb phi i)
    (j0 j1 : Fin (incidenceCount a b alpha)) :
    let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
    0 < min (s j0) (s j1) ∧ min (s j0) (s j1) ≤ min 1 (energy a b phi) ∧
      0 < min (s j0) (s j1)/10 ∧ min (s j0) (s j1)/10 ≤ min 1 (energy a b phi) := by
  intro s
  have hpmin : 0 < min (s j0) (s j1) := lt_min (hs j0) (hs j1)
  have hbound (i : Fin (incidenceCount a b alpha)) : s i ≤ min 1 (energy a b phi) := by
    dsimp only [s]
    rw [alpha_current_eq_square_side R alpha beta hne da db ha hb phi hpa psi hp i (hs i).le]
    exact Square.side_le_min_of_subset _ _
      (incrementSquare_subset_rectangle R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 _)
  have hb : min (s j0) (s j1) ≤ min 1 (energy a b phi) := (min_le_left _ _).trans (hbound j0)
  exact ⟨hpmin,hb,div_pos hpmin (by norm_num),by linarith only [hb,hpmin]⟩

/-- No packing premise: original electrical square disjointness supplies the canonical dyadic estimate. -/
theorem actual_angular_energy_le_log {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0)
    (hs : ∀ i, 0 < alphaCurrentSequence R alpha beta hne da db ha hb phi i)
    (j0 j1 : Fin (incidenceCount a b alpha)) (lambda : ℝ) (hl : 1 ≤ lambda) :
    let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
    let epsilon := min (s j0) (s j1)/10
    let he := (split_epsilon_bounds R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1).2.2.1
    (∑ e : E, ((incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).angularOsc
      epsilon (boundaryHeight s j1.val) lambda hl he)^2) ≤
      64*(4*lambda^2)^2 * (3+Real.log 10/Real.log 2+1/Real.log 2) *
        (1+Real.log (min 1 (energy a b phi)/min (s j0) (s j1))) := by
  intro s epsilon he
  obtain ⟨hmin,hminM,_,heM⟩ := split_epsilon_bounds R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1
  let Q := fun e : E => incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))
  have hd := square_open_disjoint R alpha beta hne da db ha hb hc phi hpa hpb hh (energy a b phi) psi hp
  have hQ := fun e : E => incrementSquare_subset_rectangle R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 (e,false)
  have h := angular_energy_le_log Finset.univ Q hd (energy a b phi) epsilon (boundaryHeight s j1.val)
    lambda (energy_nonneg a b phi) he heM hl (fun e _ => hQ e)
  have ht := log_bound_tenth (min 1 (energy a b phi)) (min (s j0) (s j1)) hmin hminM
  have hn : 0 ≤ 64*(4*lambda^2)^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left ht hn
  simpa only [mul_assoc] using h.trans hm

/-- The unique actual Euler stream is obtained before its literal angular-packing consumer. -/
theorem exists_stream_angular_energy_bound_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (d : ℝ) (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree a b x ≤ d)
    (phi : V → ℝ) (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (hs : ∀ i, 0 < alphaCurrentSequence R alpha beta hne da db ha hb phi i)
    (j0 j1 : Fin (incidenceCount a b alpha)) (lambda : ℝ) (hl : 1 ≤ lambda) :
    ∃ psi : ArcFace R da db → ℝ,
      ∃ hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z,
        psi (arcRightFace R da db (.inr false)) = 0 ∧
        let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
        let epsilon := min (s j0) (s j1)/10
        ∃ he : 0 < epsilon,
          (∑ e : E, ((incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).angularOsc
            epsilon (boundaryHeight s j1.val) lambda hl he)^2) ≤
            64*(4*lambda^2)^2 * (3+Real.log 10/Real.log 2+1/Real.log 2) *
              (1+Real.log (min 1 (energy a b phi)/min (s j0) (s j1))) := by
  obtain ⟨psi,⟨hp,h0,_,_,_⟩,_⟩ := existsUnique_stream_tiling_of_euler R alpha beta hne da db ha hb
    hc hface heuler d hdeg phi hpa hpb hh
  exact ⟨psi,hp,h0,(split_epsilon_bounds R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1).2.2.1,
    actual_angular_energy_le_log R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1 lambda hl⟩

end FiniteAvalanches.Electrical.Plane
