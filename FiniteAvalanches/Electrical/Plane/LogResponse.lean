import FiniteAvalanches.Electrical.Plane.Charging

/-! The actual split response logarithmic estimate under explicit original rotation/Euler data. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.Geometry

/-- An explicit universal finite real constant depending only on the free-degree bound. -/
noncomputable def splitLogConstant (d : ℝ) : ℝ :=
  3*(1+2*d)*64*(4*(2*d+3)^2)^2*(3+Real.log 10/Real.log 2+1/Real.log 2)

theorem splitLogConstant_pos (d : ℝ) (hd : 1 ≤ d) : 0 < splitLogConstant d := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlin : 0 < 1+2*d := by linarith only [hd]
  have hdil : 0 < 2*d+3 := by linarith only [hd]
  unfold splitLogConstant
  positivity

/-- The logarithm's argument is at least one, and actual positive adjacent currents rule out M=0. -/
theorem split_current_scale_pos {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
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
    0 < energy a b phi ∧ 0 < min (s j0) (s j1) ∧
      1 ≤ min 1 (energy a b phi)/min (s j0) (s j1) ∧
      0 ≤ Real.log (min 1 (energy a b phi)/min (s j0) (s j1)) := by
  intro s
  obtain ⟨hmin,hbound,_,_⟩ := split_epsilon_bounds R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1
  have hM := hmin.trans_le (hbound.trans (min_le_right _ _))
  have hratio : 1 ≤ min 1 (energy a b phi)/min (s j0) (s j1) :=
    (le_div_iff₀ hmin).mpr (by simpa using hbound)
  exact ⟨hM,hmin,hratio,Real.log_nonneg hratio⟩

/-- No stream, geometry, packing, charging, response or bounded-energy conclusion is assumed.
The actual unique stream is obtained before trial/selection construction. Plane embedding transport
is a separate source obligation; the explicit rotation/common-RIGHT/Euler premises are internal. -/
theorem splitConductance_le_log_of_euler (d : ℤ) (hd : 2 ≤ d)
    {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (he : ∀ e, a e ≠ b e)
    (hc : (supportGraph a b).Preconnected) (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree a b x ≤ (d : ℝ))
    (phi : V → ℝ) (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (hpos : ∀ z : Dart E, tail a b z = alpha → 0 < phi (head a b z))
    (j0 j1 : Fin (incidenceCount a b alpha)) (hj : j0.val+1 = j1.val) :
    let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
    let side := orderedSide R alpha beta hne da db ha hb j1.val
    splitConductance a b alpha beta hne.symm side hc ≤
      splitLogConstant d*(1+Real.log (min 1 (energy a b phi)/min (s j0) (s j1))) := by
  intro s side
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ d by omega)
  obtain ⟨psi,⟨hp,h0,_,_,_⟩,_⟩ := existsUnique_stream_tiling_of_euler R alpha beta hne da db ha hb
    hc hface heuler (d : ℝ) hdeg phi hpa hpb hh
  have hs := alphaCurrentSequence_pos R alpha beta hne da db ha hb phi hpos
  have hscale := split_current_scale_pos R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1
  let epsilon := min (s j0) (s j1)/10
  let y0 := boundaryHeight s j1.val
  let f := splitTrial R alpha beta hne da db hc phi psi epsilon y0
  have hresponse := split_response_le_weightedEnergy a b alpha beta hne.symm side hc phi hpa hpb hh f rfl rfl
  have hcharge := splitTrial_weightedEnergy_le R alpha beta hne da db ha hb he hc phi hpa hpb hh
    psi hp h0 (d : ℝ) hd1 hdeg hs j0 j1 hj
  have hpack := actual_angular_energy_le_log R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs
    j0 j1 (2*(d : ℝ)+3) (by linarith)
  have hcpos : 0 ≤ 3*(1+2*(d : ℝ)) := by linarith only [hd1]
  have hsum := mul_le_mul_of_nonneg_left hpack hcpos
  have hfinal := hresponse.trans (hcharge.trans hsum)
  simpa only [splitLogConstant,mul_assoc] using hfinal

end FiniteAvalanches.Electrical.Plane
