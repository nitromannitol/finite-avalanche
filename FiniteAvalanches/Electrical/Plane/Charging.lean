import FiniteAvalanches.Electrical.Plane.EndpointFits

/-! The actual global once-counted weighted energy bound, with no exceptional copies. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.Geometry

/-- All endpoint fits are constructed; only beta's true zero weight removes an edge.
The canonical charge count retains one own-square term and at most 2d endpoint terms. -/
theorem splitTrial_weightedEnergy_le {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (he : ∀ e, a e ≠ b e)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0)
    (d : ℝ) (hd : 1 ≤ d) (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree a b x ≤ d)
    (hs : ∀ i, 0 < alphaCurrentSequence R alpha beta hne da db ha hb phi i)
    (j0 j1 : Fin (incidenceCount a b alpha)) (hj : j0.val+1 = j1.val) :
    let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
    let epsilon := min (s j0) (s j1)/10
    let y0 := boundaryHeight s j1.val
    let side := orderedSide R alpha beta hne da db ha hb j1.val
    let A := fun e => splitEndpoint alpha side (a e) e
    let B := fun e => splitEndpoint alpha side (b e) e
    let f := splitTrial R alpha beta hne da db hc phi psi epsilon y0
    let heps := (split_epsilon_bounds R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1).2.2.1
    weightedEnergy A B (fun v => 1-phi (collapse alpha v)) f ≤
      3*(1+2*d)*∑ e : E,
        ((incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).angularOsc
          epsilon y0 (2*d+3) (by linarith) heps)^2 := by
  intro s epsilon y0 side A B f heps
  let Q := fun e => incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))
  let weight := fun v : SplitVertex alpha => 1-phi (collapse alpha v)
  let p := splitMidpoint R alpha beta hne da db hc phi psi
  let z := fun e => sideMidpoint R da db phi psi (e,false)
  let t := fun e => sideMidpoint R da db phi psi (e,true)
  obtain ⟨q,_,_,_,hqi,hqd,hfit⟩ := exists_split_endpointFits R alpha beta hne da db ha hb he hc
    phi hpa psi hp h0 d hd hdeg hs j0 j1 hj
  have hw : ∀ v, 0 ≤ weight v ∧ weight v ≤ 1 := by
    intro v
    have hr := voltage_range a b alpha beta hc phi hpa hpb hh (collapse alpha v)
    constructor <;> dsimp only [weight] <;> linarith only [hr.1,hr.2]
  have hnot (e : E) (h : weight (A e)*weight (B e) ≠ 0) : a e ≠ beta ∧ b e ≠ beta := by
    have hwab : weight (A e)*weight (B e) = (1-phi (a e))*(1-phi (b e)) := by
      simp only [weight,A,B,collapse_splitEndpoint]
    constructor
    · intro heq; apply h; rw [hwab,heq,hpb]; ring
    · intro heq; apply h; rw [hwab,heq,hpb]; ring
  have hz (e : E) : z e ∈ ((Q e).dilate (2*d+3) (by linarith)).carrier ∧
      t e ∈ ((Q e).dilate (2*d+3) (by linarith)).carrier := by
    constructor
    · exact (Q e).carrier_subset_dilate _ (by linarith)
        (sideMidpoint_mem R da db phi psi (e,false) (hp (.inl (e,false))))
    · apply (Q e).carrier_subset_dilate _ (by linarith)
      have hm := sideMidpoint_mem R da db phi psi (e,true) (hp (.inl (e,true)))
      rw [incrementSquare_eq_original R da db phi psi (energy a b phi) hp (e,true)] at hm
      exact hm
  have h := dirichlet_charging_le A B Q q epsilon y0 (2*d+3) d heps (by linarith) (by linarith)
    f weight p z t ∅ (by simp) hw (fun v e hv => (hqi v e hv).1) hqd
    (fun e _ _ => hz e)
    (fun e _ h => hfit (e,false) (hnot e h).1)
    (fun e _ h => hfit (e,true) (hnot e h).2)
  simpa only [Finset.card_empty,Nat.cast_zero,zero_add,weightedEnergy] using h

end FiniteAvalanches.Electrical.Plane
