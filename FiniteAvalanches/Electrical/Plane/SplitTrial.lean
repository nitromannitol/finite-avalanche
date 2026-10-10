import FiniteAvalanches.Electrical.Plane.SplitFormation
import FiniteAvalanches.Electrical.Plane.AngularEnergy
import FiniteAvalanches.Electrical.Plane.FreeSegments

/-! Actual ordered split coordinates, response cancellation and logarithmic square energy.
The remaining weighted endpoint-charge assembly is not asserted here. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.Geometry

/-- Source-faithful split trial construction under the honest original rotation/Euler data. -/
theorem exists_split_trial_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (he : ∀ e, a e ≠ b e)
    (hc : (supportGraph a b).Preconnected) (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (d : ℝ) (hd : 1 ≤ d) (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree a b x ≤ d)
    (phi : V → ℝ) (hpa : phi alpha = 0) (hpb : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (hpos : ∀ z : Dart E, tail a b z = alpha → 0 < phi (head a b z))
    (j0 j1 : Fin (incidenceCount a b alpha)) (hj : j0.val+1 = j1.val) :
    ∃ psi : ArcFace R da db → ℝ,
      ∃ hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z,
        psi (arcRightFace R da db (.inr false)) = 0 ∧
        let s := alphaCurrentSequence R alpha beta hne da db ha hb phi
        let epsilon := min (s j0) (s j1)/10
        let y0 := boundaryHeight s j1.val
        let side := orderedSide R alpha beta hne da db ha hb j1.val
        let A := fun e => splitEndpoint alpha side (a e) e
        let B := fun e => splitEndpoint alpha side (b e) e
        let f := splitTrial R alpha beta hne da db hc phi psi epsilon y0
        let weight := fun x => 1-phi (collapse alpha x)
        ∃ heps : 0 < epsilon,
          epsilon ≤ min 1 (energy a b phi) ∧
          0 ≤ splitConductance a b alpha beta hne.symm side hc ∧
          splitConductance a b alpha beta hne.symm side hc ≤ weightedEnergy A B weight f ∧
          energy A B (fun x => (1/2 : ℝ)+weight x*(f x-1/2)) =
            energy a b phi/4 + weightedEnergy A B weight f ∧
          (∀ i : Fin (incidenceCount a b alpha),
            f (.inr (side (alphaEnumeration R alpha beta hne da db ha hb i).val.1)) =
              angular epsilon y0 (sideMidpoint R da db phi psi
                (alphaEnumeration R alpha beta hne da db ha hb i).val)) ∧
          (∑ e : E, ((incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).angularOsc
            epsilon y0 (2*d+3) (by linarith) heps)^2) ≤
            64*(4*(2*d+3)^2)^2 * (3+Real.log 10/Real.log 2+1/Real.log 2) *
              (1+Real.log (min 1 (energy a b phi)/min (s j0) (s j1))) ∧
          ∀ x, x ≠ alpha → x ≠ beta →
            let hx := incidenceDarts_nonempty a b alpha beta hne hc x
            vertexMidpoint R da db phi psi x hx ∈ vertexSegment R da db phi psi x hx ∧
            (largestCurrent a b phi x hx = 0 → ∀ p ∈ vertexSegment R da db phi psi x hx,
              vertexMidpoint R da db phi psi x hx = p) ∧
            (0 < largestCurrent a b phi x hx →
              ∃ e : E, (a e = x ∨ b e = x) ∧
                (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).side = largestCurrent a b phi x hx ∧
                0 < (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).side ∧
                vertexSegment R da db phi psi x hx ⊆
                  ((incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).dilate (2*d+3) (by linarith)).carrier) := by
  obtain ⟨psi,⟨hp,h0,_,_,_⟩,_⟩ := existsUnique_stream_tiling_of_euler R alpha beta hne da db ha hb
    hc hface heuler d hdeg phi hpa hpb hh
  have hs := alphaCurrentSequence_pos R alpha beta hne da db ha hb phi hpos
  have hbds := split_epsilon_bounds R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1
  refine ⟨psi,hp,h0,hbds.2.2.1,hbds.2.2.2,splitConductance_nonneg a b alpha beta hne.symm _ hc,?_,?_,?_,?_,?_⟩
  · exact split_response_le_weightedEnergy a b alpha beta hne.symm _ hc phi hpa hpb hh _ rfl rfl
  · exact split_trial_energy_eq a b alpha beta hne.symm _ phi hpa hpb hh _ rfl rfl
  · intro i
    exact splitTrial_alpha_midpoint R alpha beta hne da db ha hb he hc phi hpa psi hp h0 hs j0 j1 hj i
  · exact actual_angular_energy_le_log R alpha beta hne da db ha hb hc phi hpa hpb hh psi hp h0 hs j0 j1
      (2*d+3) (by linarith)
  · intro x hx0 hx1
    let hx := incidenceDarts_nonempty a b alpha beta hne hc x
    exact ⟨vertexMidpoint_mem R da db phi psi x hx,
      fun hz p hpseg => zero_free_midpoint_eq R alpha beta da db ha hb phi (energy a b phi) psi hp
        x hx0 hx1 hx hz p hpseg,
      exists_positive_max_square R alpha beta da db ha hb phi (energy a b phi) psi hp x hx0 hx1 hx
        d hd (hdeg x hx0 hx1)⟩

end FiniteAvalanches.Electrical.Plane
