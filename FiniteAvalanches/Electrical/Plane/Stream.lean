import FiniteAvalanches.Electrical.Plane.StreamExistence
import FiniteAvalanches.Electrical.Plane.TerminalIntervals

/-! The physical harmonic flow is integrated without assuming a stream conclusion.
The explicit rotation/Euler premises still need their source plane-embedding bridge. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.Geometry

/-- A unique physical stream with the exterior zero gauge, derived from harmonicity and topology. -/
theorem existsUnique_normalized_stream_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    ∃! psi : ArcFace R da db → ℝ,
      (∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) =
        arcCurrent a b phi (energy a b phi) d) ∧
      psi (arcRightFace R da db (.inr false)) = 0 := by
  have hj (x : V) : copyBoundary (arcA a alpha) (arcB b beta)
      (physicalArcFlow a b phi (energy a b phi)) x = 0 := by
    rw [copyBoundary_physical]
    exact arcDivergence_eq_zero a b phi alpha beta hne hp0 hp1 hh x
  simpa only [arcSignedFlow_physical,streamBase] using
    existsUnique_stream_of_euler R alpha beta hne da db ha hb hc hface heuler
      (physicalArcFlow a b phi (energy a b phi)) hj

/-- The stream just constructed has both exterior values and every exact ordered terminal interval. -/
theorem existsUnique_stream_intervals_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    (∃! psi : ArcFace R da db → ℝ,
      (∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) =
        arcCurrent a b phi (energy a b phi) d) ∧
      psi (arcRightFace R da db (.inr false)) = 0 ∧
      psi (arcLeftFace R da db (.inr false)) = energy a b phi ∧
      ∀ i : Fin (incidenceCount a b alpha),
        psi (arcLeftFace R da db (.inl (alphaEnumeration R alpha beta hne da db ha hb i).val)) =
          boundaryHeight (alphaCurrentSequence R alpha beta hne da db ha hb phi) i.val ∧
        psi (arcRightFace R da db (.inl (alphaEnumeration R alpha beta hne da db ha hb i).val)) =
          boundaryHeight (alphaCurrentSequence R alpha beta hne da db ha hb phi) i.val+
            alphaCurrentSequence R alpha beta hne da db ha hb phi i) ∧
    (∑ i, alphaCurrentSequence R alpha beta hne da db ha hb phi i) = energy a b phi := by
  obtain ⟨psi,hpsi,hunique⟩ := existsUnique_normalized_stream_of_euler
    R alpha beta hne da db ha hb hc hface heuler phi hp0 hp1 hh
  refine ⟨⟨psi,⟨hpsi.1,hpsi.2,?_,?_⟩,?_⟩,?_⟩
  · exact exterior_stream_values R da db phi psi (energy a b phi) (hpsi.1 (.inr false)) hpsi.2
  · exact alpha_stream_interval R alpha beta hne da db ha hb phi hp0 psi hpsi.1 hpsi.2
  · intro chi hchi
    exact hunique chi ⟨hchi.1,hchi.2.1⟩
  · exact sum_alphaCurrentSequence_eq_energy R alpha beta hne da db ha hb phi hp0 psi hpsi.1 hpsi.2

/-- A zero copied current gives equal values on the two actual adjacent faces. -/
theorem stream_zero_current {V E : Type*} {a b : E → V} (R : EdgeRotation a b)
    (da db : Dart E) (j : ArcEdge E → ℝ) (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcSignedFlow j d)
    (e : ArcEdge E) (he : j e = 0) : psi (dualB R da db e) = psi (dualA R da db e) := by
  have h := hp (arcForward e)
  rw [arcSignedFlow_forward,he] at h
  exact sub_eq_zero.mp h

end FiniteAvalanches.Electrical.Plane
