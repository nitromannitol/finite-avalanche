import FiniteAvalanches.Electrical.Plane.Ranges

/-! Every actual electrical square is contained in the normalized closed rectangle.
No tiling, disjointness or bounded-stream premise is used. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.Geometry

/-- Maximum principles give closed rectangle containment for every original copied edge. -/
theorem incrementSquare_subset_rectangle {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) =
      arcCurrent a b phi (energy a b phi) d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) (d : Dart E) :
    (incrementSquare R da db phi psi d (hp (.inl d))).carrier ⊆ rectangle 0 1 0 (energy a b phi) := by
  rw [incrementSquare_carrier]
  have hv := voltage_range a b alpha beta hc phi hp0 hp1 hh
  have hs := stream_range R alpha beta hne da db ha hb hc phi (energy a b phi)
    (energy_nonneg a b phi) psi hp h0
  intro z hz
  change z.1 ∈ Set.Icc _ _ ∧ z.2 ∈ Set.Icc _ _ at hz
  change z.1 ∈ Set.Icc 0 1 ∧ z.2 ∈ Set.Icc 0 (energy a b phi)
  exact ⟨⟨(le_min (hv _).1 (hv _).1).trans hz.1.1,
      hz.1.2.trans (max_le (hv _).2 (hv _).2)⟩,
    ⟨(le_min (hs _).1 (hs _).1).trans hz.2.1,
      hz.2.2.trans (max_le (hs _).2 (hs _).2)⟩⟩

/-- Each current is at most min(1,M), already from the two maximum principles. -/
theorem current_le_theta {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ)
    (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) =
      arcCurrent a b phi (energy a b phi) d)
    (h0 : psi (arcRightFace R da db (.inr false)) = 0) (d : Dart E) :
    |current a b phi d| ≤ min 1 (energy a b phi) := by
  have ht := voltage_range a b alpha beta hc phi hp0 hp1 hh (tail a b d)
  have hh' := voltage_range a b alpha beta hc phi hp0 hp1 hh (head a b d)
  have hv : |current a b phi d| ≤ 1 := by
    unfold current
    exact abs_le.mpr ⟨by linarith only [ht.1,hh'.2],by linarith only [ht.2,hh'.1]⟩
  have hl := stream_range R alpha beta hne da db ha hb hc phi (energy a b phi)
    (energy_nonneg a b phi) psi hp h0 (arcLeftFace R da db (.inl d))
  have hr := stream_range R alpha beta hne da db ha hb hc phi (energy a b phi)
    (energy_nonneg a b phi) psi hp h0 (arcRightFace R da db (.inl d))
  have hs : |psi (arcLeftFace R da db (.inl d))-psi (arcRightFace R da db (.inl d))| ≤ energy a b phi :=
    abs_le.mpr ⟨by linarith only [hl.1,hr.2],by linarith only [hl.2,hr.1]⟩
  rw [hp (.inl d)] at hs
  exact le_min hv hs

/-- The actual constructed stream consumes both range and containment results jointly. -/
theorem existsUnique_bounded_stream_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    ∃! psi : ArcFace R da db → ℝ,
      (∃ hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) =
          arcCurrent a b phi (energy a b phi) d,
        psi (arcRightFace R da db (.inr false)) = 0 ∧
        (∀ f, 0 ≤ psi f ∧ psi f ≤ energy a b phi) ∧
        ∀ d : Dart E, (incrementSquare R da db phi psi d (hp (.inl d))).carrier ⊆
          rectangle 0 1 0 (energy a b phi)) := by
  obtain ⟨psi,hpsi,hu⟩ := existsUnique_normalized_stream_of_euler
    R alpha beta hne da db ha hb hc hface heuler phi hp0 hp1 hh
  refine ⟨psi,⟨hpsi.1,hpsi.2,?_,?_⟩,?_⟩
  · exact stream_range R alpha beta hne da db ha hb hc phi (energy a b phi)
      (energy_nonneg a b phi) psi hpsi.1 hpsi.2
  · exact incrementSquare_subset_rectangle R alpha beta hne da db ha hb hc phi hp0 hp1 hh psi hpsi.1 hpsi.2
  · intro chi hchi
    obtain ⟨hj,hzero,_⟩ := hchi
    exact hu chi ⟨hj,hzero⟩

end FiniteAvalanches.Electrical.Plane
