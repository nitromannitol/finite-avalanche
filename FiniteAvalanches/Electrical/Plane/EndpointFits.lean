import FiniteAvalanches.Electrical.Plane.SplitSelection
import FiniteAvalanches.Electrical.Plane.Midpoints

/-! Global endpoint fits are derived from actual alpha midpoints and free-vertex segments. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- One selection fits every actual non-beta dart endpoint, including zero-current points.
The middle comparison remains on its own original square. -/
theorem exists_split_endpointFits {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (he : ∀ e, a e ≠ b e)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (hpa : phi alpha = 0)
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
    let Q := fun e => incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))
    let f := splitTrial R alpha beta hne da db hc phi psi epsilon y0
    let p := splitMidpoint R alpha beta hne da db hc phi psi
    ∃ q : SplitVertex alpha → Option E,
      (∀ k, q (.inr k) = none) ∧
      (∀ x, x.val = beta → q (.inl x) = none) ∧
      (∀ x : {x : V // x ≠ alpha}, x.val ≠ beta →
        (q (.inl x) = none ↔ largestCurrent a b phi x.val
          (incidenceDarts_nonempty a b alpha beta hne hc x.val) = 0)) ∧
      (∀ v e, q v = some e → (v = A e ∨ v = B e) ∧ 0 < (Q e).side) ∧
      (∀ v, q v ≠ none → degree A B v ≤ d) ∧
      ∀ z : Dart E, tail a b z ≠ beta →
        endpointFits Q q epsilon y0 (2*d+3) (by linarith) f p
          (splitEndpoint alpha side (tail a b z) z.1) (sideMidpoint R da db phi psi z) := by
  intro s epsilon y0 side A B Q f p
  obtain ⟨q,hqr,hqb,hqf⟩ := exists_split_max_selection R alpha beta hne da db ha hb hc phi
    (energy a b phi) psi hp d hd hdeg
  have hqi : ∀ v e, q v = some e → (v = A e ∨ v = B e) ∧ 0 < (Q e).side := by
    intro v e hqe
    cases v with
    | inr k => rw [hqr k] at hqe; contradiction
    | inl x =>
      have hxb : x.val ≠ beta := by
        intro h; rw [hqb x h] at hqe; contradiction
      obtain ⟨hinc,_,hpos,_⟩ := (hqf x hxb).2 e hqe
      refine ⟨?_,hpos⟩
      rcases hinc with h | h
      · exact Or.inl ((splitEndpoint_eq_inl alpha side (a e) e x).mpr h).symm
      · exact Or.inr ((splitEndpoint_eq_inl alpha side (b e) e x).mpr h).symm
  have hqd : ∀ v, q v ≠ none → degree A B v ≤ d := by
    intro v hv
    cases v with
    | inr k => exact (hv (hqr k)).elim
    | inl x =>
      have hxb : x.val ≠ beta := fun h => hv (hqb x h)
      rw [split_degree_inl]
      exact hdeg x.val x.property hxb
  refine ⟨q,hqr,hqb,fun x h => (hqf x h).1,hqi,hqd,?_⟩
  intro z hzb
  by_cases hza : tail a b z = alpha
  · have hsplit : splitEndpoint alpha side (tail a b z) z.1 = .inr (side z.1) := by
      simp [hza,splitEndpoint]
    rw [hsplit]
    unfold endpointFits
    rw [hqr]
    let i := (alphaEnumeration R alpha beta hne da db ha hb).symm ⟨z,hza⟩
    have hi : (alphaEnumeration R alpha beta hne da db ha hb i).val = z :=
      congrArg Subtype.val ((alphaEnumeration R alpha beta hne da db ha hb).apply_symm_apply ⟨z,hza⟩)
    have hv := splitTrial_alpha_midpoint R alpha beta hne da db ha hb he hc phi hpa psi hp h0 hs j0 j1 hj i
    simpa only [hi] using hv
  · let x : {x : V // x ≠ alpha} := ⟨tail a b z,hza⟩
    let hx := incidenceDarts_nonempty a b alpha beta hne hc x.val
    have hsplit : splitEndpoint alpha side (tail a b z) z.1 = .inl x :=
      (splitEndpoint_eq_inl alpha side (tail a b z) z.1 x).mpr rfl
    have hmid : f (.inl x) = angular epsilon y0 (p (.inl x)) := by
      dsimp only [f,splitTrial,p,splitMidpoint,collapse]
      rw [if_neg (show x.val ≠ beta from hzb)]
    have hzm : sideMidpoint R da db phi psi z ∈ vertexSegment R da db phi psi x.val hx := by
      apply incidentSquare_side_subset R alpha beta da db ha hb phi (energy a b phi) psi hp
        x.val hza hzb hx z (Or.inl rfl) _ (sideMidpoint_mem R da db phi psi z (hp (.inl z))) rfl
    rw [hsplit]
    unfold endpointFits
    cases hqx : q (.inl x) with
    | none =>
      have hzero := (hqf x hzb).1.mp hqx
      have hm := zero_free_midpoint_eq R alpha beta da db ha hb phi (energy a b phi) psi hp
        x.val hza hzb hx hzero _ hzm
      change f (.inl x) = angular epsilon y0 _
      rw [hmid]
      exact congrArg (angular epsilon y0) hm
    | some e =>
      obtain ⟨_,_,_,hsub⟩ := (hqf x hzb).2 e hqx
      exact ⟨hmid,hsub (vertexMidpoint_mem R da db phi psi x.val hx),hsub hzm⟩

end FiniteAvalanches.Electrical.Plane
