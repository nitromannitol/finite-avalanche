import FiniteAvalanches.Electrical.Plane.Midpoints

/-! Canonical three-increment charging consumed on two actual free electrical endpoints. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- For actual positive-current maximal choices, free/free edge comparison retains its own square term.
The positive maximizers are obtained by exists_incident_max_current/exists_positive_max_square. -/
theorem free_edge_comparison_sq_le {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (hc : (supportGraph a b).Preconnected)
    (phi : V → ℝ) (M : ℝ) (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (d : ℝ) (hd : 1 ≤ d) (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree a b x ≤ d)
    (epsilon y0 : ℝ) (he : 0 < epsilon) (e : E)
    (ha0 : a e ≠ alpha) (ha1 : a e ≠ beta) (hb0 : b e ≠ alpha) (hb1 : b e ≠ beta)
    (za zb : Dart E) (hza : tail a b za = a e) (hzb : tail a b zb = b e)
    (hmaxa : |current a b phi za| = largestCurrent a b phi (a e) (incidenceDarts_nonempty a b alpha beta hne hc (a e)))
    (hmaxb : |current a b phi zb| = largestCurrent a b phi (b e) (incidenceDarts_nonempty a b alpha beta hne hc (b e)))
    (hposa : 0 < |current a b phi za|) (hposb : 0 < |current a b phi zb|) :
    let Q := fun i : E => incrementSquare R da db phi psi (i,false) (hp (.inl (i,false)))
    let lambda := 2*d+3
    let hl : 1 ≤ lambda := by linarith
    let f := splitTrial R alpha beta hne da db hc phi psi epsilon y0
    0 < (Q za.1).side ∧ 0 < (Q zb.1).side ∧
    (f (.inl ⟨a e,ha0⟩)-f (.inl ⟨b e,hb0⟩))^2 ≤
      3*((Q e).angularOsc epsilon y0 lambda hl he ^ 2 +
        (Q za.1).angularOsc epsilon y0 lambda hl he ^ 2 +
        (Q zb.1).angularOsc epsilon y0 lambda hl he ^ 2) := by
  intro Q lambda hl f
  let hx := incidenceDarts_nonempty a b alpha beta hne hc
  let p : Bool → ℝ × ℝ := fun c => if c then vertexMidpoint R da db phi psi (b e) (hx (b e))
    else vertexMidpoint R da db phi psi (a e) (hx (a e))
  let g : Bool → ℝ := fun c => angular epsilon y0 (p c)
  let q : Bool → Option E := fun c => some (if c then zb.1 else za.1)
  let z := sideMidpoint R da db phi psi (e,false)
  let t := sideMidpoint R da db phi psi (e,true)
  have hz : z ∈ (Q e).carrier := sideMidpoint_mem R da db phi psi (e,false) (hp (.inl (e,false)))
  have ht : t ∈ (Q e).carrier := by
    have h := sideMidpoint_mem R da db phi psi (e,true) (hp (.inl (e,true)))
    rw [incrementSquare_eq_original R da db phi psi M hp (e,true)] at h
    exact h
  have hsegz := incidentSquare_side_subset R alpha beta da db ha hb phi M psi hp (a e) ha0 ha1
    (hx (a e)) (e,false) (Or.inl rfl) z hz rfl
  have hsegt := incidentSquare_side_subset R alpha beta da db ha hb phi M psi hp (b e) hb0 hb1
    (hx (b e)) (e,false) (Or.inr rfl) t ht rfl
  have hsa := vertexSegment_subset_max_dilate R alpha beta da db ha hb phi M psi hp (a e) ha0 ha1
    (hx (a e)) d hd (hdeg (a e) ha0 ha1) za hza hmaxa
  have hsb := vertexSegment_subset_max_dilate R alpha beta da db ha hb phi M psi hp (b e) hb0 hb1
    (hx (b e)) d hd (hdeg (b e) hb0 hb1) zb hzb hmaxb
  have hpa : p false ∈ ((Q za.1).dilate lambda (by linarith)).carrier :=
    hsa (vertexMidpoint_mem R da db phi psi (a e) (hx (a e)))
  have hpb : p true ∈ ((Q zb.1).dilate lambda (by linarith)).carrier :=
    hsb (vertexMidpoint_mem R da db phi psi (b e) (hx (b e)))
  have hv : match q false with
      | none => g false = angular epsilon y0 z
      | some i => g false = angular epsilon y0 (p false) ∧
        p false ∈ ((Q i).dilate lambda (by linarith)).carrier ∧
        z ∈ ((Q i).dilate lambda (by linarith)).carrier := ⟨rfl,hpa,hsa hsegz⟩
  have hw : match q true with
      | none => g true = angular epsilon y0 t
      | some i => g true = angular epsilon y0 (p true) ∧
        p true ∈ ((Q i).dilate lambda (by linarith)).carrier ∧
        t ∈ ((Q i).dilate lambda (by linarith)).carrier := ⟨rfl,hpb,hsb hsegt⟩
  have h := angular_comparison_sq_le Q q epsilon y0 lambda he hl g p false true e z t
    ((Q e).carrier_subset_dilate lambda hl hz) ((Q e).carrier_subset_dilate lambda hl ht) hv hw
  have hfa : f (.inl ⟨a e,ha0⟩) = g false := by
    simp only [f,splitTrial,if_neg ha1,g,p,Bool.false_eq_true,↓reduceIte]
  have hfb : f (.inl ⟨b e,hb0⟩) = g true := by
    simp only [f,splitTrial,if_neg hb1,g,p,↓reduceIte]
  have hqa : 0 < (Q za.1).side := by
    dsimp only [Q]
    rw [← incrementSquare_eq_original R da db phi psi M hp za]
    exact hposa
  have hqb : 0 < (Q zb.1).side := by
    dsimp only [Q]
    rw [← incrementSquare_eq_original R da db phi psi M hp zb]
    exact hposb
  refine ⟨hqa,hqb,?_⟩
  rw [hfa,hfb]
  simpa only [selectedCharge,q,Bool.false_eq_true,↓reduceIte,Option.elim_some] using h

end FiniteAvalanches.Electrical.Plane
