import FiniteAvalanches.Electrical.Plane.Incidences

/-! The incident-face range is bounded by once-counted cyclic current variation. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.Geometry

/-- The actual rotation orbit is exactly the original incidence fiber. -/
theorem rotation_cyclePoints_eq_incidenceDarts {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (x : V) (d : Dart E) (hd : tail a b d = x) :
    cyclePoints R.next d = incidenceDarts a b x := by
  ext z
  rw [mem_cyclePoints,R.cycles,mem_incidenceDarts,hd,eq_comm]

/-- Going once around the free vertex charges each original incidence once. -/
theorem incident_pair_le_current_sum {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta)
    (d e : Dart E) (hd : tail a b d = x) (he : tail a b e = x) :
    |psi (arcLeftFace R da db (.inl d))-psi (arcLeftFace R da db (.inl e))| ≤
      ∑ z ∈ incidenceDarts a b x, |current a b phi z| := by
  let F := fun z : Dart E => psi (arcLeftFace R da db (.inl z))
  have hcycle : R.next.SameCycle e d := (R.cycles e d).mpr (he.trans hd.symm)
  have hv := orbit_pair_variation R.next F e d hcycle
  rw [rotation_cyclePoints_eq_incidenceDarts R x e he] at hv
  have hstep (z : Dart E) (hz : z ∈ incidenceDarts a b x) :
      |F (R.next z)-F z| = |current a b phi z| := by
    have h := hp (.inl z)
    change psi (arcLeftFace R da db (.inl z))-psi (arcRightFace R da db (.inl z)) = current a b phi z at h
    dsimp [F]
    rw [free_leftFace_next R alpha beta da db ha hb x hx0 hx1 z ((mem_incidenceDarts a b x z).mp hz),abs_sub_comm,h]
  exact hv.trans_eq (Finset.sum_congr rfl hstep)

/-- The min/max height difference is bounded by the actual copied current sum. -/
theorem stream_span_le_current_sum {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty) :
    streamMax R da db psi x hx-streamMin R da db psi x hx ≤
      ∑ z ∈ incidenceDarts a b x, |current a b phi z| := by
  have hlo : streamMin R da db psi x hx ∈ incidentHeights R da db psi x :=
    Finset.min'_mem _ _
  have hhi : streamMax R da db psi x hx ∈ incidentHeights R da db psi x :=
    Finset.max'_mem _ _
  obtain ⟨lo,hloD,hlo⟩ := Finset.mem_image.mp hlo
  obtain ⟨hi,hhiD,hhi⟩ := Finset.mem_image.mp hhi
  have hbnd := incident_pair_le_current_sum R alpha beta da db ha hb phi M psi hp x hx0 hx1 hi lo
    ((mem_incidenceDarts a b x hi).mp hhiD) ((mem_incidenceDarts a b x lo).mp hloD)
  rw [hhi,hlo] at hbnd
  exact (le_abs_self _).trans hbnd

/-- The source segment bound with literal copied degree and largest incident current. -/
theorem stream_span_le_degree_mul {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ d, psi (arcLeftFace R da db d)-psi (arcRightFace R da db d) = arcCurrent a b phi M d)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty)
    (d : ℝ) (hdeg : degree a b x ≤ d) :
    streamMax R da db psi x hx-streamMin R da db psi x hx ≤ d*largestCurrent a b phi x hx :=
  (stream_span_le_current_sum R alpha beta da db ha hb phi M psi hp x hx0 hx1 hx).trans
    ((sum_incident_current_le a b phi x hx).trans
      (mul_le_mul_of_nonneg_right hdeg (largestCurrent_nonneg a b phi x hx)))

/-- The height span is nonnegative, including singleton height carriers. -/
theorem stream_span_nonneg {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (psi : ArcFace R da db → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) :
    0 ≤ streamMax R da db psi x hx-streamMin R da db psi x hx := by
  have hex := hx
  obtain ⟨d,hd⟩ := hex
  have h := incident_left_bounds R da db psi x hx d ((mem_incidenceDarts a b x d).mp hd)
  exact sub_nonneg.mpr (h.1.trans h.2)

end FiniteAvalanches.Electrical.Plane
