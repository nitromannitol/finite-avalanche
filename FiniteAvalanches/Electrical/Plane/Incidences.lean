import FiniteAvalanches.Electrical.Plane.Variation
import FiniteAvalanches.Electrical.Plane.TerminalEnumeration
import FiniteAvalanches.Electrical.Plane.Squares

/-! Actual nonempty incidence fibers and literal incident stream extrema. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.Geometry

noncomputable def incidenceDarts {V E : Type*} [Fintype E] (a b : E → V) (x : V) : Finset (Dart E) :=
  Finset.univ.filter (fun d => tail a b d = x)

@[simp] theorem mem_incidenceDarts {V E : Type*} [Fintype E] (a b : E → V) (x : V) (d : Dart E) :
    d ∈ incidenceDarts a b x ↔ tail a b d = x := by simp [incidenceDarts]

/-- Connectedness and distinct terminals establish nonempty incidence before defining extrema. -/
theorem incidenceDarts_nonempty {V E : Type*} [Fintype E] (a b : E → V)
    (alpha beta : V) (hne : alpha ≠ beta) (hc : (supportGraph a b).Preconnected) (x : V) :
    (incidenceDarts a b x).Nonempty := by
  letI : Nontrivial V := ⟨⟨alpha,beta,hne⟩⟩
  obtain ⟨y,_,e,he⟩ := hc.exists_adj_of_nontrivial x
  rcases he with he | he
  · exact ⟨(e,false),(mem_incidenceDarts a b x _).mpr he.1⟩
  · exact ⟨(e,true),(mem_incidenceDarts a b x _).mpr he.1⟩

theorem incidenceDarts_card {V E : Type*} [Fintype E] (a b : E → V) (x : V) :
    (incidenceDarts a b x).card = incidenceCount a b x := by
  simp only [incidenceCount,Fintype.card_subtype,incidenceDarts]

/-- Left-face values at all original outgoing incidences; repeated face positions are retained before image. -/
noncomputable def incidentHeights {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (psi : ArcFace R da db → ℝ) (x : V) : Finset ℝ :=
  (incidenceDarts a b x).image (fun d => psi (arcLeftFace R da db (.inl d)))

theorem incidentHeights_nonempty {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (psi : ArcFace R da db → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) : (incidentHeights R da db psi x).Nonempty := hx.image _

noncomputable def streamMin {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (psi : ArcFace R da db → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) : ℝ :=
  (incidentHeights R da db psi x).min' (incidentHeights_nonempty R da db psi x hx)

noncomputable def streamMax {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (psi : ArcFace R da db → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) : ℝ :=
  (incidentHeights R da db psi x).max' (incidentHeights_nonempty R da db psi x hx)

/-- The actual vertical segment at the vertex's voltage, with no empty-set convention. -/
noncomputable def vertexSegment {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (phi : V → ℝ) (psi : ArcFace R da db → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) : Set (ℝ × ℝ) :=
  rectangle (phi x) (phi x) (streamMin R da db psi x hx) (streamMax R da db psi x hx)

/-- Maximum absolute current over actual original incidences; parallel copy IDs are not collapsed. -/
noncomputable def largestCurrent {V E : Type*} [Fintype E] (a b : E → V) (phi : V → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) : ℝ :=
  ((incidenceDarts a b x).image (fun d => |current a b phi d|)).max' (hx.image _)

theorem current_le_largestCurrent {V E : Type*} [Fintype E] (a b : E → V)
    (phi : V → ℝ) (x : V) (hx : (incidenceDarts a b x).Nonempty)
    (d : Dart E) (hd : tail a b d = x) : |current a b phi d| ≤ largestCurrent a b phi x hx := by
  unfold largestCurrent
  exact Finset.le_max' ((incidenceDarts a b x).image (fun z => |current a b phi z|))
    |current a b phi d| (Finset.mem_image.mpr ⟨d,(mem_incidenceDarts a b x d).mpr hd,rfl⟩)

theorem largestCurrent_nonneg {V E : Type*} [Fintype E] (a b : E → V)
    (phi : V → ℝ) (x : V) (hx : (incidenceDarts a b x).Nonempty) : 0 ≤ largestCurrent a b phi x hx := by
  have hex := hx
  obtain ⟨d,hd⟩ := hex
  exact (abs_nonneg _).trans (current_le_largestCurrent a b phi x hx d ((mem_incidenceDarts a b x d).mp hd))

/-- The free vertex's original clockwise successor sees exactly the right face of its current dart. -/
theorem free_leftFace_next {V E : Type*} {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (x : V)
    (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (d : Dart E) (hd : tail a b d = x) :
    arcLeftFace R da db (.inl (R.next d)) = arcRightFace R da db (.inl d) := by
  have hda : d ≠ da := by intro h; subst d; exact hx0 (hd.symm.trans ha)
  have hdb : d ≠ db := by intro h; subst d; exact hx1 (hd.symm.trans hb)
  rw [← insertArcRotation_other R da db d hda hdb]
  exact arcLeftFace_next R da db (.inl d)

/-- All original outgoing left-face values lie between the actual extrema. -/
theorem incident_left_bounds {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (da db : Dart E) (psi : ArcFace R da db → ℝ) (x : V)
    (hx : (incidenceDarts a b x).Nonempty) (d : Dart E) (hd : tail a b d = x) :
    streamMin R da db psi x hx ≤ psi (arcLeftFace R da db (.inl d)) ∧
      psi (arcLeftFace R da db (.inl d)) ≤ streamMax R da db psi x hx := by
  have hm : psi (arcLeftFace R da db (.inl d)) ∈ incidentHeights R da db psi x :=
    Finset.mem_image.mpr ⟨d,(mem_incidenceDarts a b x d).mpr hd,rfl⟩
  exact ⟨Finset.min'_le _ _ hm,Finset.le_max' _ _ hm⟩

/-- At a free vertex, both adjacent faces at every incidence belong to the same extrema carrier. -/
theorem incident_right_bounds {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (psi : ArcFace R da db → ℝ) (x : V)
    (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty)
    (d : Dart E) (hd : tail a b d = x) :
    streamMin R da db psi x hx ≤ psi (arcRightFace R da db (.inl d)) ∧
      psi (arcRightFace R da db (.inl d)) ≤ streamMax R da db psi x hx := by
  rw [← free_leftFace_next R alpha beta da db ha hb x hx0 hx1 d hd]
  exact incident_left_bounds R da db psi x hx (R.next d) ((R.tail_next d).trans hd)

/-- Literal copy counting yields degree times the maximum current. -/
theorem sum_incident_current_le {V E : Type*} [Fintype E] (a b : E → V)
    (phi : V → ℝ) (x : V) (hx : (incidenceDarts a b x).Nonempty) :
    (∑ d ∈ incidenceDarts a b x, |current a b phi d|) ≤ degree a b x*largestCurrent a b phi x hx := by
  calc
    _ ≤ ∑ _d ∈ incidenceDarts a b x, largestCurrent a b phi x hx :=
      Finset.sum_le_sum (fun d hd => current_le_largestCurrent a b phi x hx d ((mem_incidenceDarts a b x d).mp hd))
    _ = degree a b x*largestCurrent a b phi x hx := by
      rw [Finset.sum_const, nsmul_eq_mul,incidenceDarts_card,incidenceCount_eq_degree]

end FiniteAvalanches.Electrical.Plane
