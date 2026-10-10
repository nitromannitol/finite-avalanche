import FiniteAvalanches.Electrical.Plane.FreeSegments
import FiniteAvalanches.Electrical.Plane.SplitFormation

/-! One simultaneous selection of genuine positive maximal original copies on the split carrier. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- The midpoint map remains on the original electrical segments throughout the split carrier. -/
noncomputable def splitMidpoint {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (psi : ArcFace R da db → ℝ)
    (v : SplitVertex alpha) : ℝ × ℝ :=
  vertexMidpoint R da db phi psi (collapse alpha v)
    (incidenceDarts_nonempty a b alpha beta hne hc (collapse alpha v))

/-- Positive maximizing copies exist first; a single simultaneous selection then leaves all
terminals and all zero-current free vertices unselected. -/
theorem exists_split_max_selection {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (d : ℝ) (hd : 1 ≤ d) (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree a b x ≤ d) :
    ∃ q : SplitVertex alpha → Option E,
      (∀ k, q (.inr k) = none) ∧
      (∀ x, x.val = beta → q (.inl x) = none) ∧
      ∀ x : {x : V // x ≠ alpha}, x.val ≠ beta →
        let hx := incidenceDarts_nonempty a b alpha beta hne hc x.val
        (q (.inl x) = none ↔ largestCurrent a b phi x.val hx = 0) ∧
        ∀ e, q (.inl x) = some e →
          (a e = x.val ∨ b e = x.val) ∧
          (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).side = largestCurrent a b phi x.val hx ∧
          0 < (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).side ∧
          vertexSegment R da db phi psi x.val hx ⊆
            ((incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).dilate (2*d+3) (by linarith)).carrier := by
  let hx := incidenceDarts_nonempty a b alpha beta hne hc
  have hex (x : {x : V // x ≠ alpha}) : ∃ o : Option E,
      (x.val = beta → o = none) ∧
      (x.val ≠ beta → (o = none ↔ largestCurrent a b phi x.val (hx x.val) = 0) ∧
        ∀ e, o = some e → (a e = x.val ∨ b e = x.val) ∧
          (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).side = largestCurrent a b phi x.val (hx x.val) ∧
          0 < (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).side ∧
          vertexSegment R da db phi psi x.val (hx x.val) ⊆
            ((incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).dilate (2*d+3) (by linarith)).carrier) := by
    by_cases hxb : x.val = beta
    · exact ⟨none,fun _ => rfl,fun h => (h hxb).elim⟩
    · by_cases hz : largestCurrent a b phi x.val (hx x.val) = 0
      · exact ⟨none,fun h => (hxb h).elim,fun _ => ⟨by simp [hz],by simp⟩⟩
      · have hpos : 0 < largestCurrent a b phi x.val (hx x.val) :=
          lt_of_le_of_ne (largestCurrent_nonneg a b phi x.val (hx x.val)) (Ne.symm hz)
        obtain ⟨e,he⟩ := exists_positive_max_square R alpha beta da db ha hb phi M psi hp
          x.val x.property hxb (hx x.val) d hd (hdeg x.val x.property hxb) hpos
        refine ⟨some e,fun h => (hxb h).elim,fun _ => ⟨by simp [hz],?_⟩⟩
        intro i hi
        cases Option.some.inj hi
        exact he
  choose o ho using hex
  let q : SplitVertex alpha → Option E := Sum.elim o (fun _ => none)
  exact ⟨q,fun _ => rfl,fun x h => (ho x).1 h,fun x h => (ho x).2 h⟩

end FiniteAvalanches.Electrical.Plane
