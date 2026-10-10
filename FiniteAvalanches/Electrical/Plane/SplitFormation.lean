import FiniteAvalanches.Electrical.Plane.BoundarySplit

/-! Actual ordered split graph formation, copied free degrees and nonempty split terminals. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

theorem split_degree_inl {V E : Type*} [Fintype E] (a b : E → V)
    (alpha : V) (side : E → Bool) (x : {x : V // x ≠ alpha}) :
    degree (fun e => splitEndpoint alpha side (a e) e)
      (fun e => splitEndpoint alpha side (b e) e) (.inl x) = degree a b x.val := by
  simp only [degree,splitEndpoint_eq_inl]

/-- Positivity on all actual alpha incidences gives positivity of the actual ordered current sequence. -/
theorem alphaCurrentSequence_pos {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ)
    (hpos : ∀ z : Dart E, tail a b z = alpha → 0 < phi (head a b z)) :
    ∀ i, 0 < alphaCurrentSequence R alpha beta hne da db ha hb phi i :=
  fun i => hpos _ (alphaEnumeration R alpha beta hne da db ha hb i).property

/-- The two original copies adjacent to a proper split really are distinct. -/
theorem adjacent_alpha_copies_ne {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (he : ∀ e, a e ≠ b e)
    (j0 j1 : Fin (incidenceCount a b alpha)) (hj : j0.val+1 = j1.val) :
    (alphaEnumeration R alpha beta hne da db ha hb j0).val.1 ≠
      (alphaEnumeration R alpha beta hne da db ha hb j1).val.1 := by
  intro h
  have hinc := incidence_copy_injective alpha he h
  have hij := (alphaEnumeration R alpha beta hne da db ha hb).injective hinc
  have hval := congrArg Fin.val hij
  omega

/-- Each split terminal has a genuine original incident copy, without adding or identifying copies. -/
theorem ordered_split_terminals_incident {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (he : ∀ e, a e ≠ b e)
    (j0 j1 : Fin (incidenceCount a b alpha)) (hj : j0.val+1 = j1.val) :
    let side := orderedSide R alpha beta hne da db ha hb j1.val
    (∃ e, splitEndpoint alpha side (a e) e = .inr false ∨ splitEndpoint alpha side (b e) e = .inr false) ∧
    (∃ e, splitEndpoint alpha side (a e) e = .inr true ∨ splitEndpoint alpha side (b e) e = .inr true) := by
  intro side
  have hendpoint (i : Fin (incidenceCount a b alpha)) (k : Bool)
      (hk : side (alphaEnumeration R alpha beta hne da db ha hb i).val.1 = k) :
      ∃ e, splitEndpoint alpha side (a e) e = .inr k ∨ splitEndpoint alpha side (b e) e = .inr k := by
    let z := (alphaEnumeration R alpha beta hne da db ha hb i).val
    have hz : tail a b z = alpha := (alphaEnumeration R alpha beta hne da db ha hb i).property
    have hv : splitEndpoint alpha side (tail a b z) z.1 = .inr k := by
      rw [hz]
      unfold splitEndpoint
      rw [dif_pos rfl]
      exact congrArg Sum.inr hk
    refine ⟨z.1,?_⟩
    rcases z with ⟨e,c⟩
    cases c with
    | false => exact Or.inl hv
    | true => exact Or.inr hv
  constructor
  · apply hendpoint j0 false
    apply Bool.eq_false_of_not_eq_true
    intro h
    have hle := (orderedSide_enumeration R alpha beta hne da db ha hb he j1.val j0).mp h
    omega
  · exact hendpoint j1 true ((orderedSide_enumeration R alpha beta hne da db ha hb he j1.val j1).mpr le_rfl)

end FiniteAvalanches.Electrical.Plane
