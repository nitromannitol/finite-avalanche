import FiniteAvalanches.Electrical.Plane.Orbits
import FiniteAvalanches.Electrical.Plane.ArcCycles
import FiniteAvalanches.Electrical.Geometry.Charging

/-! Once-counted original alpha incidences between consecutive returns to the auxiliary dart. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped BigOperators Classical

/-- The actual outgoing incidence fiber, preserving the edge-copy index. -/
abbrev Incidences {V E : Type*} (a b : E → V) (x : V) := {d : Dart E // tail a b d = x}
noncomputable def incidenceCount {V E : Type*} [Fintype E] (a b : E → V) (x : V) : ℕ :=
  Fintype.card (Incidences a b x)

theorem incidenceCount_eq_degree {V E : Type*} [Fintype E] (a b : E → V) (x : V) :
    (incidenceCount a b x : ℝ) = FiniteAvalanches.Electrical.Geometry.degree a b x := by
  simp only [incidenceCount,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Fintype.sum_prod_type,Fintype.sum_bool,
    tail,Bool.false_eq_true,↓reduceIte]
  unfold FiniteAvalanches.Electrical.Geometry.degree
  apply Finset.sum_congr rfl
  intro e _
  by_cases ha : a e = x <;> by_cases hb : b e = x <;> norm_num [ha,hb]

/-- The augmented alpha orbit consists exactly of its original incidences and the one arc dart. -/
noncomputable def alphaOrbitEquiv {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) :
    (Incidences a b alpha ⊕ Unit) ≃
      {d : ArcDart E // (insertArcRotation R da db).SameCycle (.inr false) d} :=
  Equiv.ofBijective (fun z => match z with
    | .inl d => ⟨.inl d.val,(insertArcRotation_sameCycle_iff R alpha beta hne da db ha hb _ _).mpr d.property.symm⟩
    | .inr _ => ⟨.inr false,.refl _ _⟩) (by
    constructor
    · intro z w h
      have he := congrArg Subtype.val h
      cases z with
      | inl z => cases w with
        | inl w => exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective he))
        | inr w => cases he
      | inr z => cases w with
        | inl w => cases he
        | inr w => exact congrArg Sum.inr (Subsingleton.elim z w)
    · intro d
      have ht := (insertArcRotation_sameCycle_iff R alpha beta hne da db ha hb _ _).mp d.property
      cases he : d.val with
      | inl x =>
        have hx : tail a b x = alpha := by simpa only [he,arcTail] using ht.symm
        exact ⟨.inl ⟨x,hx⟩,Subtype.ext he.symm⟩
      | inr c => cases c with
        | false => exact ⟨.inr (),Subtype.ext he.symm⟩
        | true => exact (hne (by simpa only [he,arcTail] using ht)).elim)

theorem alpha_orbit_card {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) :
    (cyclePoints (insertArcRotation R da db) (.inr false)).card = incidenceCount a b alpha+1 := by
  have h1 := Fintype.card_congr (alphaOrbitEquiv R alpha beta hne da db ha hb)
  have h2 := Fintype.card_congr (orbitEquiv (insertArcRotation R da db) (.inr false))
  simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_fin] at h1 h2
  exact h2.trans h1.symm

/-- There is exactly one original incidence at each position 1,...,degree(alpha). -/
theorem existsUnique_alpha_position {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (i : Fin (incidenceCount a b alpha)) :
    ∃! d : Incidences a b alpha, .inl d.val = ((insertArcRotation R da db)^(i.val+1)) (.inr false) := by
  let T := insertArcRotation R da db
  let u : ArcDart E := .inr false
  have hc := alpha_orbit_card R alpha beta hne da db ha hb
  have hi : i.val+1 < (cyclePoints T u).card := by dsimp [T,u]; rw [hc]; omega
  have h0 : 0 < (cyclePoints T u).card := (cyclePoints_nonempty T u).card_pos
  have hp : T.SameCycle u ((T^(i.val+1)) u) := by
    simpa only [Equiv.Perm.sameCycle_pow_right] using Equiv.Perm.SameCycle.refl T u
  have ht := (insertArcRotation_sameCycle_iff R alpha beta hne da db ha hb _ _).mp hp
  cases he : ((T^(i.val+1)) u) with
  | inl d =>
    have hd : tail a b d = alpha := by simpa only [he,u,arcTail] using ht.symm
    refine ⟨⟨d,hd⟩,rfl,?_⟩
    intro d' h
    apply Subtype.ext
    exact Sum.inl_injective h
  | inr c => cases c with
    | false =>
      have hn := orbit_pow_inj T u hi h0 (show (T^(i.val+1)) u = (T^0) u from he)
      omega
    | true => exact (hne (by simpa only [he,u,arcTail] using ht)).elim

/-- The actual incidence in its unique position after the auxiliary alpha dart. -/
noncomputable def alphaDart {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (i : Fin (incidenceCount a b alpha)) :
    Incidences a b alpha := (existsUnique_alpha_position R alpha beta hne da db ha hb i).choose

theorem alphaDart_spec {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (i : Fin (incidenceCount a b alpha)) :
    .inl (alphaDart R alpha beta hne da db ha hb i).val =
      ((insertArcRotation R da db)^(i.val+1)) (.inr false) :=
  (existsUnique_alpha_position R alpha beta hne da db ha hb i).choose_spec.1

/-- Every original alpha incidence occurs once and only once, in the actual rotation order. -/
noncomputable def alphaEnumeration {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) :
    Fin (incidenceCount a b alpha) ≃ Incidences a b alpha :=
  Equiv.ofBijective (alphaDart R alpha beta hne da db ha hb) (by
    have hc := alpha_orbit_card R alpha beta hne da db ha hb
    constructor
    · intro i j h
      have hp := congrArg (fun d : Incidences a b alpha => Sum.inl d.val : Incidences a b alpha → ArcDart E) h
      rw [alphaDart_spec,alphaDart_spec] at hp
      have he := orbit_pow_inj (insertArcRotation R da db) (.inr false)
        (by rw [hc]; omega) (by rw [hc]; omega) hp
      apply Fin.ext
      omega
    · intro d
      have hd : (insertArcRotation R da db).SameCycle (.inr false) (.inl d.val) :=
        (insertArcRotation_sameCycle_iff R alpha beta hne da db ha hb (.inr false) (.inl d.val)).mpr d.property.symm
      obtain ⟨n,hn,he⟩ := (isCycleOn_cyclePoints (insertArcRotation R da db) (.inr false)).exists_pow_eq
        ((mem_cyclePoints _ _ _).mpr (.refl _ _)) ((mem_cyclePoints _ _ _).mpr hd)
      have hn0 : 0 < n := by
        by_contra h
        have h0 : n = 0 := by omega
        rw [h0,pow_zero,Equiv.Perm.one_apply] at he
        cases he
      let i : Fin (incidenceCount a b alpha) := ⟨n-1,by rw [hc] at hn; omega⟩
      refine ⟨i,?_⟩
      apply Subtype.ext
      apply Sum.inl_injective (β := Bool)
      rw [alphaDart_spec]
      have hi : i.val+1 = n := by dsimp [i]; omega
      rwa [hi])

@[simp] theorem alphaEnumeration_spec {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (i : Fin (incidenceCount a b alpha)) :
    .inl (alphaEnumeration R alpha beta hne da db ha hb i).val =
      ((insertArcRotation R da db)^(i.val+1)) (.inr false) :=
  alphaDart_spec R alpha beta hne da db ha hb i

end FiniteAvalanches.Electrical.Plane
