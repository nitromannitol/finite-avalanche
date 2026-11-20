import FiniteAvalanches.Support.Plane.ArcClosingPath

/-!
# Upper bounds for nested loops

A nested family of loops of a path has an upper loop. This is a compactness
step in the loop-deletion proof of arcwise connectedness; see J. Brazas,
*Constructing arcs from paths using Zorn's Lemma*, Lemma 3,
https://arxiv.org/abs/2207.07242.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A nonempty nested family of subloops of a path is contained in another
subloop. -/
theorem exists_upper_subloop_of_nested {X : Type*} [TopologicalSpace X] [T2Space X]
    {x y : X} (p : Path x y) (S : Set (unitInterval × unitInterval))
    (hne : S.Nonempty)
    (hloop : ∀ v ∈ S, v.1 ≤ v.2 ∧ p v.1 = p v.2)
    (hchain : ∀ v ∈ S, ∀ w ∈ S,
      (v.1 ≤ w.1 ∧ w.2 ≤ v.2) ∨ (w.1 ≤ v.1 ∧ v.2 ≤ w.2)) :
    ∃ a b : unitInterval, a ≤ b ∧ p a = p b ∧
      ∀ v ∈ S, a ≤ v.1 ∧ v.2 ≤ b := by
  let T := closure S
  have hT : IsCompact T := isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ T)
  have hTne : T.Nonempty := hne.mono subset_closure
  have horder : ∀ v ∈ T, v.1 ≤ v.2 := by
    apply closure_minimal _ (isClosed_le continuous_fst continuous_snd)
    intro v hv
    exact (hloop v hv).1
  have heq : ∀ v ∈ T, p v.1 = p v.2 := by
    apply closure_minimal _ (isClosed_eq (p.continuous.comp continuous_fst)
      (p.continuous.comp continuous_snd))
    intro v hv
    exact (hloop v hv).2
  let len : unitInterval × unitInterval → ℝ := fun v => v.2.val - v.1.val
  have hlen : Continuous len :=
    (continuous_subtype_val.comp continuous_snd).sub (continuous_subtype_val.comp continuous_fst)
  obtain ⟨v, hvT, hvmax⟩ := hT.exists_isMaxOn hTne hlen.continuousOn
  refine ⟨v.1, v.2, horder v hvT, heq v hvT, ?_⟩
  intro w hw
  let C : Set (unitInterval × unitInterval) :=
    {z | z.1 ≤ w.1 ∧ w.2 ≤ z.2} ∪ {z | w.1 ≤ z.1 ∧ z.2 ≤ w.2}
  have hCclosed : IsClosed C := by
    apply IsClosed.union
    · exact (isClosed_le continuous_fst continuous_const).inter
        (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd))
    · exact (isClosed_le continuous_const continuous_fst).inter
        (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const)
  have hSC : S ⊆ C := by
    intro z hz
    exact hchain z hz w hw
  have hvC : v ∈ C := closure_minimal hSC hCclosed hvT
  rcases hvC with hvw | hwv
  · exact hvw
  · have hm : len w ≤ len v := hvmax (subset_closure hw)
    have hleft : (w.1 : ℝ) ≤ v.1 := hwv.1
    have hright : (v.2 : ℝ) ≤ w.2 := hwv.2
    have ha : (v.1 : ℝ) ≤ w.1 := by dsimp [len] at hm; linarith
    have hb : (w.2 : ℝ) ≤ v.2 := by dsimp [len] at hm; linarith
    exact ⟨ha, hb⟩

/-- Every subloop is contained in an inclusion-maximal subloop. -/
theorem exists_maximal_subloop {X : Type*} [TopologicalSpace X] [T2Space X]
    {x y : X} (p : Path x y) {a b : unitInterval} (hab : a ≤ b) (hp : p a = p b) :
    ∃ u v : unitInterval, u ≤ v ∧ u ≤ a ∧ b ≤ v ∧ p u = p v ∧
      ∀ u' v' : unitInterval, u' ≤ u → v ≤ v' → p u' = p v' → u' = u ∧ v' = v := by
  let T : Set (unitInterval × unitInterval) :=
    {z | z.1 ≤ a ∧ b ≤ z.2 ∧ p z.1 = p z.2}
  have hTclosed : IsClosed T := by
    apply IsClosed.inter (isClosed_le continuous_fst continuous_const)
    apply IsClosed.inter
    · exact isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)
    · exact isClosed_eq (p.continuous.comp continuous_fst) (p.continuous.comp continuous_snd)
  have hT : IsCompact T := isCompact_univ.of_isClosed_subset hTclosed (subset_univ T)
  have hTne : T.Nonempty := ⟨(a, b), le_rfl, le_rfl, hp⟩
  let len : unitInterval × unitInterval → ℝ := fun v => v.2.val - v.1.val
  have hlen : Continuous len :=
    (continuous_subtype_val.comp continuous_snd).sub (continuous_subtype_val.comp continuous_fst)
  obtain ⟨z, hz, hzmax⟩ := hT.exists_isMaxOn hTne hlen.continuousOn
  refine ⟨z.1, z.2, hz.1.trans (hab.trans hz.2.1), hz.1, hz.2.1, hz.2.2, ?_⟩
  intro u v hu hv huv
  have hmem : (u, v) ∈ T := ⟨le_trans hu hz.1, le_trans hz.2.1 hv, huv⟩
  have hmax : len (u, v) ≤ len z := hzmax hmem
  have hleft : (u : ℝ) ≤ z.1 := hu
  have hright : (z.2 : ℝ) ≤ v := hv
  have hrevleft : (z.1 : ℝ) ≤ u := by dsimp [len] at hmax; linarith
  have hrevright : (v : ℝ) ≤ z.2 := by dsimp [len] at hmax; linarith
  exact ⟨Subtype.ext (le_antisymm hleft hrevleft),
    Subtype.ext (le_antisymm hrevright hright)⟩

end FiniteAvalanches.Electrical.StatementGeometry
