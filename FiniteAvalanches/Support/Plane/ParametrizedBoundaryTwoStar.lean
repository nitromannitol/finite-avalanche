import FiniteAvalanches.Support.Plane.RetainedTailReparam

/-!
# Parametrized pairs of boundary arms

Two disjoint boundary accesses admit separated rooted arms with their original
terminal parametrizations preserved.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two disjoint boundary accesses admit separated arms with exact terminal
speed and avoidance of a prescribed finite set. -/
theorem exists_two_boundary_arms_with_parametrized_tails
    {U S : Set (ℝ × ℝ)} {a b c d : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Path a b) (q : Path c d) (hp : Function.Injective p)
    (hq : Function.Injective q) (hd : Disjoint (range p) (range q))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hb : b ∉ U) (hd' : d ∉ U)
    (hS : S.Finite) (hpS : Disjoint (range p) S) (hqS : Disjoint (range q) S) :
    ∃ r ∈ U, ∃ (v : Path r b) (w : Path r d),
      Function.Injective v ∧ Function.Injective w ∧
      Disjoint (range v) S ∧ Disjoint (range w) S ∧
      range v ∩ range w = {r} ∧
      range v ∩ Uᶜ = {b} ∧ range w ∩ Uᶜ = {d} ∧
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          v t = p ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) ∧
      (∃ u : unitInterval, u ≠ 1 ∧
        ∀ (t : unitInterval) (ht : ((u : ℝ) + 1) / 2 ≤ (t : ℝ)),
          w t = q ⟨2 * (t : ℝ) - 1, by
            constructor
            · have := u.property.1
              linarith
            · linarith [t.property.2]⟩) := by
  obtain ⟨r, hr, v, w, hv, hw, hvS, hwS, hinter, hvU, hwU,
    ⟨tp, htp, hptail⟩, ⟨tq, htq, hqtail⟩⟩ :=
    exists_two_boundary_arms_with_tails hU hconn p q hp hq hd hpU hqU hb hd' hS hpS hqS
  obtain ⟨v', hv', hvsub, u, hu, huspeed⟩ :=
    exists_path_with_parametrized_retained_tail v p hv hp htp hptail
  obtain ⟨w', hw', hwsub, z, hz, hzspeed⟩ :=
    exists_path_with_parametrized_retained_tail w q hw hq htq hqtail
  refine ⟨r, hr, v', w', hv', hw', hvS.mono_left hvsub, hwS.mono_left hwsub, ?_, ?_, ?_,
    ⟨u, hu, huspeed⟩, ⟨z, hz, hzspeed⟩⟩
  · apply subset_antisymm
    · exact (inter_subset_inter hvsub hwsub).trans hinter.le
    · exact singleton_subset_iff.mpr ⟨v'.source_mem_range, w'.source_mem_range⟩
  · apply subset_antisymm
    · exact (inter_subset_inter_left _ hvsub).trans hvU.le
    · exact singleton_subset_iff.mpr ⟨v'.target_mem_range, hb⟩
  · apply subset_antisymm
    · exact (inter_subset_inter_left _ hwsub).trans hwU.le
    · exact singleton_subset_iff.mpr ⟨w'.target_mem_range, hd'⟩

end FiniteAvalanches.Electrical.StatementGeometry
