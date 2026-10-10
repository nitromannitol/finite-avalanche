import FiniteAvalanches.Sandpile.Translation

/-! Literal avalanche observables commute with every lattice translation. -/
namespace FiniteAvalanches.Sandpile
open LatticeProb LatticeProb.Sandpile FiniteAvalanches
open scoped Classical
noncomputable section

theorem siteRadius_sub (o z x : Site2) : siteRadius (o-z) x = siteRadius o (x+z) := by
  unfold siteRadius
  congr 1
  funext i
  congr 1
  simp only [Pi.sub_apply,Pi.add_apply]
  ring

theorem countsRadius_map_sub (w : List Site2) (o z : Site2) :
    countsRadius (o-z) (listCounts (w.map (fun x => x-z))) = countsRadius o (listCounts w) := by
  apply le_antisymm
  · apply (countsRadius_le_iff _ _ _).mpr
    intro x hx
    rw [siteRadius_sub]
    apply (countsRadius_le_iff o (listCounts w) _).mp le_rfl
    rwa [listCounts_map_sub] at hx
  · apply (countsRadius_le_iff _ _ _).mpr
    intro x hx
    have h := (countsRadius_le_iff (o-z) (listCounts (w.map (fun y => y-z))) _).mp le_rfl (x-z)
    have hp : 0 < listCounts (w.map (fun y => y-z)) (x-z) := by
      simpa only [listCounts_map_sub,sub_add_cancel] using hx
    simpa only [siteRadius_sub,sub_add_cancel] using h hp

/-- The entire legal stabilization, including its final stable field, translates. -/
theorem Stabilizes.map_sub {η : StableField} {o : Site2} {w : List Site2}
    (hw : Stabilizes η (oneGrain o) w) (z : Site2) :
    Stabilizes (translate z η) (oneGrain (o-z)) (w.map (fun x => x-z)) := by
  have hi : initial (translate z η) (oneGrain (o-z)) =
      fun x => initial η (oneGrain o) (x+z) := by
    funext x
    simp only [initial_oneGrain,translate,dirac,eq_sub_iff_add_eq]
  refine ⟨?_,?_⟩
  · rw [hi]
    exact hw.1.map_sub z
  · intro x
    rw [hi]
    have hc : (fun y => (listCounts (w.map (fun t => t-z)) y : ℤ)) =
        fun y => (listCounts w (y+z) : ℤ) := by
      funext y
      rw [listCounts_map_sub]
    rw [hc]
    rw [lap_translate (fun y => (listCounts w y : ℤ)) z x]
    exact hw.2 (x+z)

/-- This equivalence retains the nonstabilizing fields on both complete carriers. -/
theorem finiteStabilizable_translate (η : StableField) (o z : Site2) :
    FiniteStabilizable (translate z η) (o-z) ↔ FiniteStabilizable η o := by
  constructor
  · rintro ⟨w,hw⟩
    have h := hw.map_sub (-z)
    have he : translate (-z) (translate z η) = η := by
      funext x
      simp [translate,add_assoc]
    have ho : (o-z)-(-z) = o := by abel
    rw [he,ho] at h
    exact ⟨_,h⟩
  · rintro ⟨w,hw⟩
    exact ⟨_,hw.map_sub z⟩

theorem radius_translate (η : StableField) (o z : Site2) :
    radius (translate z η) (o-z) = radius η o := by
  by_cases h : FiniteStabilizable η o
  · obtain ⟨w,hw⟩ := h
    rw [radius_of_stabilizes (hw.map_sub z),radius_of_stabilizes hw,countsRadius_map_sub]
  · have h' : ¬FiniteStabilizable (translate z η) (o-z) :=
      fun h' => h ((finiteStabilizable_translate η o z).mp h')
    rw [(radius_eq_top_iff _ _).mpr h',(radius_eq_top_iff _ _).mpr h]

theorem totalTopplings_translate (η : StableField) (o z : Site2) :
    totalTopplings (translate z η) (o-z) = totalTopplings η o := by
  by_cases h : FiniteStabilizable η o
  · obtain ⟨w,hw⟩ := h
    rw [totalTopplings_of_stabilizes (hw.map_sub z),totalTopplings_of_stabilizes hw,List.length_map]
  · have h' : ¬FiniteStabilizable (translate z η) (o-z) :=
      fun h' => h ((finiteStabilizable_translate η o z).mp h')
    rw [(totalTopplings_eq_top_iff _ _).mpr h',(totalTopplings_eq_top_iff _ _).mpr h]

end
end FiniteAvalanches.Sandpile
