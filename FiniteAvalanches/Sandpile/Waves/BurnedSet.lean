import FiniteAvalanches.Sandpile.Components.Restriction
import FiniteAvalanches.Sandpile.Waves.HeldBurning
import FiniteAvalanches.Sandpile.Waves.Inverse

/-! Burning inside a component while holding its lattice boundary gives part of the next wave. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Components
open scoped Classical
noncomputable section

/-- Nonsource vertices with a neighbor outside the specified component. -/
def heldBoundary {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) : Finset Site2 :=
  (C.val.erase (FiniteWired.site o)).filter fun x => degree C.val x < 4

/-- The burned vertices, including the source, of the actual held burn in C. -/
def heldInterior {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o)
    (C : ComponentShape o) : Finset Site2 :=
  C.val \ heldBurning (wiredHeight 4 h) (heldBoundary C) (C.val.erase (FiniteWired.site o))
    (Finset.filter_subset _ _)

/-- Every interior vertex burned from the source belongs to the actual next wave. -/
theorem held_interior_subset_wave {N : ℕ} {o : FiniteWired.Active N}
    (h : OffField N o) (C : ComponentShape o) :
    heldInterior h C ⊆ (waveCounts h).support := by
  let W := (waveCounts h).support
  let D := ((C.val.erase (FiniteWired.site o)) \ W) ∪ heldBoundary C
  have hDC : D ⊆ C.val.erase (FiniteWired.site o) :=
    Finset.union_subset (Finset.sdiff_subset) (Finset.filter_subset _ _)
  have hclosed : held_closed (wiredHeight 4 h) (heldBoundary C) D := by
    refine ⟨Finset.subset_union_right, ?_⟩
    intro x hx hxb
    obtain ⟨hxC, hxW⟩ := Finset.mem_sdiff.mp
      ((Finset.mem_union.mp hx).resolve_right hxb)
    obtain ⟨hxo, hxC⟩ := Finset.mem_erase.mp hxC
    have hd : degree C.val x = 4 := by
      have he : ¬degree C.val x < 4 := by
        intro he
        exact hxb (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxo, hxC⟩, he⟩)
      have hb := degree_le_four C.val x
      omega
    have hstable : waveHeight h x < 4 := by
      have he := wired_output_height h (C.property.1 hxC) hxo
      have hb := wired_height_le_three (waveOutput h) (C.property.1 hxC) hxo
      rw [wired_height_off (-1) 4 (waveOutput h) hxo] at he
      omega
    have hheight : waveHeight h x = wiredHeight 4 h x + (degree W x : ℤ) := by
      have hn : x ∉ (waveCounts h).support := hxW
      simp only [waveHeight, lap_counts_eq_degree (wave_counts_le_one h),
        if_neg hn, mul_zero, sub_zero]
      rfl
    have hdegree : (4 : ℤ) ≤ (degree D x : ℤ) + (degree W x : ℤ) := by
      have h1 := degree_le_sdiff_add C.val W x
      have hsub : C.val \ W ⊆ D := by
        intro y hy
        obtain ⟨hyC, hyW⟩ := Finset.mem_sdiff.mp hy
        apply Finset.mem_union_left
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr
          ⟨fun he => hyW (he ▸ source_mem_wave h), hyC⟩, hyW⟩
      have h2 := degree_mono hsub x
      rw [hd] at h1
      exact_mod_cast (show 4 ≤ degree D x + degree W x by omega)
    omega
  have hfinal := (held_burning_largest (wiredHeight 4 h) (heldBoundary C)
    (C.val.erase (FiniteWired.site o)) (Finset.filter_subset _ _)).2.2 D hDC hclosed
  intro x hx
  obtain ⟨hxC, hxR⟩ := Finset.mem_sdiff.mp hx
  by_cases hxo : x = FiniteWired.site o
  · exact hxo ▸ source_mem_wave h
  · by_contra hxW
    apply hxR
    apply hfinal
    apply Finset.mem_union_left
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxo, hxC⟩, hxW⟩

/-- In inverse-wave notation the same burned set lies in the following forward output core. -/
theorem held_interior_subset_core_forward {N : ℕ} {o : FiniteWired.Active N}
    (g : Punctured N o) (C : ComponentShape o) :
    heldInterior g.val C ⊆ core (forward g).val := by
  change heldInterior g.val C ⊆ core (waveOutput g.val)
  rw [← wave_support_eq_core_output g.property]
  exact held_interior_subset_wave g.val C

/-- Reindexing by the actual wave permutation puts the transition in forward time. -/
theorem sum_inverse_transitions_eq_forward {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset Site2) :
    (∑ h : Punctured N o,
      (if ¬S ⊆ core h.val ∧ S ⊆ core (inverse h).val then 1 else 0 : ℝ)) =
      ∑ g : Punctured N o,
        (if S ⊆ core g.val ∧ ¬S ⊆ core (forward g).val then 1 else 0 : ℝ) := by
  classical
  let q : Punctured N o → ℝ := fun h =>
    if ¬S ⊆ core h.val ∧ S ⊆ core (inverse h).val then 1 else 0
  calc
    _ = ∑ g : Punctured N o, q (forward g) := (waveEquiv.sum_comp q).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      change (if ¬S ⊆ core (forward g).val ∧ S ⊆ core (inverse (forward g)).val
        then 1 else 0 : ℝ) = _
      rw [inverse_forward]
      simp only [and_comm]

/-- The transition count is bounded before any conditioning on the transition event. -/
theorem sum_inverse_transitions_le_held_interior {N : ℕ} (o : FiniteWired.Active N)
    (S : Finset Site2) :
    (∑ h : Punctured N o,
      (if ¬S ⊆ core h.val ∧ S ⊆ core (inverse h).val then 1 else 0 : ℝ)) ≤
      ∑ g : Punctured N o,
        (if S ⊆ core g.val ∧ ¬S ⊆ heldInterior g.val (coreShape g.val)
          then 1 else 0 : ℝ) := by
  classical
  rw [sum_inverse_transitions_eq_forward]
  apply Finset.sum_le_sum
  intro g _
  by_cases hg : S ⊆ core g.val ∧ ¬S ⊆ core (forward g).val
  · rw [if_pos hg]
    have hh : S ⊆ core g.val ∧ ¬S ⊆ heldInterior g.val (coreShape g.val) :=
      ⟨hg.1, fun h => hg.2 (h.trans (held_interior_subset_core_forward g _))⟩
    rw [if_pos hh]
  · rw [if_neg hg]
    positivity

end
end FiniteAvalanches.Sandpile.Waves
