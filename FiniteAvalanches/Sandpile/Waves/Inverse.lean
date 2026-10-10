import FiniteAvalanches.Sandpile.Waves.Punctured

/-! The fired set is recovered from the actual output's largest forbidden set.
This proves the finite punctured wave permutation without a group-law input. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- The source-minus-one largest forbidden set of the literal punctured field. -/
def core {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) : Finset Site2 :=
  forbiddenCore (boxSites N) (wiredHeight (-1) h)

theorem source_mem_wave {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    FiniteWired.site o ∈ (waveCounts h).support := by
  rw [Finsupp.mem_support_iff, wave_counts_source]
  norm_num

theorem wave_set_forbidden {N : ℕ} {o : FiniteWired.Active N} (h : OffField N o) :
    forbidden (wiredHeight (-1) (waveOutput h)) (waveCounts h).support := by
  refine ⟨⟨FiniteWired.site o, source_mem_wave h⟩, ?_⟩
  intro x hx
  by_cases hxo : x = FiniteWired.site o
  · subst x
    rw [wired_height_site, active_height_source]
    have hn : 0 ≤ (degree (waveCounts h).support (FiniteWired.site o) : ℤ) := Nat.cast_nonneg _
    omega
  · rw [wired_output_height h (wave_counts_support_subset h hx) hxo, waveHeight,
      lap_counts_eq_degree (wave_counts_le_one h)]
    simp only [hx, if_true, mul_one]
    have hh := wired_height_le_three h (wave_counts_support_subset h hx) hxo
    omega

theorem forbidden_output_subset_wave {N : ℕ} {o : FiniteWired.Active N}
    {h : OffField N o} (ha : punctured_allowed h) {H : Finset Site2}
    (hH : H ⊆ boxSites N) (hf : forbidden (wiredHeight (-1) (waveOutput h)) H) :
    H ⊆ (waveCounts h).support := by
  by_contra hn
  have hne : (H \ (waveCounts h).support).Nonempty := by
    simpa only [Finset.sdiff_nonempty] using hn
  have hsub : H \ (waveCounts h).support ⊆ (boxSites N).erase (FiniteWired.site o) := by
    intro x hx
    obtain ⟨hxH, hxW⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_erase.mpr ⟨fun he => hxW (he ▸ source_mem_wave h), hH hxH⟩
  apply ha _ hsub
  refine ⟨hne, ?_⟩
  intro x hx
  obtain ⟨hxH, hxW⟩ := Finset.mem_sdiff.mp hx
  have hxo : x ≠ FiniteWired.site o := fun he => hxW (he ▸ source_mem_wave h)
  have hh := hf.2 x hxH
  rw [wired_output_height h (hH hxH) hxo, waveHeight,
    lap_counts_eq_degree (wave_counts_le_one h)] at hh
  simp only [hxW, if_false, mul_zero, sub_zero] at hh
  have hd : (degree H x : ℤ) ≤ (degree (H \ (waveCounts h).support) x : ℤ) +
      (degree (waveCounts h).support x : ℤ) := by
    exact_mod_cast degree_le_sdiff_add H (waveCounts h).support x
  rw [wired_height_off (-1) 4 h hxo]
  omega

/-- The first assertion of `fv:inverse-waves`, for the actual legal wave. -/
theorem wave_support_eq_core_output {N : ℕ} {o : FiniteWired.Active N}
    {h : OffField N o} (ha : punctured_allowed h) :
    (waveCounts h).support = core (waveOutput h) := by
  apply Finset.Subset.antisymm
  · exact forbidden_subset_core (wave_counts_support_subset h) (wave_set_forbidden h)
  · intro x hx
    obtain ⟨_, H, hH, hf, hxH⟩ := Finset.mem_filter.mp hx
    exact forbidden_output_subset_wave ha hH hf hxH

theorem counts_eq_of_support_eq {u v : Counts} (hu : ∀ x, u x ≤ 1)
    (hv : ∀ x, v x ≤ 1) (hs : u.support = v.support) : u = v := by
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ u.support
  · have hn := Finsupp.mem_support_iff.mp hx
    have hvn := Finsupp.mem_support_iff.mp (hs ▸ hx)
    have hu1 := hu x
    have hv1 := hv x
    omega
  · have hz := Finsupp.notMem_support_iff.mp hx
    have hz' := Finsupp.notMem_support_iff.mp (hs ▸ hx)
    omega

theorem forward_injective {N : ℕ} {o : FiniteWired.Active N} :
    Function.Injective (@forward N o) := by
  intro h g he
  have hout : waveOutput h.val = waveOutput g.val := congrArg Subtype.val he
  have hc : waveCounts h.val = waveCounts g.val := by
    apply counts_eq_of_support_eq (wave_counts_le_one h.val) (wave_counts_le_one g.val)
    rw [wave_support_eq_core_output h.property, wave_support_eq_core_output g.property, hout]
  apply Subtype.ext
  funext x
  apply Fin.ext
  have hh := wave_output_height h.val x
  have hg := wave_output_height g.val x
  have hp := congrArg (fun f : OffField N o => ((f x).val : ℤ)) hout
  simp only [waveHeight, wired_height_site, active_height_off] at hh hg
  rw [hc] at hh
  have heq : ((h.val x).val : ℤ) = ((g.val x).val : ℤ) := by omega
  exact_mod_cast heq

/-- The actual finite punctured-wave permutation. -/
def waveEquiv {N : ℕ} {o : FiniteWired.Active N} : Punctured N o ≃ Punctured N o :=
  Equiv.ofBijective forward (Finite.injective_iff_bijective.mp forward_injective)

/-- The literal inverse of the now-proved bijection. -/
def inverse {N : ℕ} {o : FiniteWired.Active N} : Punctured N o → Punctured N o :=
  waveEquiv.symm

theorem forward_inverse {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) :
    forward (inverse h) = h := waveEquiv.apply_symm_apply h

theorem inverse_forward {N : ℕ} {o : FiniteWired.Active N} (h : Punctured N o) :
    inverse (forward h) = h := waveEquiv.symm_apply_apply h

end
end FiniteAvalanches.Sandpile.Waves
