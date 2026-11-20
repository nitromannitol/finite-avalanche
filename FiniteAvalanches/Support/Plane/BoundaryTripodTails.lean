import FiniteAvalanches.Support.Plane.TerminalTailSeparation
import FiniteAvalanches.Support.Plane.RetainedTailReparam

/-!
# Tripods with prescribed endpoint tails

First-meeting tripods can retain terminal subarcs at all three endpoints.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A first-meeting tripod can be reparametrized to retain three prescribed
terminal path speeds. -/
theorem exists_tripod_of_path_first_hit_with_tails
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b c d xa xb xc : X} (p : Path a b) (q : Path c d)
    (alpha : Path xa a) (beta : Path xb b) (gamma : Path xc c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (ha : Function.Injective alpha) (hb : Function.Injective beta)
    (hc : Function.Injective gamma) (hcP : c ∉ range p) (hd : d ∈ range p)
    (haQ : a ∉ range q) (hbQ : b ∉ range q)
    (htailA : ∃ t : unitInterval, t ≠ 1 ∧ range (alpha.subpath t 1) ⊆ range p)
    (htailB : ∃ t : unitInterval, t ≠ 1 ∧ range (beta.subpath t 1) ⊆ range p)
    (htailC : ∃ t : unitInterval, t ≠ 1 ∧ range (gamma.subpath t 1) ⊆ range q) :
    ∃ (r : X) (u : Path r a) (v : Path r b) (w : Path r c),
      Function.Injective u ∧ Function.Injective v ∧ Function.Injective w ∧
      range u ⊆ range p ∧ range v ⊆ range p ∧ range w ⊆ range q ∧
      range u ∩ range v = {r} ∧ range u ∩ range w = {r} ∧
      range v ∩ range w = {r} ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (s : unitInterval)
        (hs : ((t : ℝ) + 1) / 2 ≤ (s : ℝ)),
        u s = alpha ⟨2 * (s : ℝ) - 1, by constructor <;> linarith [t.property.1, s.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (s : unitInterval)
        (hs : ((t : ℝ) + 1) / 2 ≤ (s : ℝ)),
        v s = beta ⟨2 * (s : ℝ) - 1, by constructor <;> linarith [t.property.1, s.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (s : unitInterval)
        (hs : ((t : ℝ) + 1) / 2 ≤ (s : ℝ)),
        w s = gamma ⟨2 * (s : ℝ) - 1, by constructor <;> linarith [t.property.1, s.property.2]⟩) := by
  obtain ⟨r, u, v, w, hu, hv, hw, hup, hvp, hwq, huv, huw, hvw, hpcover, T, hT, hTw⟩ :=
    exists_tripod_of_path_first_hit p q hp hq hcP hd haQ hbQ
  have hra : r ≠ a := fun h => haQ (h ▸ hwq w.source_mem_range)
  have hrb : r ≠ b := fun h => hbQ (h ▸ hwq w.source_mem_range)
  have hav : a ∉ range v := by
    intro h
    have h' : a ∈ range u ∩ range v := ⟨u.target_mem_range, h⟩
    rw [huv] at h'
    exact hra (mem_singleton_iff.mp h').symm
  have hbu : b ∉ range u := by
    intro h
    have h' : b ∈ range u ∩ range v := ⟨h, v.target_mem_range⟩
    rw [huv] at h'
    exact hrb (mem_singleton_iff.mp h').symm
  obtain ⟨ta, hta, htaP⟩ := htailA
  obtain ⟨tb, htb, htbP⟩ := htailB
  obtain ⟨tc, htc, htcQ⟩ := htailC
  obtain ⟨ta', hta', htaU⟩ := exists_terminal_subpath_subset_of_union_closed alpha (A := range u)
    (isCompact_range v.continuous).isClosed hav hta (by simpa only [hpcover] using htaP)
  obtain ⟨tb', htb', htbV⟩ := exists_terminal_subpath_subset_of_union_closed beta (A := range v)
    (isCompact_range u.continuous).isClosed hbu htb (by
      simpa only [hpcover, union_comm] using htbP)
  have hqrev : Function.Injective q.symm := hq.comp unitInterval.symm_involutive.injective
  obtain ⟨tc', htc', htcW⟩ := terminal_subpath_in_initial_reverse q.symm gamma hqrev htc hT (by
    simpa only [Path.symm_range] using htcQ)
  have htcW' : range (gamma.subpath tc' 1) ⊆ range w := by
    rw [Path.symm_symm, hTw] at htcW
    exact htcW
  obtain ⟨u', hu', hu'sub, ta'', hta'', hspeedA⟩ :=
    exists_path_with_parametrized_retained_tail u alpha hu ha hta' htaU
  obtain ⟨v', hv', hv'sub, tb'', htb'', hspeedB⟩ :=
    exists_path_with_parametrized_retained_tail v beta hv hb htb' htbV
  obtain ⟨w', hw', hw'sub, tc'', htc'', hspeedC⟩ :=
    exists_path_with_parametrized_retained_tail w gamma hw hc htc' htcW'
  have huv' : range u' ∩ range v' = {r} := by
    apply subset_antisymm
    · exact (inter_subset_inter hu'sub hv'sub).trans huv.le
    · exact singleton_subset_iff.mpr ⟨u'.source_mem_range, v'.source_mem_range⟩
  have huw' : range u' ∩ range w' = {r} := by
    apply subset_antisymm
    · exact (inter_subset_inter hu'sub hw'sub).trans huw.le
    · exact singleton_subset_iff.mpr ⟨u'.source_mem_range, w'.source_mem_range⟩
  have hvw' : range v' ∩ range w' = {r} := by
    apply subset_antisymm
    · exact (inter_subset_inter hv'sub hw'sub).trans hvw.le
    · exact singleton_subset_iff.mpr ⟨v'.source_mem_range, w'.source_mem_range⟩
  exact ⟨r, u', v', w', hu', hv', hw', hu'sub.trans hup, hv'sub.trans hvp,
    hw'sub.trans hwq, huv', huw', hvw', ⟨ta'', hta'', hspeedA⟩,
    ⟨tb'', htb'', hspeedB⟩, ⟨tc'', htc'', hspeedC⟩⟩

end FiniteAvalanches.Electrical.StatementGeometry
