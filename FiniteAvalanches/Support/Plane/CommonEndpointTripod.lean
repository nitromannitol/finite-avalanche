import FiniteAvalanches.Support.Plane.TwoArcRerootTails

/-!
# Three arms with a shared endpoint

A path meeting a pair of arcs with common endpoints yields three separated
arms, with prescribed terminal parametrizations.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Attach a third access to two arcs with common endpoints at its first
meeting, preserving all three prescribed terminal speeds. -/
theorem exists_common_endpoint_tripod_of_first_hit
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {a b c d xa xb xc : X} (p q : Path a b) (h : Path c d)
    (alpha : Path xa b) (beta : Path xb b) (gamma : Path xc c)
    (hp : Function.Injective p) (hq : Function.Injective q) (hh : Function.Injective h)
    (ha : Function.Injective alpha) (hb : Function.Injective beta)
    (hc : Function.Injective gamma) (hpq : range p ∩ range q = {a, b})
    (hcK : c ∉ range p ∪ range q) (hdK : d ∈ range p ∪ range q)
    (hbH : b ∉ range h)
    (htailA : ∃ t : unitInterval, t ≠ 1 ∧ range (alpha.subpath t 1) ⊆ range p)
    (htailB : ∃ t : unitInterval, t ≠ 1 ∧ range (beta.subpath t 1) ⊆ range q)
    (htailC : ∃ t : unitInterval, t ≠ 1 ∧ range (gamma.subpath t 1) ⊆ range h) :
    ∃ (r : X) (v w : Path r b) (z : Path r c),
      Function.Injective v ∧ Function.Injective w ∧ Function.Injective z ∧
      range v ⊆ range p ∪ range q ∧ range w ⊆ range p ∪ range q ∧
      range z ⊆ range h ∧ range v ∩ range w = {r, b} ∧
      range v ∩ range z = {r} ∧ range w ∩ range z = {r} ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        v u = alpha ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        w u = beta ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        z u = gamma ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) := by
  have hK : IsClosed (range p ∪ range q) :=
    ((isCompact_range p.continuous).union (isCompact_range q.continuous)).isClosed
  obtain ⟨r, hr, path, hpath, hpathsub, hmeet, T, hT, hTpath⟩ :=
    exists_initial_path_first_hit_with_subpath h hh hK hcK hdK
  have hrb : r ≠ b := fun he => hbH (he ▸ hpathsub path.target_mem_range)
  obtain ⟨v, w, hv, hw, hvw, hvK, hwK, hvtail, hwtail⟩ :=
    exists_reroot_two_arcs_with_tails p q alpha beta hp hq ha hb hpq hr hrb htailA htailB
  have hrev : Function.Injective h.symm := hh.comp unitInterval.symm_involutive.injective
  obtain ⟨t, ht, htH⟩ := htailC
  obtain ⟨u, hu, huPath⟩ := terminal_subpath_in_initial_reverse h.symm gamma hrev ht hT (by
    simpa only [Path.symm_range] using htH)
  have huPath' : range (gamma.subpath u 1) ⊆ range path.symm := by
    rw [Path.symm_symm, hTpath] at huPath
    simpa only [Path.symm_range] using huPath
  have hpathrev : Function.Injective path.symm :=
    hpath.comp unitInterval.symm_involutive.injective
  obtain ⟨z, hz, hzsub, t', ht', hztail⟩ :=
    exists_path_with_parametrized_retained_tail path.symm gamma hpathrev hc hu huPath'
  have hzH : range z ⊆ range h := by
    exact hzsub.trans (by simpa only [Path.symm_range] using hpathsub)
  have hzK : range z ∩ (range p ∪ range q) ⊆ {r} := by
    exact (inter_subset_inter_left _ (hzsub.trans (by
      intro x hx
      simpa only [Path.symm_range] using hx))).trans hmeet.le
  have hvz : range v ∩ range z = {r} := by
    apply subset_antisymm
    · intro x hx
      exact hzK ⟨hx.2, hvK hx.1⟩
    · exact singleton_subset_iff.mpr ⟨v.source_mem_range, z.source_mem_range⟩
  have hwz : range w ∩ range z = {r} := by
    apply subset_antisymm
    · intro x hx
      exact hzK ⟨hx.2, hwK hx.1⟩
    · exact singleton_subset_iff.mpr ⟨w.source_mem_range, z.source_mem_range⟩
  exact ⟨r, v, w, z, hv, hw, hz, hvK, hwK, hzH, hvw, hvz, hwz,
    hvtail, hwtail, ⟨t', ht', hztail⟩⟩

end FiniteAvalanches.Electrical.StatementGeometry
