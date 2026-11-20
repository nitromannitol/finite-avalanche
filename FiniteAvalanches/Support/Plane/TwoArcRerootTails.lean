import FiniteAvalanches.Support.Plane.TerminalTailTransfer
import FiniteAvalanches.Support.Plane.RetainedTailReparam

/-!
# Rerooted arcs with prescribed endpoint tails

Two arcs can be rerooted while retaining independently prescribed terminal
parametrizations at their common endpoint.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Reroot two arcs at any point of their union, preserving terminal speeds
from the respective original arcs. -/
theorem exists_reroot_two_arcs_with_tails
    {X : Type*} [TopologicalSpace X] [T2Space X] {a b r xa xb : X}
    (p q : Path a b) (alpha : Path xa b) (beta : Path xb b)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (ha : Function.Injective alpha) (hb : Function.Injective beta)
    (hpq : range p ∩ range q = {a, b}) (hr : r ∈ range p ∪ range q) (hrb : r ≠ b)
    (htailA : ∃ t : unitInterval, t ≠ 1 ∧ range (alpha.subpath t 1) ⊆ range p)
    (htailB : ∃ t : unitInterval, t ≠ 1 ∧ range (beta.subpath t 1) ⊆ range q) :
    ∃ (v w : Path r b), Function.Injective v ∧ Function.Injective w ∧
      range v ∩ range w = {r, b} ∧
      range v ⊆ range p ∪ range q ∧ range w ⊆ range p ∪ range q ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        v u = alpha ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        w u = beta ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) := by
  obtain ⟨ta, hta, htaP⟩ := htailA
  obtain ⟨tb, htb, htbQ⟩ := htailB
  have hex : ∃ (v w : Path r b), Function.Injective v ∧ Function.Injective w ∧
      range v ∩ range w = {r, b} ∧
      range v ⊆ range p ∪ range q ∧ range w ⊆ range p ∪ range q ∧
      (∃ t : unitInterval, t ≠ 1 ∧ range (alpha.subpath t 1) ⊆ range v) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ range (beta.subpath t 1) ⊆ range w) := by
    rcases hr with hr | hr
    · obtain ⟨v, w, hv, hw, hvw, hcover, ⟨t, ht, htp⟩, hqW⟩ :=
        exists_reroot_two_arcs_of_mem_left p q hp hq hpq hr hrb
      obtain ⟨u, hu, huP⟩ := exists_terminal_subpath_subset_terminal_subpath
        p alpha hp hta ht htaP
      exact ⟨v, w, hv, hw, hvw, subset_union_left.trans hcover.le,
        subset_union_right.trans hcover.le, ⟨u, hu, huP.trans htp⟩,
        ⟨tb, htb, htbQ.trans hqW⟩⟩
    · have hqp : range q ∩ range p = {a, b} := by simpa only [inter_comm] using hpq
      obtain ⟨w, v, hw, hv, hwv, hcover, ⟨t, ht, htq⟩, hpV⟩ :=
        exists_reroot_two_arcs_of_mem_left q p hq hp hqp hr hrb
      obtain ⟨u, hu, huQ⟩ := exists_terminal_subpath_subset_terminal_subpath
        q beta hq htb ht htbQ
      have hvw : range v ∩ range w = {r, b} := by simpa only [inter_comm] using hwv
      have hcover' : range w ∪ range v = range p ∪ range q := by
        simpa only [union_comm] using hcover
      exact ⟨v, w, hv, hw, hvw, subset_union_right.trans hcover'.le,
        subset_union_left.trans hcover'.le, ⟨ta, hta, htaP.trans hpV⟩,
        ⟨u, hu, huQ.trans htq⟩⟩
  obtain ⟨v, w, hv, hw, hvw, hvsub, hwsub, ⟨u, hu, huA⟩, ⟨t, ht, htB⟩⟩ := hex
  obtain ⟨v', hv', hv'sub, u', hu', hv'tail⟩ :=
    exists_path_with_parametrized_retained_tail v alpha hv ha hu huA
  obtain ⟨w', hw', hw'sub, t', ht', hw'tail⟩ :=
    exists_path_with_parametrized_retained_tail w beta hw hb ht htB
  have hvw' : range v' ∩ range w' = {r, b} := by
    apply subset_antisymm
    · exact (inter_subset_inter hv'sub hw'sub).trans hvw.le
    · simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨⟨v'.source_mem_range, w'.source_mem_range⟩,
        ⟨v'.target_mem_range, w'.target_mem_range⟩⟩
  exact ⟨v', w', hv', hw', hvw', hv'sub.trans hvsub, hw'sub.trans hwsub,
    ⟨u', hu', hv'tail⟩, ⟨t', ht', hw'tail⟩⟩

end FiniteAvalanches.Electrical.StatementGeometry
