import FiniteAvalanches.Support.Plane.BoundaryArcJoin
import FiniteAvalanches.Support.Plane.LoopPaths

/-!
# Completing an interior subarc

The portions of a simple path on either side of an interior subarc give disjoint
access paths to its complement. Joining these paths closes the subarc into a
simple loop.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open scoped Classical

private theorem subpath_injective {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (hp : Function.Injective p) {s t : unitInterval} (hst : s ≠ t) :
    Function.Injective (p.subpath s t) := by
  intro u v huv
  have h := congrArg Subtype.val (hp huv)
  simp only [Set.Icc.coe_convexComb] at h
  have hst' : (s : ℝ) ≠ t := fun h => hst (Subtype.ext h)
  apply Subtype.ext
  have hz : ((u : ℝ) - v) * ((t : ℝ) - s) = 0 := by nlinarith [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (Ne.symm hst')))

/-- An interior subarc of a simple plane path has a simple closing arc which
meets it only at its endpoints. -/
theorem exists_closing_arc_of_subpath {x y : ℝ × ℝ} (p : Path x y)
    (hp : Function.Injective p) (a b : unitInterval)
    (ha : (0 : ℝ) < a.val) (hab : a.val < b.val) (hb : b.val < 1) :
    ∃ q : Path (p a) (p b), Function.Injective q ∧
      range (p.subpath a b) ∩ range q = {p a, p b} := by
  have hab' : a < b := hab
  have h0a : (0 : unitInterval) < a := ha
  have hb1 : b < (1 : unitInterval) := hb
  let mid := p.subpath a b
  let left := p.subpath 0 a
  let right := p.subpath 1 b
  have hmid : Function.Injective mid := subpath_injective p hp (ne_of_lt hab')
  have hleft : Function.Injective left := subpath_injective p hp (ne_of_lt h0a)
  have hright : Function.Injective right := subpath_injective p hp (ne_of_gt hb1)
  let U : Set (ℝ × ℝ) := (range mid)ᶜ
  have hU : IsOpen U := (isCompact_range mid.continuous).isClosed.isOpen_compl
  have hconn : IsPreconnected U := by
    simpa only [U, Set.sdiff_eq, Set.univ_inter] using
      (isPreconnected_sdiff_injective_path isOpen_univ isPreconnected_univ mid hmid
        (subset_univ (range mid)))
  have hdisjoint : Disjoint (range left) (range right) := by
    apply disjoint_left.mpr
    intro z hz1 hz2
    rw [show range left = p '' Icc 0 a from Path.range_subpath_of_le p 0 a bot_le] at hz1
    rw [show range right = p '' Icc b 1 from Path.range_subpath_of_ge p 1 b le_top] at hz2
    obtain ⟨u, hu, rfl⟩ := hz1
    obtain ⟨v, hv, heq⟩ := hz2
    have huv : v = u := hp heq
    have hle : b ≤ a := le_trans hv.1 (huv.symm ▸ hu.2)
    exact (not_le_of_gt hab') hle
  have hleftU : ∀ t : unitInterval, t ≠ 1 → left t ∈ U := by
    intro t ht hmem
    rw [show range mid = p '' Icc a b from Path.range_subpath_of_le p a b hab'.le] at hmem
    obtain ⟨v, hv, heq⟩ := hmem
    have hpar : Set.Icc.convexComb (0 : unitInterval) a t = v := hp heq.symm
    have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (fun h => ht (Subtype.ext h))
    have hval := congrArg Subtype.val hpar
    simp only [Set.Icc.coe_convexComb] at hval
    have hva : (a : ℝ) ≤ v := hv.1
    change (1 - (t : ℝ)) * 0 + (t : ℝ) * (a : ℝ) = (v : ℝ) at hval
    have hpos : 0 < (1 - (t : ℝ)) * (a : ℝ) := mul_pos (by linarith) ha
    nlinarith
  have hrightU : ∀ t : unitInterval, t ≠ 1 → right t ∈ U := by
    intro t ht hmem
    rw [show range mid = p '' Icc a b from Path.range_subpath_of_le p a b hab'.le] at hmem
    obtain ⟨v, hv, heq⟩ := hmem
    have hpar : Set.Icc.convexComb (1 : unitInterval) b t = v := hp heq.symm
    have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (fun h => ht (Subtype.ext h))
    have hval := congrArg Subtype.val hpar
    simp only [Set.Icc.coe_convexComb] at hval
    have hvb : (v : ℝ) ≤ b := hv.2
    change (1 - (t : ℝ)) * 1 + (t : ℝ) * (b : ℝ) = (v : ℝ) at hval
    have hpos : 0 < (1 - (t : ℝ)) * (1 - (b : ℝ)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have haU : p a ∉ U := fun h => h mid.source_mem_range
  have hbU : p b ∉ U := fun h => h mid.target_mem_range
  obtain ⟨q, hq, hqboundary⟩ :=
    exists_injective_path_between_boundary_accesses hU hconn left right hleft hright
      hdisjoint hleftU hrightU haU hbU
  refine ⟨q, hq, ?_⟩
  have hcompl : Uᶜ = range mid := by simp only [U, compl_compl]
  rw [hcompl, inter_comm] at hqboundary
  exact hqboundary

end FiniteAvalanches.Electrical.StatementGeometry
