import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import Mathlib.Topology.Path
import Mathlib.Topology.Order.IntermediateValue

open Set unitInterval

namespace FiniteAvalanches.Electrical.StatementGeometry

/-- Joining simple paths at their only common point preserves simplicity. -/
theorem path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X}
    (f : Path a b) (g : Path b c) (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : ∀ s t, f s = g t → f s = b) :
    Function.Injective (f.trans g) := by
  intro s t h
  rw [Path.trans_apply, Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · have hh := congrArg Subtype.val (hf h)
    exact Subtype.ext (by dsimp at hh; linarith)
  · have hb := hfg _ _ h
    have h1 := congrArg Subtype.val (hf (hb.trans f.target.symm))
    have h0 := congrArg Subtype.val (hg (h.symm.trans hb |>.trans g.source.symm))
    exact Subtype.ext (by dsimp at h1 h0; linarith)
  · have hb := hfg _ _ h.symm
    have h1 := congrArg Subtype.val (hf (hb.trans f.target.symm))
    have h0 := congrArg Subtype.val (hg (h.trans hb |>.trans g.source.symm))
    exact Subtype.ext (by dsimp at h1 h0; linarith)
  · have hh := congrArg Subtype.val (hg h)
    exact Subtype.ext (by dsimp at hh; linarith)

/-- A finite simple chain of arcs has a simple continuous realization with ordered visit times.
The hypotheses describe the individual arcs and their intersections, not a circle order. -/
theorem simple_chain_realization {X : Type*} [TopologicalSpace X] (n : ℕ)
    (p : Fin (n + 2) → X) (hp : Function.Injective p)
    (arcs : ∀ i : Fin (n + 1), Path (p i.castSucc) (p i.succ))
    (hinj : ∀ i, Function.Injective (arcs i))
    (hcross : ∀ i j, i ≠ j → ∀ s t, arcs i s = arcs j t →
      (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) :
    ∃ f : Path (p 0) (p (Fin.last (n + 1))), Function.Injective f ∧
      ∃ τ : Fin (n + 2) → I, StrictMono τ ∧ τ 0 = 0 ∧ τ (Fin.last (n + 1)) = 1 ∧
        (∀ k, f (τ k) = p k) ∧ (∀ t, ∃ i s, f t = arcs i s) := by
  induction n with
  | zero =>
    refine ⟨arcs 0, hinj 0, ![0, 1], ?_, rfl, rfl, ?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro k
      fin_cases k
      · exact (arcs 0).source
      · exact (arcs 0).target
    · intro t
      exact ⟨0, t, rfl⟩
  | succ n ih =>
    let q : Fin (n + 2) → X := fun i => p i.succ
    let tail : ∀ i : Fin (n + 1), Path (q i.castSucc) (q i.succ) := fun i => arcs i.succ
    obtain ⟨g, hg, τ, hτ, hτ0, hτ1, hvisit, hrange⟩ :=
      ih q (hp.comp (Fin.succ_injective (n + 2))) tail (fun i => hinj i.succ)
        (fun i j hij => hcross i.succ j.succ (fun h => hij (Fin.succ_injective (n + 1) h)))
    let f := (arcs 0).trans g
    have hmeet : ∀ s t, arcs 0 s = g t → arcs 0 s = p (Fin.succ 0) := by
      intro s t h
      obtain ⟨i, r, hr⟩ := hrange t
      have hx := hcross 0 i.succ (by intro he; have := congrArg Fin.val he; simp at this)
        s r (h.trans hr)
      rcases hx.1 with rfl | rfl <;> rcases hx.2 with rfl | rfl
      · have he := hp ((arcs 0).source.symm.trans ((h.trans hr).trans (arcs i.succ).source))
        have := congrArg Fin.val he
        simp at this
      · have he := hp ((arcs 0).source.symm.trans ((h.trans hr).trans (arcs i.succ).target))
        have := congrArg Fin.val he
        simp at this
      · exact (arcs 0).target
      · exact (arcs 0).target
    let shift (t : I) : I :=
      ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
    let times : Fin (n + 3) → I := Fin.cons 0 (fun i => shift (τ i))
    refine ⟨f, path_trans_injective _ _ (hinj 0) hg hmeet, times, ?_, rfl, ?_, ?_, ?_⟩
    · intro a b hab
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => exact (lt_irrefl _ hab).elim
        | succ b =>
          change (0 : ℝ) < ((τ b : ℝ) + 1) / 2
          linarith [(τ b).property.1]
      | succ a =>
        cases b using Fin.cases with
        | zero => exact (not_lt_of_ge (Fin.zero_le _) hab).elim
        | succ b =>
          have ht := hτ (by change a.val < b.val; have hh : a.val + 1 < b.val + 1 := hab; omega)
          change ((τ a : ℝ) + 1) / 2 < ((τ b : ℝ) + 1) / 2
          have ht' : (τ a : ℝ) < τ b := ht
          linarith
    · apply Subtype.ext
      change ((τ (Fin.last (n + 1)) : ℝ) + 1) / 2 = 1
      rw [hτ1]
      norm_num
    · intro k
      cases k using Fin.cases with
      | zero => exact f.source
      | succ k =>
        change f (shift (τ k)) = q k
        have hh : (1 : ℝ) / 2 ≤ (shift (τ k) : ℝ) := by
          change 1 / 2 ≤ ((τ k : ℝ) + 1) / 2
          linarith [(τ k).property.1]
        have hn : 2 * (shift (τ k) : ℝ) - 1 = (τ k : ℝ) := by
          change 2 * (((τ k : ℝ) + 1) / 2) - 1 = (τ k : ℝ)
          ring
        calc
          f (shift (τ k)) = f.extend (shift (τ k)) := (Path.extend_apply _ _).symm
          _ = g.extend (2 * (shift (τ k) : ℝ) - 1) :=
            Path.extend_trans_of_half_le _ _ hh
          _ = g (τ k) := by rw [hn, Path.extend_apply]
          _ = q k := hvisit k
    · intro t
      have ht : f t ∈ Set.range (arcs 0) ∪ Set.range g := by
        rw [← Path.trans_range]
        exact ⟨t, rfl⟩
      rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact ⟨0, s, hs.symm⟩
      · obtain ⟨i, r, hr⟩ := hrange s
        exact ⟨i.succ, r, hs.symm.trans hr⟩

end FiniteAvalanches.Electrical.StatementGeometry
