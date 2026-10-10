import FiniteAvalanches.Wilson.Lattice.PrependRay
import FiniteAvalanches.Model.WiredTreeExistence
import FiniteAvalanches.Trees.ConnectorTree

/-! Ordinary escaping rays from original copied wired-box paths. -/
open scoped Classical
namespace FiniteAvalanches.Wilson.Lattice.FiniteExitRay
open LatticeProb FiniteAvalanches.Sandpile
open FiniteAvalanches.Trees.RootedPaths
noncomputable section

def outwardVertex {N : ℕ} (a : FiniteWired.Active N)
    (d : FiniteWired.Direction) (n : ℕ) : Site 2 :=
  FiniteWired.site a + (n : ℤ) • FiniteWired.step d

theorem outwardVertex_apply {N : ℕ} (a : FiniteWired.Active N)
    (d : FiniteWired.Direction) (n : ℕ) (i : Fin 2) :
    outwardVertex a d n i = FiniteWired.site a i +
      if i = d.1 then (if d.2 then (n : ℤ) else -(n : ℤ)) else 0 := by
  rcases d with ⟨j, b⟩
  cases b <;> by_cases h : i = j <;>
    simp [outwardVertex, FiniteWired.step, unit, h]

theorem outwardVertex_zero {N : ℕ} (a : FiniteWired.Active N)
    (d : FiniteWired.Direction) : outwardVertex a d 0 = FiniteWired.site a := by
  simp [outwardVertex]

theorem outwardVertex_adjacent {N : ℕ} (a : FiniteWired.Active N)
    (d : FiniteWired.Direction) (n : ℕ) :
    (lattice 2).Adj (outwardVertex a d n) (outwardVertex a d (n + 1)) := by
  refine ⟨d.1, ?_⟩
  cases h : d.2
  · right
    funext i
    simp only [Pi.add_apply]
    rw [outwardVertex_apply, outwardVertex_apply]
    by_cases hi : i = d.1 <;> simp [unit, hi, h]
    all_goals omega
  · left
    funext i
    simp only [Pi.add_apply]
    rw [outwardVertex_apply, outwardVertex_apply]
    by_cases hi : i = d.1 <;> simp [unit, hi, h]
    all_goals omega

theorem outwardVertex_injective {N : ℕ} (a : FiniteWired.Active N)
    (d : FiniteWired.Direction) : Function.Injective (outwardVertex a d) := by
  intro n m h
  have he := congrFun h d.1
  rw [outwardVertex_apply, outwardVertex_apply] at he
  cases d.2 <;> simp only [ite_true] at he <;> omega

theorem outwardVertex_outside {N : ℕ} (e : FiniteWired.ExitEdge N)
    {n : ℕ} (hn : 0 < n) :
    ¬ FiniteWired.inBox N (outwardVertex e.val.1 e.val.2 n) := by
  intro hb
  apply e.property
  intro i
  have ha := (e.val.1 i).property
  change -(N : ℤ) ≤ FiniteWired.site e.val.1 i ∧ FiniteWired.site e.val.1 i ≤ N at ha
  have hi := hb i
  rw [outwardVertex_apply] at hi
  change -(N : ℤ) ≤ FiniteWired.site e.val.1 i + FiniteWired.step e.val.2 i ∧
    FiniteWired.site e.val.1 i + FiniteWired.step e.val.2 i ≤ N
  by_cases hdir : i = e.val.2.1
  · subst i
    cases h : e.val.2.2 <;> simp [FiniteWired.step, unit, h] at hi ⊢ <;> omega
  · cases h : e.val.2.2 <;>
      simp [FiniteWired.step, unit, hdir, h] at hi ⊢ <;> omega

def straightExitRay {N : ℕ} (e : FiniteWired.ExitEdge N) : SimpleRay where
  vertex := outwardVertex e.val.1 e.val.2
  adjacent := outwardVertex_adjacent e.val.1 e.val.2
  injective := outwardVertex_injective e.val.1 e.val.2

theorem copied_internal_adjacent {N : ℕ} {F : Finset (FiniteWired.Edge N)}
    {a b : FiniteWired.Active N}
    (h : ((WiredTrees.graph N).toSimple F).Adj (some a) (some b)) :
    (lattice 2).Adj (FiniteWired.site a) (FiniteWired.site b) := by
  obtain ⟨e, _, he⟩ := h
  change ((FiniteWired.endpoints e).1 = some a ∧ (FiniteWired.endpoints e).2 = some b) ∨
    ((FiniteWired.endpoints e).2 = some a ∧ (FiniteWired.endpoints e).1 = some b) at he
  cases e with
  | inl e =>
    obtain ⟨i, hi⟩ := e.property
    rcases he with he | he
    · have ha := Option.some.inj he.1
      have hb := Option.some.inj he.2
      exact ⟨i, Or.inl (by simpa only [← ha, ← hb] using hi)⟩
    · have hb := Option.some.inj he.2
      have ha := Option.some.inj he.1
      exact ⟨i, Or.inr (by simpa only [← ha, ← hb] using hi)⟩
  | inr e => rcases he with he | he <;> simp [FiniteWired.endpoints] at he

/-- The original last exit copy, not a collapsed or newly selected boundary edge. -/
theorem copied_exit {N : ℕ} {F : Finset (FiniteWired.Edge N)}
    {a : FiniteWired.Active N}
    (h : ((WiredTrees.graph N).toSimple F).Adj (some a) none) :
    ∃ e : FiniteWired.ExitEdge N, Sum.inr e ∈ F ∧ e.val.1 = a := by
  obtain ⟨e, heF, he⟩ := h
  change ((FiniteWired.endpoints e).1 = some a ∧ (FiniteWired.endpoints e).2 = none) ∨
    ((FiniteWired.endpoints e).2 = some a ∧ (FiniteWired.endpoints e).1 = none) at he
  cases e with
  | inl e => rcases he with he | he <;> simp [FiniteWired.endpoints] at he
  | inr e =>
    rcases he with he | he
    · exact ⟨e, heF, Option.some.inj he.1⟩
    · simp [FiniteWired.endpoints] at he

/-- Every genuine simple copied path to the sink extends along its own last exit.
The inside vertices are retained, and the infinite tail is straight. -/
theorem walk_extension {N : ℕ} {F : Finset (FiniteWired.Edge N)}
    {u v : FiniteWired.Vertex N} (p : ((WiredTrees.graph N).toSimple F).Walk u v)
    (hp : p.IsPath) (hv : v = none) (a : FiniteWired.Active N) (hu : u = some a) :
    ∃ γ : SimpleRay, γ.vertex 0 = FiniteWired.site a ∧
      (∀ n, FiniteWired.inBox N (γ.vertex n) →
        ∃ b : FiniteWired.Active N, γ.vertex n = FiniteWired.site b ∧ some b ∈ p.support) ∧
      ∃ e : FiniteWired.ExitEdge N, Sum.inr e ∈ F ∧
        (WiredTrees.graph N).edge (Sum.inr e) ∈ p.edges ∧
        ∃ m : ℕ, ∀ n, γ.vertex (m + n) = outwardVertex e.val.1 e.val.2 n := by
  induction p generalizing a with
  | nil => exact (Option.some_ne_none a (hu.symm.trans hv)).elim
  | @cons u v w h p ih =>
    subst u
    subst w
    have hpq := hp.of_cons
    have hfree := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp |>.2
    cases v with
    | none =>
      have hnil := SimpleGraph.Walk.eq_nil_iff_nil.mpr (hpq.nil_iff_eq.mpr rfl)
      subst p
      obtain ⟨e, heF, hea⟩ := copied_exit h
      refine ⟨straightExitRay e, ?_, ?_, e, heF, ?_, 0, ?_⟩
      · simp only [straightExitRay, outwardVertex_zero, hea]
      · intro n hn
        have hn0 : n = 0 := by
          by_contra hn0
          exact outwardVertex_outside e (Nat.pos_of_ne_zero hn0) hn
        subst n
        exact ⟨a, by simp [straightExitRay, outwardVertex_zero, hea], by simp⟩
      · change s(some e.val.1, none) ∈ _
        simp [hea]
      · intro n
        simp only [Nat.zero_add]
        rfl
    | some b =>
      obtain ⟨γ, hstart, hinside, e, heF, hepath, m, htail⟩ := ih hpq rfl b rfl
      have hnot : FiniteWired.site a ∉ γ.vertices := by
        rintro ⟨n, hn⟩
        have hb : FiniteWired.inBox N (γ.vertex n) := by
          rw [hn]
          exact fun i => (a i).property
        obtain ⟨c, hc, hcp⟩ := hinside n hb
        have hca : c = a := FiniteWired.site_injective N (hc.symm.trans hn)
        exact hfree (hca ▸ hcp)
      have hadj : (lattice 2).Adj (FiniteWired.site a) (γ.vertex 0) := by
        rw [hstart]
        exact copied_internal_adjacent h
      refine ⟨γ.prepend (FiniteWired.site a) hadj hnot, rfl, ?_,
        e, heF, List.mem_cons_of_mem _ hepath, m + 1, ?_⟩
      · intro n hn
        cases n with
        | zero => exact ⟨a, rfl, List.mem_cons_self⟩
        | succ n =>
          obtain ⟨c, hc, hcp⟩ := hinside n hn
          exact ⟨c, hc, List.mem_cons_of_mem _ hcp⟩
      · intro n
        rw [show m + 1 + n = (m + n) + 1 by omega]
        exact htail n

end
end FiniteAvalanches.Wilson.Lattice.FiniteExitRay
