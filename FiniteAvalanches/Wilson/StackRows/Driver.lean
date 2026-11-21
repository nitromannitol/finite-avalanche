import FiniteAvalanches.Wilson.StackRows.Words
import FiniteAvalanches.Wilson.CyclePopping.IncidentForestLaw
import FiniteAvalanches.Wilson.CyclePopping.InstructionTrace

/-! A copied walk driven by vertex stacks of incident copies. At every time the driver
offers each vertex the entry of its stack at the current cursor; the walk uses the entry
at its own position, so it follows the chronological stack trace. The event that this
driver realizes a word of copies is a cylinder on distinct stack coordinates and has the
same product inverse-degree mass as the word event for independent uniform letters. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CopiedNetwork

open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Vertex stacks of incident copies, indexed by vertex and depth. -/
abbrev CopyStacks := (p : V × ℕ) → IncidentCopy G p.1

/-- The chronological walk from `x` reading the stacks from the cursor `k`. -/
def stackTrace (σ : CopyStacks G) (k : Cursor V) (x : V) :
    ℕ → Σ y : V, @Quiver.Path V (instructionQuiver (incidentCopyHead G)) x y :=
  instructionTrace (incidentCopyHead G) (fun v i => σ (v, i)) k x

/-- The stack cursors after the first `n` steps of the walk. -/
def traceCursor (σ : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ) : Cursor V :=
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  consume k (stackTrace G σ k x n).2

/-- The driver offering every vertex the entry of its stack at the current cursor. -/
def stackDriver (σ : CopyStacks G) (k : Cursor V) (x : V) : Driver G :=
  fun n v => σ (v, traceCursor G σ k x n v)

theorem traceCursor_succ (σ : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ) :
    traceCursor G σ k x (n + 1) =
      pop (traceCursor G σ k x n) {(stackTrace G σ k x n).1} := rfl

theorem stackTrace_succ_fst (σ : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ) :
    (stackTrace G σ k x (n + 1)).1 = incidentCopyHead G (stackTrace G σ k x n).1
      (σ ((stackTrace G σ k x n).1, traceCursor G σ k x n (stackTrace G σ k x n).1)) := rfl

/-- The walk of the stack driver is the stack trace. -/
theorem position_stackDriver (σ : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ) :
    position G x (stackDriver G σ k x) n = (stackTrace G σ k x n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stackTrace_succ_fst]
    change other G (position G x (stackDriver G σ k x) n)
      (stackDriver G σ k x n (position G x (stackDriver G σ k x) n)) = _
    rw [ih]
    rfl

/-- The copy used by the stack driver is the stack entry at the current cursor. -/
theorem usedCopy_stackDriver (σ : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ) :
    usedCopy G x (stackDriver G σ k x) n =
      (σ ((stackTrace G σ k x n).1, traceCursor G σ k x n (stackTrace G σ k x n).1)).val := by
  rw [usedCopy, position_stackDriver]
  rfl

/-- While the stack driver reads the copies of a word, its trace and cursors follow the
word. -/
theorem stackTrace_eq_wordWalk (σ : CopyStacks G) (k : Cursor V) (x : V) (L : List E) (n : ℕ)
    (h : ∀ i < n, L[i]? = some (usedCopy G x (stackDriver G σ k x) i)) :
    (stackTrace G σ k x n).1 = (wordWalk G x k L n).1 ∧
      traceCursor G σ k x n = (wordWalk G x k L n).2 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    refine ⟨?_, ?_⟩
    · rw [stackTrace_succ_fst]
      change _ = copyHead G (wordWalk G x k L n).1 L[n]?
      rw [hn, usedCopy_stackDriver, ← h1]
      rfl
    · rw [traceCursor_succ, h2, h1]
      rfl

/-- The stack coordinate read at time `i` along the word `L` from the cursor `k`. -/
abbrev wordAddr (x : V) (k : Cursor V) (L : List E) (i : ℕ) : V × ℕ :=
  wordAddress (copyHead G) x k (fun j => L[j]?) i

theorem wordAddr_fst (x : V) (k : Cursor V) (L : List E) (i : ℕ) :
    (wordAddr G x k L i).1 = wordPos G x L i :=
  wordWalk_fst G x k L i

/-- The stack driver realizes a word exactly when the word is valid and the stacks hold
its copies at the word addresses. -/
theorem stackDriver_mem_rowCyl_iff (σ : CopyStacks G) (R : Set V) (k : Cursor V) (x : V)
    (L : List E) :
    stackDriver G σ k x ∈ rowCyl G R x L ↔ ValidWord G R x L ∧
      ∀ i < L.length, L[i]? = some (σ (wordAddr G x k L i)).val := by
  rw [rowCyl_eq, Set.mem_setOf_eq]
  apply and_congr_right
  intro _
  suffices H : ∀ n, (∀ i < n, L[i]? = some (stackDriver G σ k x i (wordPos G x L i)).val) ↔
      ∀ i < n, L[i]? = some (σ (wordAddr G x k L i)).val from H _
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have step : (∀ i < n, L[i]? = some (stackDriver G σ k x i (wordPos G x L i)).val) →
        (stackDriver G σ k x n (wordPos G x L n)).val = (σ (wordAddr G x k L n)).val := by
      intro hlt
      have hu := (usedCopy_iff_wordPos G x (stackDriver G σ k x) L n).mpr hlt
      obtain ⟨_, h2⟩ := stackTrace_eq_wordWalk G σ k x L n hu
      have hp : wordPos G x L n = (wordWalk G x k L n).1 := (wordWalk_fst G x k L n).symm
      have hq : (wordPos G x L n, traceCursor G σ k x n (wordPos G x L n)) =
          wordAddr G x k L n := by
        change _ = ((wordWalk G x k L n).1, (wordWalk G x k L n).2 (wordWalk G x k L n).1)
        rw [h2, hp]
      exact congrArg (fun q => (σ q).val) hq
    constructor
    · intro hall i hi
      have hlt : ∀ j < n, L[j]? = some (stackDriver G σ k x j (wordPos G x L j)).val :=
        fun j hj => hall j (Nat.lt_succ_of_lt hj)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact ih.mp hlt i hi
      · rw [← step hlt]
        exact hall i hi
    · intro hall i hi
      have hlt := ih.mpr (fun j hj => hall j (Nat.lt_succ_of_lt hj))
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hlt i hi
      · rw [step hlt]
        exact hall i hi

/-- The stack word events depend only on the word addresses. -/
theorem stackDriver_mem_rowCyl_congr (σ σ' : CopyStacks G) (R : Set V) (k : Cursor V) (x : V)
    (L : List E) (h : ∀ i < L.length, σ (wordAddr G x k L i) = σ' (wordAddr G x k L i)) :
    stackDriver G σ k x ∈ rowCyl G R x L ↔ stackDriver G σ' k x ∈ rowCyl G R x L := by
  rw [stackDriver_mem_rowCyl_iff, stackDriver_mem_rowCyl_iff]
  apply and_congr_right
  intro _
  constructor
  · intro hw i hi
    rw [← h i hi]
    exact hw i hi
  · intro hw i hi
    rw [h i hi]
    exact hw i hi

theorem measurableSet_stackCyl (R : Set V) (k : Cursor V) (x : V) (L : List E) :
    MeasurableSet {σ : CopyStacks G | stackDriver G σ k x ∈ rowCyl G R x L} := by
  have he : {σ : CopyStacks G | stackDriver G σ k x ∈ rowCyl G R x L} =
      {_σ | ValidWord G R x L} ∩
        ⋂ i ∈ Finset.range L.length,
          (fun σ : CopyStacks G => σ (wordAddr G x k L i)) ⁻¹'
            {c | L[i]? = some c.val} := by
    ext σ
    simp only [Set.mem_setOf_eq, stackDriver_mem_rowCyl_iff, Set.mem_inter_iff, Set.mem_iInter,
      Finset.mem_range, Set.mem_preimage]
  rw [he]
  refine MeasurableSet.inter ?_ ?_
  · by_cases hv : ValidWord G R x L
    · simp only [hv, Set.setOf_true, MeasurableSet.univ]
    · simp only [hv, Set.setOf_false, MeasurableSet.empty]
  · refine Finset.measurableSet_biInter _ (fun i _ => ?_)
    exact measurable_pi_apply _ (Set.toFinite _).measurableSet

variable [∀ v, Nonempty (IncidentCopy G v)]

/-- The stack word event has the product inverse-degree mass along a valid word. -/
theorem variableStackLaw_stackCyl (R : Set V) (k : Cursor V) (x : V) (L : List E) :
    variableStackLaw (IncidentCopy G) {σ | stackDriver G σ k x ∈ rowCyl G R x L} =
      if ValidWord G R x L then
        ∏ i ∈ Finset.range L.length, (Nat.card (Incident G (wordPos G x L i)) : ℝ≥0∞)⁻¹
      else 0 := by
  have hinj : Function.Injective (wordAddr G x k L) := wordAddress_injective _ _ _ _
  simp_rw [stackDriver_mem_rowCyl_iff]
  split_ifs with hv
  · let t : (p : V × ℕ) → Set (IncidentCopy G p.1) :=
      fun p => {c | ∀ i < L.length, wordAddr G x k L i = p → L[i]? = some c.val}
    have hs : {σ : CopyStacks G | ValidWord G R x L ∧
        ∀ i < L.length, L[i]? = some (σ (wordAddr G x k L i)).val} =
        Set.pi ((Finset.range L.length).image (wordAddr G x k L) : Set (V × ℕ)) t := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_image, Finset.coe_range,
        Set.mem_image, Set.mem_Iio, hv, true_and, t]
      constructor
      · rintro h p ⟨i, hi, rfl⟩ j hj hji
        rw [hinj hji]
        exact h i hi
      · intro h i hi
        exact h (wordAddr G x k L i) ⟨i, hi, rfl⟩ i hi rfl
    rw [hs, variableStackLaw, Measure.infinitePi_pi,
      Finset.prod_image (fun i _ j _ h => hinj h)]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      obtain ⟨e, he⟩ : ∃ e, L[i]? = some e := ⟨L[i], List.getElem?_eq_getElem hi'⟩
      have hpos := wordAddr_fst G x k L i
      have hinc : G.left e = (wordAddr G x k L i).1 ∨ G.right e = (wordAddr G x k L i).1 := by
        rw [hpos]
        exact hv.1 i hi' e he
      have ht : t (wordAddr G x k L i) = {⟨e, hinc⟩} := by
        ext c
        simp only [t, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hc
          apply Subtype.ext
          have h' := hc i hi' rfl
          rw [he, Option.some.injEq] at h'
          exact h'.symm
        · rintro rfl j hj hji
          rw [hinj hji, he]
      rw [ht, FiniteAvalanches.uniformMeasure_apply, Nat.card_unique, Nat.cast_one, one_div, hpos]
      rfl
    · intro p _
      exact (Set.toFinite _).measurableSet
  · have hs : {σ : CopyStacks G | ValidWord G R x L ∧
        ∀ i < L.length, L[i]? = some (σ (wordAddr G x k L i)).val} = ∅ := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hv
    rw [hs, measure_empty]

end
end FiniteAvalanches.Wilson.CopiedNetwork
