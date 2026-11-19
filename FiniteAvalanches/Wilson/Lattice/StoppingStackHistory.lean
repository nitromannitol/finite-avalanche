import FiniteAvalanches.Wilson.Lattice.RandomStackHistory

/-! Fresh stack walks after a finite, adaptively chosen stack history. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory FiniteAvalanches.Sandpile Function
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- A state determined by the entries below its own finite cursor is independent
of the next walk read from that cursor, even when its start depends on the state. -/
theorem directionStackLaw_stopping_history_inter_reading
    {α : Type*} [Countable α] (head : V → FiniteWired.Direction → V)
    (state : (V × ℕ → FiniteWired.Direction) → α) (k : α → Cursor V) (x : α → V)
    (hstable : ∀ σ τ, (∀ v i, i < k (state σ) v → τ (v, i) = σ (v, i)) →
      state τ = state σ)
    (P : α → Prop) (A : Set WalkDriver) (hA : MeasurableSet A) :
    directionStackLaw V {σ | P (state σ) ∧
      readingLetter head (x (state σ)) (k (state σ)) σ ∈ A} =
    directionStackLaw V {σ | P (state σ)} * walkLaw A := by
  let I := {p : Σ a : α, prefixIndices (k a) → FiniteWired.Direction //
    P p.1 ∧ ∃ σ : V × ℕ → FiniteWired.Direction,
      state σ = p.1 ∧ ∀ q, σ q.val = p.2 q}
  let witness : I → V × ℕ → FiniteWired.Direction := fun p => Classical.choose p.property.2
  have hw (p : I) : state (witness p) = p.val.1 ∧
      ∀ q, witness p q.val = p.val.2 q := Classical.choose_spec p.property.2
  let c : I → Cursor V := fun p => k p.val.1
  let start : I → V := fun p => x p.val.1
  have hstate (p : I) (σ : V × ℕ → FiniteWired.Direction)
      (h : ∀ v i, i < c p v → σ (v, i) = witness p (v, i)) :
      state σ = p.val.1 := by
    apply (hstable (witness p) σ ?_).trans (hw p).1
    simpa only [(hw p).1, c] using h
  have hdis : Pairwise (Disjoint on fun p : I =>
      {σ : V × ℕ → FiniteWired.Direction |
        ∀ v i, i < c p v → σ (v, i) = witness p (v, i)}) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro σ hσp hσq
    have ha : p.val.1 = q.val.1 := (hstate p σ hσp).symm.trans (hstate q σ hσq)
    apply hpq
    apply Subtype.ext
    rcases p with ⟨⟨a, u⟩, hp⟩
    rcases q with ⟨⟨b, v⟩, hq⟩
    dsimp only at ha
    subst b
    change (⟨a, u⟩ : Σ a : α, prefixIndices (k a) → FiniteWired.Direction) = ⟨a, v⟩
    congr 1
    funext z
    have hu := (hw ⟨⟨a, u⟩, hp⟩).2 z
    have hv := (hw ⟨⟨a, v⟩, hq⟩).2 z
    have hsu := hσp z.val.1 z.val.2 ((mem_prefixIndices (k a) _ _).mp z.property)
    have hsv := hσq z.val.1 z.val.2 ((mem_prefixIndices (k a) _ _).mp z.property)
    exact hu.symm.trans (hsu.symm.trans (hsv.trans hv))
  have hU : (⋃ p : I, {σ : V × ℕ → FiniteWired.Direction |
      ∀ v i, i < c p v → σ (v, i) = witness p (v, i)}) = {σ | P (state σ)} := by
    ext σ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp⟩
      rw [hstate p σ hp]
      exact p.property.1
    · intro hP
      let p : I := ⟨⟨state σ, fun q => σ q.val⟩, hP, σ, rfl, fun _ => rfl⟩
      refine ⟨p, ?_⟩
      intro v i hi
      exact ((hw p).2 ⟨(v, i), (mem_prefixIndices (k (state σ)) v i).mpr hi⟩).symm
  have hE : (⋃ p : I, {σ : V × ℕ → FiniteWired.Direction |
      (∀ v i, i < c p v → σ (v, i) = witness p (v, i)) ∧
      readingLetter head (start p) (c p) σ ∈ A}) =
      {σ | P (state σ) ∧ readingLetter head (x (state σ)) (k (state σ)) σ ∈ A} := by
    ext σ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, hA'⟩
      have hs := hstate p σ hp
      refine ⟨hs.symm ▸ p.property.1, ?_⟩
      simpa only [hs, start, c] using hA'
    · rintro ⟨hP, hA'⟩
      let p : I := ⟨⟨state σ, fun q => σ q.val⟩, hP, σ, rfl, fun _ => rfl⟩
      refine ⟨p, ?_, hA'⟩
      intro v i hi
      exact ((hw p).2 ⟨(v, i), (mem_prefixIndices (k (state σ)) v i).mpr hi⟩).symm
  have h := directionStackLaw_iUnion_prefix_inter_reading V head start c witness hdis A hA
  simpa only [hE, hU] using h

end
end FiniteAvalanches.Wilson.Lattice
