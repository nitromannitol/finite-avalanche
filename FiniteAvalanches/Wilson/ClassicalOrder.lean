import FiniteAvalanches.Wilson.UniformLetters
import FiniteAvalanches.Wilson.SpanningTrees

/-! Normalize a spanning query list to the classical ordering of distinct
nonroot vertices. Removing skipped entries preserves the entire first-unretained
protocol pointwise, including all complete histories and failure arrays. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E I : Type} [Fintype V] [Fintype E]
variable (G : Multigraph V E) (ι : E ↪ I)

theorem classicalExplore_filter (p : V → Bool) (s : State (V := V) (E := E) (I := I))
    (hp : ∀ v, p v = false → v ∈ s.roots) (order : List V) (ω : ℕ → Driver G) :
    classicalExplore G ι s (order.filter p) ω = classicalExplore G ι s order ω := by
  induction order generalizing s ω with
  | nil => rfl
  | cons x xs ih =>
    cases hx : p x with
    | false =>
      have hr := hp x hx
      simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte, classicalExplore, if_pos hr]
      exact ih s hp ω
    | true =>
      simp only [List.filter_cons, hx, ↓reduceIte]
      by_cases hr : x ∈ s.roots
      · simp only [classicalExplore, if_pos hr]
        exact ih s hp ω
      · simp only [classicalExplore, if_neg hr]
        cases he : query G ι s x (ω 0) with
        | none => rfl
        | some t =>
          simp only [Option.bind_some]
          exact ih t (fun v hv => query_roots_mono G ι s t x (ω 0) he (hp v hv)) _

variable [BEq V] [LawfulBEq V]

theorem classicalExplore_eraseDups (s : State (V := V) (E := E) (I := I))
    (order : List V) (ω : ℕ → Driver G) :
    classicalExplore G ι s order.eraseDups ω = classicalExplore G ι s order ω := by
  have main : ∀ n : ℕ, ∀ order : List V, order.length = n →
      ∀ s ω, classicalExplore G ι s order.eraseDups ω = classicalExplore G ι s order ω := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro order hn s ω
      cases order with
      | nil => rfl
      | cons x xs =>
        let p : V → Bool := fun v => !v == x
        have hl : (xs.filter p).length < n := by
          have hf := List.length_filter_le p xs
          simp only [List.length_cons] at hn
          omega
        rw [List.eraseDups_cons]
        change classicalExplore G ι s (x :: (xs.filter p).eraseDups) ω = _
        by_cases hx : x ∈ s.roots
        · simp only [classicalExplore, if_pos hx]
          rw [ih _ hl _ rfl]
          apply classicalExplore_filter
          intro v hv
          have he : v = x := by simpa [p, bne] using hv
          exact he ▸ hx
        · simp only [classicalExplore, if_neg hx]
          cases he : query G ι s x (ω 0) with
          | none => rfl
          | some t =>
            simp only [Option.bind_some]
            rw [ih _ hl _ rfl]
            apply classicalExplore_filter
            intro v hv
            have heq : v = x := by simpa [p, bne] using hv
            exact heq ▸ query_start_mem G ι s t x (ω 0) he
  exact main order.length order rfl s ω

omit [Fintype V] in
theorem nodup_eraseDups (order : List V) : order.eraseDups.Nodup := by
  have main : ∀ n : ℕ, ∀ order : List V, order.length = n → order.eraseDups.Nodup := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro order hn
      cases order with
      | nil => simp
      | cons x xs =>
        rw [List.eraseDups_cons]
        apply List.nodup_cons.mpr
        constructor
        · simp
        · apply ih _ _ _ rfl
          have hf := List.length_filter_le (fun v => !v == x) xs
          simp only [List.length_cons] at hn
          omega
  exact main order.length order rfl

def classicalOrder (r : V) (order : List V) : List V :=
  order.eraseDups.filter (fun v => decide (v ≠ r))

omit [Fintype V] in
theorem classicalOrder_nodup (r : V) (order : List V) : (classicalOrder r order).Nodup :=
  (nodup_eraseDups order).filter _

omit [Fintype V] in
theorem mem_classicalOrder (r v : V) (order : List V) :
    v ∈ classicalOrder r order ↔ v ∈ order ∧ v ≠ r := by simp [classicalOrder]

omit [Fintype V] in
theorem classicalOrder_spanning (r : V) (order : List V) (horder : ∀ v, v = r ∨ v ∈ order) :
    ∀ v, v ∈ classicalOrder r order ↔ v ≠ r := by
  intro v
  rw [mem_classicalOrder]
  constructor
  · exact And.right
  · intro hv
    exact ⟨(horder v).resolve_left hv, hv⟩

theorem classicalExplore_normalize (r : V) (order : List V) (ω : ℕ → Driver G) :
    classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) (classicalOrder r order) ω =
      classicalExplore G ι (initialState ⟨{r}, Set.singleton_nonempty r⟩) order ω := by
  rw [classicalOrder, classicalExplore_filter G ι _ _ (fun v hv => by
    have he : v = r := by simpa using hv
    exact he ▸ Set.mem_singleton r)]
  exact classicalExplore_eraseDups G ι _ order ω

end
end FiniteAvalanches.Wilson.CopiedNetwork
