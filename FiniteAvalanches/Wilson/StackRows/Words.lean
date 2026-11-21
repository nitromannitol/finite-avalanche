import FiniteAvalanches.Wilson.UniformLetters
import FiniteAvalanches.Wilson.CyclePopping.StackReading

/-! Words of edge copies read by one copied walk. A driver realizes a finite word when
its walk reads exactly the listed copies and first meets the roots right after the last
one. These events are finite cylinders, and under independent uniform letters their mass
is the product of the inverse degrees along the word. On such an event the first-hit
attachment of the walk depends only on the word. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CopiedNetwork

open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V E I : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- The endpoint reached along a listed copy; an absent copy keeps the position. -/
def copyHead (v : V) : Option E → V
  | none => v
  | some e => if G.left e = v then G.right e else G.left e

/-- Positions and stack cursors along a finite word of copies. -/
def wordWalk (x : V) (k : Cursor V) (L : List E) : ℕ → V × Cursor V :=
  wordState (copyHead G) x k (fun i => L[i]?)

/-- Positions along a finite word of copies. -/
def wordPos (x : V) (L : List E) (n : ℕ) : V := (wordWalk G x 0 L n).1

theorem wordWalk_fst (x : V) (k : Cursor V) (L : List E) (n : ℕ) :
    (wordWalk G x k L n).1 = wordPos G x L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change copyHead G (wordWalk G x k L n).1 L[n]? = copyHead G (wordWalk G x 0 L n).1 L[n]?
    rw [ih]
    rfl

/-- The copy read at time `i` by the walk of a driver started at `x`. -/
def usedCopy (x : V) (ω : Driver G) (i : ℕ) : E := (ω i (position G x ω i)).val

theorem position_eq_wordPos (x : V) (ω : Driver G) (L : List E) (n : ℕ)
    (h : ∀ i < n, L[i]? = some (usedCopy G x ω i)) :
    position G x ω n = wordPos G x L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    change other G (position G x ω n) (ω n (position G x ω n)) =
      copyHead G (wordPos G x L n) L[n]?
    rw [h n (Nat.lt_succ_self n), ← ih']
    rfl

/-- Reading the letters at the word positions is the same as reading the used copies. -/
theorem usedCopy_iff_wordPos (x : V) (ω : Driver G) (L : List E) (n : ℕ) :
    (∀ i < n, L[i]? = some (usedCopy G x ω i)) ↔
      ∀ i < n, L[i]? = some (ω i (wordPos G x L i)).val := by
  constructor
  · intro h i hi
    rw [h i hi, usedCopy, position_eq_wordPos G x ω L i (fun j hj => h j (hj.trans hi))]
  · intro h i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rw [h i hi, usedCopy, position_eq_wordPos G x ω L i (fun j hj => ih j hj (hj.trans hi))]

/-- A word is valid for `R` from `x` when every listed copy is incident to the current
position, and the positions avoid `R` before the end of the word and lie in `R` at its end. -/
def ValidWord (R : Set V) (x : V) (L : List E) : Prop :=
  (∀ i < L.length, ∀ e, L[i]? = some e →
      G.left e = wordPos G x L i ∨ G.right e = wordPos G x L i) ∧
    wordPos G x L L.length ∈ R ∧ ∀ i < L.length, wordPos G x L i ∉ R

/-- The drivers whose walk reads the copies of `L` and first meets `R` right after them. -/
def rowCyl (R : Set V) (x : V) (L : List E) : Set (Driver G) :=
  {ω | (∀ i < L.length, L[i]? = some (usedCopy G x ω i)) ∧
    position G x ω L.length ∈ R ∧ ∀ i < L.length, position G x ω i ∉ R}

/-- A word event is the cylinder of the letters at the word positions, or empty. -/
theorem rowCyl_eq (R : Set V) (x : V) (L : List E) :
    rowCyl G R x L = {ω | ValidWord G R x L ∧
      ∀ i < L.length, L[i]? = some (ω i (wordPos G x L i)).val} := by
  ext ω
  constructor
  · rintro ⟨hw, hR, hav⟩
    have hp : ∀ n ≤ L.length, position G x ω n = wordPos G x L n := fun n hn =>
      position_eq_wordPos G x ω L n (fun i hi => hw i (Nat.lt_of_lt_of_le hi hn))
    refine ⟨⟨?_, ?_, ?_⟩, (usedCopy_iff_wordPos G x ω L L.length).mp hw⟩
    · intro i hi e he
      rw [hw i hi, Option.some.injEq] at he
      subst he
      rw [← hp i hi.le]
      exact (ω i (position G x ω i)).property
    · rw [← hp _ le_rfl]
      exact hR
    · intro i hi
      rw [← hp i hi.le]
      exact hav i hi
  · rintro ⟨⟨_, hR, hav⟩, hw⟩
    have hu := (usedCopy_iff_wordPos G x ω L L.length).mpr hw
    have hp : ∀ n ≤ L.length, position G x ω n = wordPos G x L n := fun n hn =>
      position_eq_wordPos G x ω L n (fun i hi => hu i (Nat.lt_of_lt_of_le hi hn))
    refine ⟨hu, ?_, ?_⟩
    · rw [hp _ le_rfl]
      exact hR
    · intro i hi
      rw [hp i hi.le]
      exact hav i hi

/-- Distinct words give disjoint events. -/
theorem rowCyl_disjoint (R : Set V) (x : V) :
    Pairwise (Function.onFun Disjoint (rowCyl G R x)) := by
  intro L L' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨hw, hR, hav⟩ ⟨hw', hR', hav'⟩
  have hlen : L.length = L'.length := by
    rcases lt_trichotomy L.length L'.length with h | h | h
    · exact absurd hR (hav' _ h)
    · exact h
    · exact absurd hR' (hav _ h)
  apply hne
  apply List.ext_getElem?
  intro i
  by_cases hi : i < L.length
  · rw [hw i hi, hw' i (hlen ▸ hi)]
  · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]

/-- A walk meets `R` exactly when it realizes some word. -/
theorem hits_iff_exists_rowCyl (R : Set V) (x : V) (ω : Driver G) :
    hits G R x ω ↔ ∃ L, ω ∈ rowCyl G R x L := by
  constructor
  · intro h
    refine ⟨(List.range (Nat.find h)).map (usedCopy G x ω), ?_, ?_, ?_⟩
    · intro i hi
      simp only [List.length_map, List.length_range] at hi
      simp [List.getElem?_map, List.getElem?_range hi]
    · simpa only [List.length_map, List.length_range] using Nat.find_spec h
    · intro i hi
      simp only [List.length_map, List.length_range] at hi
      exact Nat.find_min h hi
  · rintro ⟨L, _, hR, _⟩
    exact ⟨L.length, hR⟩

variable {G} in
/-- One step of a packed walk, depending only on the copy read at its endpoint. -/
private def stepFrom {x y : V} (q : Trace G x y) (c : Incident G y) : Σ b : V, Trace G x b :=
  letI := pathQuiver G
  ⟨other G y c, q.cons ⟨c.val, by
    rcases other_spec G y c with h | h
    · exact Or.inl (Prod.ext (congrArg ULift.up h.1) (congrArg ULift.up h.2))
    · exact Or.inr (Prod.ext (congrArg ULift.up h.2) (congrArg ULift.up h.1))⟩⟩

/-- A packed walk depends only on the copies it reads. -/
theorem packedPath_eq_of_used (x : V) (ω η : Driver G) (n : ℕ)
    (h : ∀ i < n, ω i (position G x ω i) = η i (position G x ω i)) :
    packedPath G x ω n = packedPath G x η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    change stepFrom (packedPath G x ω n).2 (ω n (packedPath G x ω n).1) =
      stepFrom (packedPath G x η n).2 (η n (packedPath G x η n).1)
    have hn' : ω n (packedPath G x ω n).1 = η n (packedPath G x ω n).1 := hn
    rw [hn']
    exact congrArg (fun p : Σ b : V, Trace G x b => stepFrom p.2 (η n p.1)) ih'

/-- Positions depend only on the copies read. -/
theorem position_eq_of_used (x : V) (ω η : Driver G) (n : ℕ)
    (h : ∀ i < n, ω i (position G x ω i) = η i (position G x ω i)) :
    position G x ω n = position G x η n :=
  congrArg Sigma.fst (packedPath_eq_of_used G x ω η n h)

variable {G} in
/-- Two drivers realizing the same word read the same copies along it. -/
theorem used_eq_of_mem_rowCyl {R : Set V} {x : V} {L : List E} {ω η : Driver G}
    (hω : ω ∈ rowCyl G R x L) (hη : η ∈ rowCyl G R x L) :
    ∀ i < L.length, ω i (position G x ω i) = η i (position G x ω i) := by
  rw [rowCyl_eq] at hω hη
  intro i hi
  have hp : position G x ω i = wordPos G x L i :=
    position_eq_wordPos G x ω L i (fun j hj =>
      ((usedCopy_iff_wordPos G x ω L L.length).mpr hω.2) j (hj.trans hi))
  rw [hp]
  apply Subtype.ext
  have h1 := hω.2 i hi
  have h2 := hη.2 i hi
  rw [h1, Option.some.injEq] at h2
  exact h2

variable (ι : E ↪ I)

/-- The first-hit attachment depends only on the copies read before the hit. -/
theorem attachAt_eq_of_used (s : State (V := V) (E := E) (I := I)) (x : V) (ω η : Driver G)
    (n : ℕ) (h : ∀ i < n, ω i (position G x ω i) = η i (position G x ω i)) :
    attachAt G ι s x ω n = attachAt G ι s x η n := by
  apply State.ext
  all_goals dsimp only [attachAt]; rw [packedPath_eq_of_used G x ω η n h]

/-- On a word event the query attaches the walk stopped at the end of the word. -/
theorem query_of_mem_rowCyl (s : State (V := V) (E := E) (I := I)) (x : V)
    (hx : x ∉ s.roots) (L : List E) (ω : Driver G) (hω : ω ∈ rowCyl G s.roots x L) :
    query G ι s x ω = some (attachAt G ι s x ω L.length) := by
  have hh : hits G s.roots x ω := ⟨L.length, hω.2.1⟩
  have hf : Nat.find hh = L.length :=
    (Nat.find_eq_iff hh).mpr ⟨hω.2.1, fun n hn => hω.2.2 n hn⟩
  rw [query, if_neg hx, dif_pos hh, hf]

/-- Without a hit the query fails. -/
theorem query_of_not_hits (s : State (V := V) (E := E) (I := I)) (x : V)
    (hx : x ∉ s.roots) (ω : Driver G) (hω : ¬ hits G s.roots x ω) :
    query G ι s x ω = none := by
  rw [query, if_neg hx, dif_neg hω]

/-- The state attached by a walk realizing the word `L`. -/
def wordAttach (s : State (V := V) (E := E) (I := I)) (x : V) (L : List E) :
    State (V := V) (E := E) (I := I) :=
  if h : (rowCyl G s.roots x L).Nonempty then attachAt G ι s x h.some L.length else s

/-- Every driver realizing a word attaches the same state. -/
theorem query_eq_wordAttach (s : State (V := V) (E := E) (I := I)) (x : V)
    (hx : x ∉ s.roots) (L : List E) (ω : Driver G) (hω : ω ∈ rowCyl G s.roots x L) :
    query G ι s x ω = some (wordAttach G ι s x L) := by
  have hne : (rowCyl G s.roots x L).Nonempty := ⟨ω, hω⟩
  rw [query_of_mem_rowCyl G ι s x hx L ω hω, wordAttach, dif_pos hne]
  congr 1
  exact attachAt_eq_of_used G ι s x ω hne.some L.length
    (used_eq_of_mem_rowCyl hω hne.some_mem)

variable [Nontrivial V] (hconn : ∀ x y, G.reaches Finset.univ x y)

/-- A single incident copy has the inverse-degree mass under uniform letters. -/
theorem uniformLetterLaw_copy (v : V) (e : E) (he : G.left e = v ∨ G.right e = v) :
    uniformLetterLaw G hconn {a | (a v).val = e} = (Nat.card (Incident G v) : ℝ≥0∞)⁻¹ := by
  letI : ∀ w : V, MeasurableSpace (Incident G w) := fun _ => ⊤
  letI : ∀ w : V, MeasurableSingletonClass (Incident G w) := fun _ => ⟨fun _ => trivial⟩
  have hs : {a : Letter G | (a v).val = e} = (fun a => a v) ⁻¹' {⟨e, he⟩} := by
    ext a
    simp [Subtype.ext_iff]
  rw [hs, ← Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    uniformLetterLaw_eval, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    unitCopyPMF_apply, Nat.card_eq_fintype_card]

/-- The mass of a word event is the product of inverse degrees along a valid word. -/
theorem driverLaw_rowCyl (R : Set V) (x : V) (L : List E) :
    driverLaw G (uniformLetterLaw G hconn) (rowCyl G R x L) =
      if ValidWord G R x L then
        ∏ i ∈ Finset.range L.length, (Nat.card (Incident G (wordPos G x L i)) : ℝ≥0∞)⁻¹
      else 0 := by
  rw [rowCyl_eq]
  split_ifs with hv
  · have hs : {ω : Driver G | ValidWord G R x L ∧
        ∀ i < L.length, L[i]? = some (ω i (wordPos G x L i)).val} =
        Set.pi (Finset.range L.length : Set ℕ)
          (fun i => {a : Letter G | L[i]? = some (a (wordPos G x L i)).val}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio, hv, true_and]
    rw [hs, driverLaw, Measure.infinitePi_pi]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      obtain ⟨e, he⟩ : ∃ e, L[i]? = some e := ⟨L[i], List.getElem?_eq_getElem hi'⟩
      have hset : {a : Letter G | L[i]? = some (a (wordPos G x L i)).val} =
          {a | (a (wordPos G x L i)).val = e} := by
        ext a
        simp only [Set.mem_setOf_eq, he, Option.some.injEq]
        exact eq_comm
      rw [hset, uniformLetterLaw_copy G hconn _ e (hv.1 i hi' e he)]
    · intro i _
      exact (Set.toFinite _).measurableSet
  · have hs : {ω : Driver G | ValidWord G R x L ∧
        ∀ i < L.length, L[i]? = some (ω i (wordPos G x L i)).val} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hv
    rw [hs, measure_empty]

end
end FiniteAvalanches.Wilson.CopiedNetwork
