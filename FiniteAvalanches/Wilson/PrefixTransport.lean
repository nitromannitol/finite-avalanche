import FiniteAvalanches.Wilson.PrefixLaw

/-! Complete copied prefixes determine chronological path erasure and first-hit
operations. No representative driver is chosen for an unrealizable prefix. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open Quiver MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
open scoped Classical ENNReal
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

theorem walkPrefix_length (x : V) (ω : Driver G) (n : ℕ) :
    (walkPrefix G x ω n).2.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [walkPrefix, prefixStep, List.length_append, List.length_singleton, ih]

theorem walkPrefix_eq_of_steps_eq (x : V) (ω η : Driver G) (n : ℕ)
    (h : (walkPrefix G x ω n).2 = (walkPrefix G x η n).2) :
    walkPrefix G x ω n = walkPrefix G x η n := by
  apply Prod.ext _ h
  cases n with
  | zero => rfl
  | succ n =>
    have he := congrArg (fun l : List (V × E) => l.getLast?.map Prod.fst) h
    simpa [walkPrefix, prefixStep] using he

theorem walkPrefix_prev (x : V) (ω η : Driver G) (n : ℕ)
    (h : walkPrefix G x ω (n + 1) = walkPrefix G x η (n + 1)) :
    walkPrefix G x ω n = walkPrefix G x η n := by
  apply walkPrefix_eq_of_steps_eq
  apply List.append_inj_left (congrArg Prod.snd h)
  rw [walkPrefix_length, walkPrefix_length]

theorem walkPrefix_eq_of_le (x : V) (ω η : Driver G) {n : ℕ}
    (h : walkPrefix G x ω n = walkPrefix G x η n) (k : ℕ) (hk : k ≤ n) :
    walkPrefix G x ω k = walkPrefix G x η k := by
  induction n with
  | zero => have he : k = 0 := Nat.eq_zero_of_le_zero hk; subst k; rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hk with he | hl
    · exact he ▸ h
    · exact ih (walkPrefix_prev G x ω η n h) (Nat.le_of_lt_succ hl)

private def incidentArrow (v : V) (e : Incident G v) :
    @Quiver.Hom (ULift.{0} V) (pathQuiver G) (ULift.up v) (ULift.up (other G v e)) :=
  ⟨e.val, by
    rcases other_spec G v e with h | h
    · exact Or.inl (Prod.ext (congrArg ULift.up h.1) (congrArg ULift.up h.2))
    · exact Or.inr (Prod.ext (congrArg ULift.up h.2) (congrArg ULift.up h.1))⟩

private def extendPath {x : V} (p : Σ b : V, Trace G x b) (e : Incident G p.1) : Σ b : V, Trace G x b :=
  letI := pathQuiver G
  ⟨other G p.1 e, p.2.cons (incidentArrow G p.1 e)⟩

theorem packedPath_eq_of_walkPrefix_eq (x : V) (ω η : Driver G) (n : ℕ)
    (h : walkPrefix G x ω n = walkPrefix G x η n) : packedPath G x ω n = packedPath G x η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := walkPrefix_prev G x ω η n h
    have hv : position G x ω n = position G x η n := by
      simpa only [walkPrefix_terminal] using congrArg Prod.fst hp
    have hc := List.append_inj_right (congrArg Prod.snd h)
      (by rw [walkPrefix_length, walkPrefix_length])
    have he : (ω n (position G x ω n)).val = (η n (position G x ω n)).val := by
      have he' := congrArg (fun l : List (V × E) => l.head?.map Prod.snd) hc
      dsimp only [prefixStep, List.head?_cons, Option.map_some] at he'
      rw [walkPrefix_terminal, walkPrefix_terminal, ← hv] at he'
      exact Option.some.inj he'
    change extendPath G (packedPath G x ω n) (ω n (packedPath G x ω n).1) =
      extendPath G (packedPath G x η n) (η n (packedPath G x η n).1)
    rw [ih hp]
    apply congrArg (extendPath G (packedPath G x η n))
    apply Subtype.ext
    change (ω n (position G x η n)).val = (η n (position G x η n)).val
    rw [← hv]
    exact he


variable {I : Type} (ι : E ↪ I)

theorem attachAt_eq_of_walkPrefix_eq (s : State (V := V) (E := E) (I := I))
    (x : V) (ω η : Driver G) (n : ℕ) (h : walkPrefix G x ω n = walkPrefix G x η n) :
    attachAt G ι s x ω n = attachAt G ι s x η n := by
  apply State.ext
  all_goals dsimp only [attachAt]; rw [packedPath_eq_of_walkPrefix_eq G x ω η n h]

def firstHitAt (B : Set V) (x : V) (ω : Driver G) (n : ℕ) : Prop :=
  position G x ω n ∈ B ∧ ∀ k < n, position G x ω k ∉ B

theorem firstHitAt_unique (B : Set V) (x : V) (ω : Driver G) {n m : ℕ}
    (hn : firstHitAt G B x ω n) (hm : firstHitAt G B x ω m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact False.elim (hm.2 n h hn.1)
  · exact h
  · exact False.elim (hn.2 m h hm.1)

theorem firstHitAt_iff_find (B : Set V) (x : V) (ω : Driver G) (n : ℕ) :
    firstHitAt G B x ω n ↔ ∃ h : hits G B x ω, Nat.find h = n := by
  constructor
  · intro hn
    have hh : hits G B x ω := ⟨n, hn.1⟩
    exact ⟨hh, (Nat.find_eq_iff hh).mpr ⟨hn.1, hn.2⟩⟩
  · rintro ⟨hh, rfl⟩
    exact ⟨Nat.find_spec hh, fun k hk => Nat.find_min hh hk⟩

theorem firstHitAt_eq_of_walkPrefix_eq (B : Set V) (x : V) (ω η : Driver G) (n : ℕ)
    (h : walkPrefix G x ω n = walkPrefix G x η n) :
    firstHitAt G B x ω n ↔ firstHitAt G B x η n := by
  have hv (k : ℕ) (hk : k ≤ n) : position G x ω k = position G x η k := by
    simpa only [walkPrefix_terminal] using congrArg Prod.fst (walkPrefix_eq_of_le G x ω η h k hk)
  simp only [firstHitAt, hv n le_rfl]
  exact and_congr_right (fun _ => forall_congr' fun k => forall_congr' fun hk => by rw [hv k hk.le])

end
end FiniteAvalanches.Wilson.CopiedNetwork
