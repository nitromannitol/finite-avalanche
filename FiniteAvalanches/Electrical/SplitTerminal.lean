import FiniteAvalanches.Electrical.Network
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Splitting a vertex while retaining the literal finite edge-copy carrier. -/

namespace FiniteAvalanches.Electrical

open scoped BigOperators Classical

variable {V E : Type*} [Fintype E]

/-- Replace the distinguished vertex by two distinct terminals. -/
abbrev SplitVertex (alpha : V) := {x : V // x ≠ alpha} ⊕ Bool

/-- Collapse both copies of the terminal to the original vertex. -/
def collapse (alpha : V) : SplitVertex alpha → V
  | Sum.inl x => x.val
  | Sum.inr _ => alpha

/-- `side e` specifies which copy receives an incidence at `alpha`. -/
noncomputable def splitEndpoint (alpha : V) (side : E → Bool)
    (v : V) (e : E) : SplitVertex alpha :=
  if hv : v = alpha then Sum.inr (side e) else Sum.inl ⟨v, hv⟩

omit [Fintype E] in
@[simp] theorem collapse_splitEndpoint (alpha : V) (side : E → Bool) (v : V) (e : E) :
    collapse alpha (splitEndpoint alpha side v e) = v := by
  unfold splitEndpoint
  split_ifs with hv
  · exact hv.symm
  · rfl

omit [Fintype E] in
@[simp] theorem splitEndpoint_eq_inl (alpha : V) (side : E → Bool)
    (v : V) (e : E) (x : {x : V // x ≠ alpha}) :
    splitEndpoint alpha side v e = Sum.inl x ↔ v = x.val := by
  unfold splitEndpoint
  split_ifs with hv
  · simp only [false_iff]
    exact fun h => x.property (h.symm.trans hv)
  · simp only [Sum.inl.injEq, Subtype.ext_iff]

/-- No edge copy is removed, added, or identified. -/
theorem split_energy_pullback (a b : E → V) (alpha : V) (side : E → Bool) (f : V → ℝ) :
    energy (fun e => splitEndpoint alpha side (a e) e)
      (fun e => splitEndpoint alpha side (b e) e) (fun x => f (collapse alpha x)) =
      energy a b f := by
  unfold energy
  simp only [collapse_splitEndpoint]

omit [Fintype E] in
theorem split_endpoint_ne (a b : E → V) (alpha : V) (side : E → Bool)
    (he : ∀ e, a e ≠ b e) (e : E) :
    splitEndpoint alpha side (a e) e ≠ splitEndpoint alpha side (b e) e := by
  intro h
  have hc := congrArg (collapse alpha) h
  exact he e (by simpa only [collapse_splitEndpoint] using hc)

/-- Pulling back the old voltage preserves its free-vertex Laplacian exactly. -/
theorem split_laplacian_inl (a b : E → V) (alpha : V) (side : E → Bool)
    (f : V → ℝ) (x : {x : V // x ≠ alpha}) :
    laplacian (fun e => splitEndpoint alpha side (a e) e)
      (fun e => splitEndpoint alpha side (b e) e) (fun y => f (collapse alpha y))
      (Sum.inl x) = laplacian a b f x.val := by
  unfold laplacian
  simp only [collapse_splitEndpoint, splitEndpoint_eq_inl]
  rfl

omit [Fintype E] in
/-- Every split component still reaches one of the two copies of the old terminal. -/
theorem split_reachable_terminal (a b : E → V) (alpha : V) (side : E → Bool)
    (hc : (supportGraph a b).Preconnected) (x : SplitVertex alpha) :
    ∃ k : Bool, (supportGraph (fun e => splitEndpoint alpha side (a e) e)
      (fun e => splitEndpoint alpha side (b e) e)).Reachable x (Sum.inr k) := by
  let G := supportGraph (fun e => splitEndpoint alpha side (a e) e)
    (fun e => splitEndpoint alpha side (b e) e)
  have hwalk {u : V} (p : (supportGraph a b).Walk u alpha) :
      ∀ hu : u ≠ alpha, ∃ k : Bool, G.Reachable (Sum.inl ⟨u, hu⟩) (Sum.inr k) := by
    induction p with
    | nil => intro hu; exact (hu rfl).elim
    | @cons u v alpha huv p ih =>
      intro hu
      obtain ⟨hne, e, he⟩ := huv
      have hsplit : G.Adj (splitEndpoint alpha side u e) (splitEndpoint alpha side v e) := by
        refine ⟨?_, e, ?_⟩
        · intro h
          exact hne (by simpa only [collapse_splitEndpoint] using congrArg (collapse alpha) h)
        · rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩
          · exact Or.inl ⟨congrArg (fun v => splitEndpoint alpha side v e) ha,
              congrArg (fun v => splitEndpoint alpha side v e) hb⟩
          · exact Or.inr ⟨congrArg (fun v => splitEndpoint alpha side v e) hb,
              congrArg (fun v => splitEndpoint alpha side v e) ha⟩
      have hsu : splitEndpoint alpha side u e = Sum.inl ⟨u, hu⟩ :=
        (splitEndpoint_eq_inl alpha side u e ⟨u, hu⟩).mpr rfl
      rw [hsu] at hsplit
      by_cases hv : v = alpha
      · subst v
        have hsv : splitEndpoint alpha side alpha e = Sum.inr (side e) := by
          simp [splitEndpoint]
        rw [hsv] at hsplit
        exact ⟨side e, hsplit.reachable⟩
      · obtain ⟨k, hk⟩ := ih x hv
        have hsv : splitEndpoint alpha side v e = Sum.inl ⟨v, hv⟩ :=
          (splitEndpoint_eq_inl alpha side v e ⟨v, hv⟩).mpr rfl
        rw [hsv] at hsplit
        exact ⟨k, hsplit.reachable.trans hk⟩
  rcases x with x | k
  · obtain ⟨p⟩ := hc x.val alpha
    exact hwalk p x.property
  · exact ⟨k, SimpleGraph.Reachable.refl _⟩

end FiniteAvalanches.Electrical
