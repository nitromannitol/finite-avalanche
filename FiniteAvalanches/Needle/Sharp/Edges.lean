import FiniteAvalanches.Needle.Energy

set_option autoImplicit false
namespace Needle107Edges
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open scoped Classical

/-- Positive-coordinate base and axis of an original copied edge. -/
noncomputable def key (N : ℕ) : Edge N → Point × Fin 2
  | .inl e => (site e.val.1, e.property.choose)
  | .inr e => (if e.val.2.2 then site e.val.1 else site e.val.1 - unit e.val.2.1,
      e.val.2.1)

lemma site_inBox (N : ℕ) (x : Active N) : inBox N (site x) :=
  fun i => (x i).property

lemma exit_base_outside (N : ℕ) (x : Active N) (i : Fin 2)
    (he : ¬inBox N (site x + step (i, false))) :
    ¬inBox N (site x - unit i) := by
  simpa only [step, Bool.false_eq_true, if_false, sub_eq_add_neg] using he

lemma exit_top_outside (N : ℕ) (x : Active N) (i : Fin 2)
    (he : ¬inBox N (site x + step (i, true))) :
    ¬inBox N (site x + unit i) := by
  simpa only [step, if_true] using he

lemma interior_key_ne_exit (N : ℕ) (e : InteriorEdge N) (f : ExitEdge N) :
    key N (.inl e) ≠ key N (.inr f) := by
  rcases f with ⟨⟨x, i, b⟩, hf⟩
  cases b
  · intro hh
    have hb := congrArg Prod.fst hh
    change site e.val.1 = site x - unit i at hb
    exact exit_base_outside N x i hf (hb ▸ site_inBox N e.val.1)
  · intro hh
    have hb := congrArg Prod.fst hh
    have hi := congrArg Prod.snd hh
    change site e.val.1 = site x at hb
    change e.property.choose = i at hi
    have hu : site e.val.2 = site x + unit i := by
      exact e.property.choose_spec.trans (congrArg₂ (fun x i => x+unit i) hb hi)
    exact exit_top_outside N x i hf (hu ▸ site_inBox N e.val.2)

/-- No interior or exterior copy is identified by this geometric indexing. -/
theorem key_injective (N : ℕ) : Function.Injective (key N) := by
  intro e f hh
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have hb := congrArg Prod.fst hh
      have hi := congrArg Prod.snd hh
      change site e.val.1 = site f.val.1 at hb
      change e.property.choose = f.property.choose at hi
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · exact site_injective N hb
      · apply site_injective N
        exact e.property.choose_spec.trans
          ((congrArg₂ (fun x i => x + unit i) hb hi).trans f.property.choose_spec.symm)
    | inr f => exact (interior_key_ne_exit N e f hh).elim
  | inr e =>
    cases f with
    | inl f => exact (interior_key_ne_exit N f e hh.symm).elim
    | inr f =>
      rcases e with ⟨⟨x, i, b⟩, he⟩
      rcases f with ⟨⟨y, j, c⟩, hf⟩
      have hi := congrArg Prod.snd hh
      change i = j at hi
      subst j
      cases b <;> cases c
      · have hb := congrArg Prod.fst hh
        change site x - unit i = site y - unit i at hb
        have hxy := site_injective N (sub_left_inj.mp hb)
        apply congrArg Sum.inr
        apply Subtype.ext
        exact congrArg (fun z : Active N => (z, (i, false))) hxy
      · have hb := congrArg Prod.fst hh
        change site x - unit i = site y at hb
        exact (exit_base_outside N x i he (hb.symm ▸ site_inBox N y)).elim
      · have hb := congrArg Prod.fst hh
        change site x = site y - unit i at hb
        exact (exit_base_outside N y i hf (hb ▸ site_inBox N x)).elim
      · have hb := congrArg Prod.fst hh
        change site x = site y at hb
        have hxy := site_injective N hb
        apply congrArg Sum.inr
        apply Subtype.ext
        exact congrArg (fun z : Active N => (z, (i, true))) hxy

lemma key_adj (N : ℕ) (e : Edge N) :
    (lattice 2).Adj (key N e).1 ((key N e).1 + unit (key N e).2) :=
  ⟨(key N e).2, Or.inl rfl⟩

end Needle107Edges
