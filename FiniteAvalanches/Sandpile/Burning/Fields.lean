module

public import FiniteAvalanches.Sandpile.Burning.Characterization

@[expose] public section

/-! The field bijection precedes any recurrence, tree-count, or probability input.
Inner heights are unchanged. Outer heights subtract the original incident copies
entering A; reconstruction adds exactly those copies on the entire outer carrier. -/
namespace FiniteAvalanches.Sandpile.Burning
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (U : Finset V)

abbrev InnerField (B A : Finset (InducedVertex U)) :=
  (x : {x : InducedVertex U // x ∈ A}) →
    Fin (if x.val ∈ B then degree G x.val.val else activeDegree G U A x.val)
abbrev OuterField (A : Finset (InducedVertex U)) :=
  (x : {x : InducedVertex U // x ∉ A}) →
    Fin (degree G x.val.val - activeDegree G U A x.val)

def InnerAllowed (B A : Finset (InducedVertex U)) (a : InnerField G U B A) : Prop :=
  ∀ H (hHA : H ⊆ A), ¬(H.Nonempty ∧ ∀ x (hx : x ∈ H),
    (a ⟨x, hHA hx⟩).val < activeDegree G U H x)
def OuterAllowed (A : Finset (InducedVertex U)) (d : OuterField G U A) : Prop :=
  ∀ H (hHD : H ⊆ Finset.univ \ A), ¬(H.Nonempty ∧ ∀ x (hx : x ∈ H),
    (d ⟨x, (Finset.mem_sdiff.mp (hHD hx)).2⟩).val < activeDegree G U H x)

abbrev HeldFiber (hB : Finset (InducedVertex U)) (A : Finset (InducedVertex U)) :=
  {h : Heights G U // noForbidden G U h ∧ heldBurning G U h hB = A}

def assemble (B A : Finset (InducedVertex U))
    (a : InnerField G U B A) (d : OuterField G U A) : Heights G U := fun x =>
  if hx : x ∈ A then
    ⟨(a ⟨x, hx⟩).val, by
      have hi := (a ⟨x, hx⟩).isLt
      by_cases hb : x ∈ B
      · simpa only [if_pos hb] using hi
      · simp only [if_neg hb] at hi
        exact lt_of_lt_of_le hi (degree_into_le_degree G (A.image Subtype.val) x.val)⟩
  else
    ⟨(d ⟨x, hx⟩).val + activeDegree G U A x, by
      have hi := (d ⟨x, hx⟩).isLt
      change (d ⟨x, hx⟩).val < degree G x.val - activeDegree G U A x at hi
      omega⟩

theorem assemble_inside (B A : Finset (InducedVertex U))
    (a : InnerField G U B A) (d : OuterField G U A)
    (x : InducedVertex U) (hx : x ∈ A) :
    (assemble G U B A a d x).val = (a ⟨x, hx⟩).val := by simp [assemble, hx]
theorem assemble_outside (B A : Finset (InducedVertex U))
    (a : InnerField G U B A) (d : OuterField G U A)
    (x : InducedVertex U) (hx : x ∉ A) :
    (assemble G U B A a d x).val = (d ⟨x, hx⟩).val + activeDegree G U A x := by
  simp [assemble, hx]

def splitField (B A : Finset (InducedVertex U)) (hBA : B ⊆ A)
    (h : HeldFiber G U B A) :
    {a : InnerField G U B A // InnerAllowed G U B A a} ×
      {d : OuterField G U A // OuterAllowed G U A d} := by
  have hc := (held_field_iff G U h.val B A hBA).mp h.property
  let a : InnerField G U B A := fun x => ⟨(h.val x.val).val, by
    by_cases hb : x.val ∈ B
    · simpa only [if_pos hb] using (h.val x.val).isLt
    · simpa only [if_neg hb] using hc.1 x.val x.property hb⟩
  let d : OuterField G U A := fun x => ⟨(h.val x.val).val - activeDegree G U A x.val, by
    have hl := hc.2.2.1 x.val x.property
    have hh := (h.val x.val).isLt
    omega⟩
  exact (⟨a, fun H hHA => hc.2.1 H hHA⟩, ⟨d, fun H hHD => hc.2.2.2 H hHD⟩)

theorem assemble_mem (B A : Finset (InducedVertex U)) (hBA : B ⊆ A)
    (a : {a : InnerField G U B A // InnerAllowed G U B A a})
    (d : {d : OuterField G U A // OuterAllowed G U A d}) :
    noForbidden G U (assemble G U B A a.val d.val) ∧
      heldBurning G U (assemble G U B A a.val d.val) B = A := by
  apply (held_field_iff G U _ B A hBA).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hb
    rw [assemble_inside G U B A a.val d.val x hx]
    simpa only [if_neg hb] using (a.val ⟨x, hx⟩).isLt
  · intro H hHA hf
    apply a.property H hHA
    refine ⟨hf.1, ?_⟩
    intro x hx
    simpa only [assemble_inside G U B A a.val d.val x (hHA hx)] using hf.2 x hx
  · intro x hx
    rw [assemble_outside G U B A a.val d.val x hx]
    omega
  · intro H hHD hf
    apply d.property H hHD
    refine ⟨hf.1, ?_⟩
    intro x hx
    have hh := hf.2 x hx
    rw [assemble_outside G U B A a.val d.val x (Finset.mem_sdiff.mp (hHD hx)).2] at hh
    simpa using hh

def joinField (B A : Finset (InducedVertex U)) (hBA : B ⊆ A)
    (p : {a : InnerField G U B A // InnerAllowed G U B A a} ×
      {d : OuterField G U A // OuterAllowed G U A d}) : HeldFiber G U B A :=
  ⟨assemble G U B A p.1.val p.2.val, assemble_mem G U B A hBA p.1 p.2⟩

/-- Deterministic two-phase field equivalence, without a recurrence or tree-law bridge. -/
def heldFieldEquiv (B A : Finset (InducedVertex U)) (hBA : B ⊆ A) :
    HeldFiber G U B A ≃
      ({a : InnerField G U B A // InnerAllowed G U B A a} ×
        {d : OuterField G U A // OuterAllowed G U A d}) where
  toFun := splitField G U B A hBA
  invFun := joinField G U B A hBA
  left_inv h := by
    apply Subtype.ext
    funext x
    apply Fin.ext
    by_cases hx : x ∈ A
    · simp [joinField, splitField, assemble, hx]
    · have hlo := ((held_field_iff G U h.val B A hBA).mp h.property).2.2.1 x hx
      simp [joinField, splitField, assemble, hx, Nat.sub_add_cancel hlo]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      apply Fin.ext
      simp [splitField, joinField, assemble]
    · apply Subtype.ext
      funext x
      apply Fin.ext
      simp [splitField, joinField, assemble, x.property]

end
end FiniteAvalanches.Sandpile.Burning
