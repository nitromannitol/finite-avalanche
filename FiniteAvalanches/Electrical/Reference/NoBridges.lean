import FiniteAvalanches.Electrical.Reference.Connected

/-! Copy-preserving cut bounds for the actual finite wired lattice quotient. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice

open LatticeProb
open FiniteAvalanches.Sandpile.FiniteWired (Direction step)
open scoped Classical
noncomputable section

/-- Original IDs crossing a finite set of lattice sites. -/
def latticeExits (S : Finset (Site 2)) : Finset OriginalCopy :=
  (domainCopies S).filter fun e =>
    (originalA e ∈ S ∧ originalB e ∉ S) ∨
    (originalB e ∈ S ∧ originalA e ∉ S)

theorem mem_latticeExits (S : Finset (Site 2)) (e : OriginalCopy) :
    e ∈ latticeExits S ↔
      (originalA e ∈ S ∧ originalB e ∉ S) ∨
      (originalB e ∈ S ∧ originalA e ∉ S) := by
  rw [latticeExits, Finset.mem_filter, mem_domainCopies]
  tauto

private theorem exists_direction_exit (S : Finset (Site 2)) (hS : S.Nonempty)
    (d : Direction) : ∃ x ∈ S, x + step d ∉ S := by
  rcases d with ⟨i,b⟩
  cases b with
  | false =>
    obtain ⟨x,hx,hmin⟩ := S.exists_min_image (fun x => x i) hS
    refine ⟨x,hx,?_⟩
    intro h
    have hh := hmin (x + step (i,false)) h
    simp only [step, Bool.false_eq_true, if_false, Pi.add_apply,
      Pi.neg_apply, unit, Pi.single_eq_same] at hh
    omega
  | true =>
    obtain ⟨x,hx,hmax⟩ := S.exists_max_image (fun x => x i) hS
    refine ⟨x,hx,?_⟩
    intro h
    have hh := hmax (x + step (i,true)) h
    simp only [step, if_true, Pi.add_apply, unit, Pi.single_eq_same] at hh
    omega

private theorem incidentID_mem_exits (S : Finset (Site 2))
    (x : Site 2) (d : Direction) (hx : x ∈ S) (hout : x + step d ∉ S) :
    incidentID x d ∈ latticeExits S := by
  rw [mem_latticeExits]
  rcases d with ⟨i,b⟩
  cases b with
  | false =>
    right
    simpa only [incidentID, if_false, originalA, originalB, sub_add_cancel,
      step, Bool.false_eq_true, if_false, ← sub_eq_add_neg] using And.intro hx hout
  | true =>
    left
    exact ⟨hx,hout⟩

/-- Four extremal exits have distinct original IDs, even after wiring. -/
theorem latticeExits_card_ge_four (S : Finset (Site 2)) (hS : S.Nonempty) :
    4 ≤ (latticeExits S).card := by
  let x : Direction → Site 2 := fun d => (exists_direction_exit S hS d).choose
  have hx (d : Direction) : x d ∈ S ∧ x d + step d ∉ S :=
    (exists_direction_exit S hS d).choose_spec
  let f : Direction → ↥(latticeExits S) := fun d =>
    ⟨incidentID (x d) d, incidentID_mem_exits S (x d) d (hx d).1 (hx d).2⟩
  have hf : Function.Injective f := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    have he : incidentID (x (i,b)) (i,b) = incidentID (x (j,c)) (j,c) :=
      congrArg Subtype.val h
    have hij : i = j := congrArg Prod.snd he
    subst j
    cases b <;> cases c
    · rfl
    · have hp := congrArg Prod.fst he
      have hout := (hx (i,false)).2
      apply False.elim
      apply hout
      change x (i,false) - unit i = x (i,true) at hp
      simpa only [step, Bool.false_eq_true, if_false, ← sub_eq_add_neg, hp] using (hx (i,true)).1
    · have hp := congrArg Prod.fst he
      have hout := (hx (i,false)).2
      apply False.elim
      apply hout
      change x (i,true) = x (i,false) - unit i at hp
      simpa only [step, Bool.false_eq_true, if_false, ← sub_eq_add_neg, ← hp] using (hx (i,true)).1
    · rfl
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Direction, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.reduceMul, Fintype.card_coe] using hh

end
end FiniteAvalanches.Electrical.Plane.SourceLattice
