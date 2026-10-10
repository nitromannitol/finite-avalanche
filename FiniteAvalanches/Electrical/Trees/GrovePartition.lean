import FiniteAvalanches.Electrical.Trees.TwoCopyGroves

/-! The literal path-grove carrier is exactly the six-terminal partition 16|23|45. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
open scoped Classical
noncomputable section
variable {V E : Type} (J : CopiedGraph V E)

/-- Source terminal ordering `(v,u,a,b,c,d)`. -/
def pathTerminals (u a b c d v : V) : Fin 6 → V := ![v,u,a,b,c,d]
/-- The actual terminal blocks 16, 23, 45. -/
def pairClass : Fin 6 → Fin 3 := ![0,1,1,2,2,0]

/-- Complete forest support and EVERY terminal relation, with no distinct-terminal premise. -/
abbrev TerminalGrove (x : Fin 6 → V) := {F : Finset E //
  (∀ e ∈ F, ¬J.reaches (F.erase e) (J.left e) (J.right e)) ∧
  (∀ y, ∃ i, J.reaches F y (x i)) ∧
  (∀ i j, J.reaches F (x i) (x j) ↔ pairClass i = pairClass j)}

/-- The three-component description and the exact source terminal-partition carrier coincide. -/
def pathGroveTerminalEquiv (u a b c d v : V) :
    PathGrove J u a b c d v ≃ TerminalGrove J (pathTerminals u a b c d v) :=
  Equiv.subtypeEquivRight (fun F => by
    constructor
    · intro h
      let roots : Fin 3 → V := ![d,a,b]
      have hr (i : Fin 6) : J.reaches F (pathTerminals u a b c d v i) (roots (pairClass i)) := by
        fin_cases i
        · exact reaches_symm J h.2.2.2.2.2.2.2
        · exact h.2.2.2.2.2.1
        · exact .refl
        · exact .refl
        · exact reaches_symm J h.2.2.2.2.2.2.1
        · exact .refl
      have sep (i j : Fin 3) (hne : i ≠ j) : ¬J.reaches F (roots i) (roots j) := by
        fin_cases i <;> fin_cases j <;> first
        | exact (hne rfl).elim
        | exact h.2.2.1
        | exact h.2.2.2.1
        | exact h.2.2.2.2.1
        | exact fun hh => h.2.2.1 (reaches_symm J hh)
        | exact fun hh => h.2.2.2.1 (reaches_symm J hh)
        | exact fun hh => h.2.2.2.2.1 (reaches_symm J hh)
      refine ⟨h.1,?_,?_⟩
      · intro y
        rcases h.2.1 y with ha | hb | hd
        · exact ⟨2,ha⟩
        · exact ⟨3,hb⟩
        · exact ⟨5,hd⟩
      · intro i j
        constructor
        · intro hij
          by_contra hne
          exact sep (pairClass i) (pairClass j) hne
            (((reaches_symm J (hr i)).trans hij).trans (hr j))
        · intro hij
          have h := hr i
          rw [hij] at h
          exact h.trans (reaches_symm J (hr j))
    · intro h
      have ua : J.reaches F u a := (h.2.2 1 2).mpr rfl
      have bc : J.reaches F b c := (h.2.2 3 4).mpr rfl
      have dv : J.reaches F d v := (h.2.2 5 0).mpr rfl
      refine ⟨h.1,?_,?_,?_,?_,ua,bc,dv⟩
      · intro y
        obtain ⟨i,hi⟩ := h.2.1 y
        fin_cases i
        · exact Or.inr (Or.inr (hi.trans (reaches_symm J dv)))
        · exact Or.inl (hi.trans ua)
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inl (hi.trans (reaches_symm J bc)))
        · exact Or.inr (Or.inr hi)
      · exact fun hh => (by decide : pairClass 2 ≠ pairClass 3) ((h.2.2 2 3).mp hh)
      · exact fun hh => (by decide : pairClass 2 ≠ pairClass 5) ((h.2.2 2 5).mp hh)
      · exact fun hh => (by decide : pairClass 3 ≠ pairClass 5) ((h.2.2 3 5).mp hh))

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
