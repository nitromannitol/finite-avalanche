import FiniteAvalanches.Electrical.Trees.GrovePartition
import FiniteAvalanches.Electrical.Trees.PairingGroves

/-! Exact original-copy transport to the actual canonical Kenyon--Wilson grove carrier. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (J : CopiedGraph V E)

/-- `v` pairs with `d`, `u` with `a`, and `b` with `c`. -/
def pathPairing : Equiv.Perm (Fin 3) where
  toFun := ![2,0,1]
  invFun := ![1,2,0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- No edge IDs, component supports, or coincident terminals are changed. -/
def pathGrovePairingEquiv (u a b c d v : V) :
    PathGrove J u a b c d v ≃ J.PairingGrove ![v,u,b] ![a,c,d] pathPairing :=
  Equiv.subtypeEquivRight (fun F => by
    constructor
    · intro h
      have ht := (pathGroveTerminalEquiv J u a b c d v ⟨F,h⟩).property.2.2
      change ∀ i j, J.reaches F (pathTerminals u a b c d v i)
        (pathTerminals u a b c d v j) ↔ pairClass i = pairClass j at ht
      let α : Fin 3 → Fin 6 := ![0,1,3]
      let β : Fin 3 → Fin 6 := ![2,4,5]
      have hα (i : Fin 3) : pathTerminals u a b c d v (α i) = (![v,u,b] : Fin 3 → V) i := by
        fin_cases i <;> rfl
      have hβ (i : Fin 3) : pathTerminals u a b c d v (β i) = (![a,c,d] : Fin 3 → V) i := by
        fin_cases i <;> rfl
      have hc (i j : Fin 3) : pairClass (α i) = pairClass (β j) ↔ j = pathPairing i := by
        revert i j; decide
      have hαc (i : Fin 3) : pairClass (α i) = i := by fin_cases i <;> rfl
      refine ⟨h.1,?_,?_,?_⟩
      · intro y
        rcases h.2.1 y with ha | hb | hd
        · exact ⟨0,Or.inr ha⟩
        · exact ⟨2,Or.inl hb⟩
        · exact ⟨2,Or.inr hd⟩
      · intro i j
        simpa only [hα,hβ] using (ht (α i) (β j)).trans (hc i j)
      · intro i j hij hr
        have ht' := (ht (α i) (α j)).mp (by simpa only [hα] using hr)
        exact hij (by simpa only [hαc] using ht')
    · intro h
      have va : J.reaches F v d := (h.2.2.1 0 2).mpr rfl
      have ua : J.reaches F u a := (h.2.2.1 1 0).mpr rfl
      have bc : J.reaches F b c := (h.2.2.1 2 1).mpr rfl
      refine ⟨h.1,?_,?_,?_,?_,ua,bc,reaches_symm J va⟩
      · intro y
        obtain ⟨i,hi⟩ := h.2.1 y
        fin_cases i
        · rcases hi with hv | ha
          · exact Or.inr (Or.inr (hv.trans va))
          · exact Or.inl ha
        · rcases hi with hu | hc
          · exact Or.inl (hu.trans ua)
          · exact Or.inr (Or.inl (hc.trans (reaches_symm J bc)))
        · rcases hi with hb | hd
          · exact Or.inr (Or.inl hb)
          · exact Or.inr (Or.inr hd)
      · intro hab
        exact h.2.2.2 1 2 (by decide) (ua.trans hab)
      · intro had
        exact h.2.2.2 1 0 (by decide) ((ua.trans had).trans (reaches_symm J va))
      · intro hbd
        exact h.2.2.2 2 0 (by decide) (hbd.trans (reaches_symm J va)))

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph.TwoCopy
