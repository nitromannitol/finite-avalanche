import FiniteAvalanches.Electrical.ChordSplit.CopiedDiagram
import FiniteAvalanches.Electrical.ChordSplit.TotalResponse

/-! Identifying the two zero terminals preserves the attained total response energy. -/
namespace FiniteAvalanches.Electrical.ChordSplit
open scoped Classical BigOperators
open FiniteAvalanches.Electrical.StatementGeometry
noncomputable section
variable {V E : Type}

/-- Identifications transport copied reachability even when some copies become loops. -/
theorem mapped_copies_reachable {W : Type} (a b : E → V) (q : V → W) {x y : V}
    (h : (supportGraph a b).Reachable x y) :
    (supportGraph (fun e => q (a e)) (fun e => q (b e))).Reachable (q x) (q y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | @cons x y z h p ih =>
    have hstep : (supportGraph (fun e => q (a e)) (fun e => q (b e))).Reachable
        (q x) (q y) := by
      by_cases heq : q x = q y
      · rw [heq]
      · obtain ⟨_,e,he⟩ := h
        apply SimpleGraph.Adj.reachable
        refine ⟨heq,e,?_⟩
        rcases he with he | he
        · exact Or.inl ⟨congrArg q he.1,congrArg q he.2⟩
        · exact Or.inr ⟨congrArg q he.1,congrArg q he.2⟩
    exact hstep.trans ih

@[simp] theorem groundMap_eq_inl (alpha beta : V) (z : SplitVertex alpha)
    (x : {v : V // v ≠ alpha ∧ v ≠ beta}) :
    groundMap alpha beta z = .inl x ↔ z = .inl ⟨x.val,x.property.1⟩ := by
  cases z with
  | inr k => simp only [groundMap,Sum.inr_ne_inl]
  | inl y =>
    by_cases hy : y.val = beta
    · simp only [groundMap,dif_pos hy,Sum.inr_ne_inl,Sum.inl.injEq,Subtype.ext_iff,false_iff]
      intro h
      exact x.property.2 (h.symm.trans hy)
    · simp only [groundMap,dif_neg hy,Sum.inl.injEq,Subtype.ext_iff]

/-- All components of the identified network meet its genuine two-terminal boundary. -/
theorem identified_boundary_reachable (J : CopiedGraph V E) (alpha beta : V)
    (side : E → Bool) (hc : (supportGraph J.left J.right).Preconnected) :
    ∀ x, ∃ y ∈ ({.inr false,.inr true} : Finset (GroundedSplitVertex alpha beta)),
      (supportGraph (groundedSplitGraph J alpha beta side).left
        (groundedSplitGraph J alpha beta side).right).Reachable x y := by
  intro x
  have lift (z : SplitVertex alpha) :
      ∃ y ∈ ({.inr false,.inr true} : Finset (GroundedSplitVertex alpha beta)),
        (supportGraph (groundedSplitGraph J alpha beta side).left
          (groundedSplitGraph J alpha beta side).right).Reachable (groundMap alpha beta z) y := by
    obtain ⟨k,hk⟩ := split_reachable_terminal J.left J.right alpha side hc z
    refine ⟨.inr k,?_,mapped_copies_reachable _ _ (groundMap alpha beta) hk⟩
    cases k <;> simp only [Finset.mem_insert,Finset.mem_singleton,or_true,true_or]
  cases x with
  | inr k => exact lift (.inr k)
  | inl v =>
    have h := lift (.inl ⟨v.val,v.property.1⟩)
    simpa only [groundMap,dif_neg v.property.2] using h

/-- The unique zero/one harmonic voltage on the literal identified split graph. -/
def identifiedVoltage [Fintype V] [Fintype E] (J : CopiedGraph V E) (alpha beta : V)
    (side : E → Bool) (hc : (supportGraph J.left J.right).Preconnected) :
    GroundedSplitVertex alpha beta → ℝ :=
  harmonicExtension (groundedSplitGraph J alpha beta side).left
    (groundedSplitGraph J alpha beta side).right {.inr false,.inr true}
    (identified_boundary_reachable J alpha beta side hc)
    (fun x => if x = .inr true then 1 else 0)

/-- Identification changes no free-vertex Laplacian term, including zero terms of loops. -/
theorem identified_laplacian_inl [Fintype E] (J : CopiedGraph V E) (alpha beta : V)
    (side : E → Bool) (f : GroundedSplitVertex alpha beta → ℝ)
    (x : {v : V // v ≠ alpha ∧ v ≠ beta}) :
    laplacian (groundedSplitGraph J alpha beta side).left
      (groundedSplitGraph J alpha beta side).right f (.inl x) =
    laplacian (splitGraph J alpha side).left (splitGraph J alpha side).right
      (fun z => f (groundMap alpha beta z)) (.inl ⟨x.val,x.property.1⟩) := by
  have hmap : groundMap alpha beta (.inl ⟨x.val,x.property.1⟩) = .inl x := by
    simp only [groundMap,dif_neg x.property.2]
  simp only [laplacian,groundedSplitGraph,groundMap_eq_inl,hmap]

/-- The actual harmonic voltage pulls back to split values (0,1,0). -/
theorem identified_voltage_pullback [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (alpha beta : V) (hbeta : beta ≠ alpha)
    (side : E → Bool) (hc : (supportGraph J.left J.right).Preconnected) :
    (fun z => identifiedVoltage J alpha beta side hc (groundMap alpha beta z)) =
      responseBasis (splitGraph J alpha side).left (splitGraph J alpha side).right
        (splitTerminals alpha beta hbeta)
        (split_terminal_reachable J.left J.right alpha beta hbeta side hc) 1 := by
  let K := groundedSplitGraph J alpha beta side
  let r := splitTerminals alpha beta hbeta
  let hR := split_terminal_reachable J.left J.right alpha beta hbeta side hc
  let u := identifiedVoltage J alpha beta side hc
  have hu := harmonicExtension_spec K.left K.right
    ({.inr false,.inr true} : Finset (GroundedSplitVertex alpha beta))
    (identified_boundary_reachable J alpha beta side hc)
    (fun x => if x = .inr true then (1 : ℝ) else 0)
  have h0 : u (.inr false) = 0 := by
    exact (hu.1 _ (by simp)).trans (if_neg (by intro h; have hb := Sum.inr.inj h; cases hb))
  have h1 : u (.inr true) = 1 := by
    exact (hu.1 _ (by simp)).trans (if_pos rfl)
  apply eq_of_harmonic_boundary (splitGraph J alpha side).left
    (splitGraph J alpha side).right (terminalSet r) hR
  · intro x hx
    obtain ⟨i,rfl⟩ := (mem_terminalSet_iff r x).mp hx
    change u (groundMap alpha beta (r i)) =
      responseBasis (fun e => splitEndpoint alpha side (J.left e) e)
        (fun e => splitEndpoint alpha side (J.right e) e) r hR 1 (r i)
    rw [responseBasis_terminal _ _ r (splitTerminals_injective alpha beta hbeta) hR]
    fin_cases i
    · exact h0
    · exact h1
    · change u (groundMap alpha beta (.inl ⟨beta,hbeta⟩)) = 0
      rw [groundMap_beta]
      exact h0
  · intro x hx
    cases x with
    | inr k =>
      cases k
      · exact (hx (mem_terminalSet r 0)).elim
      · exact (hx (mem_terminalSet r 1)).elim
    | inl v =>
      have hv : v.val ≠ beta := by
        intro hv
        have he : r 2 = .inl v := congrArg Sum.inl (Subtype.ext hv.symm)
        exact hx (he ▸ mem_terminalSet r 2)
      rw [← identified_laplacian_inl J alpha beta side u ⟨v.val,v.property,hv⟩]
      exact hu.2 _ (by simp)
  · exact responseBasis_harmonic _ _ r hR 1

/-- The conductance against the identified ground is the total diagonal R11. -/
theorem identified_energy_eq_total_response [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (alpha beta : V) (hbeta : beta ≠ alpha)
    (side : E → Bool) (hc : (supportGraph J.left J.right).Preconnected) :
    energy (groundedSplitGraph J alpha beta side).left
      (groundedSplitGraph J alpha beta side).right (identifiedVoltage J alpha beta side hc) =
    responseEntry (splitGraph J alpha side).left (splitGraph J alpha side).right
      (splitTerminals alpha beta hbeta)
      (split_terminal_reachable J.left J.right alpha beta hbeta side hc) 1 1 := by
  rw [identified_energy_pullback,identified_voltage_pullback J alpha beta hbeta side hc]
  exact (split_total_response_eq_energy J.left J.right alpha beta hbeta side hc).symm

end
end FiniteAvalanches.Electrical.ChordSplit
