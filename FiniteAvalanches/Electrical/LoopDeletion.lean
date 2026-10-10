import FiniteAvalanches.Electrical.ChordSplit.CopiedDiagram
import FiniteAvalanches.Electrical.Geometry.SourceVoltage

/-! Deleting only literal loops preserves original copies and electrical data. -/
namespace FiniteAvalanches.Electrical
open StatementGeometry
open scoped Classical BigOperators
noncomputable section
variable {V E : Type}

/-- Surviving original IDs, without any quotient of parallel copies. -/
abbrev NonloopCopy (J : CopiedGraph V E) := {e : E // J.left e ≠ J.right e}

/-- A fixed finite enumeration of the surviving original IDs. -/
instance nonloopCopyFintype [Fintype E] (J : CopiedGraph V E) : Fintype (NonloopCopy J) :=
  inferInstanceAs (Fintype {e : E // J.left e ≠ J.right e})

/-- Delete exactly those original IDs whose literal endpoints coincide. -/
def deleteLoops (J : CopiedGraph V E) : CopiedGraph V (NonloopCopy J) :=
  ⟨fun e => J.left e.val, fun e => J.right e.val⟩

theorem deleteLoops_endpoints (J : CopiedGraph V E) (e : NonloopCopy J) :
    (deleteLoops J).left e = J.left e.val ∧
      (deleteLoops J).right e = J.right e.val := ⟨rfl,rfl⟩

theorem deleteLoops_copy_injective (J : CopiedGraph V E) :
    Function.Injective (Subtype.val : NonloopCopy J → E) := Subtype.val_injective

theorem deleteLoops_loopless (J : CopiedGraph V E) (e : NonloopCopy J) :
    (deleteLoops J).left e ≠ (deleteLoops J).right e := e.property

private theorem sum_nonloop [Fintype E] (J : CopiedGraph V E) (f : E → ℝ)
    (hf : ∀ e, J.left e = J.right e → f e = 0) :
    (∑ e : NonloopCopy J, f e.val) = ∑ e : E, f e := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun e => J.left e ≠ J.right e) f]
  have hz : (∑ e : {e : E // ¬J.left e ≠ J.right e}, f e.val) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact hf e.val (not_not.mp e.property)
  rw [hz,add_zero]

theorem deleteLoops_energy [Fintype E] (J : CopiedGraph V E) (f : V → ℝ) :
    energy (deleteLoops J).left (deleteLoops J).right f = energy J.left J.right f := by
  unfold energy
  apply sum_nonloop J (fun e => (f (J.left e) - f (J.right e)) ^ 2)
  intro e he
  rw [he,sub_self,zero_pow (by decide : 2 ≠ 0)]

theorem deleteLoops_laplacian [Fintype E] (J : CopiedGraph V E)
    (f : V → ℝ) (x : V) :
    laplacian (deleteLoops J).left (deleteLoops J).right f x =
      laplacian J.left J.right f x := by
  unfold laplacian
  apply sum_nonloop J (fun e => (if J.left e = x then f x - f (J.right e) else 0) +
    (if J.right e = x then f x - f (J.left e) else 0))
  intro e he
  rw [he]
  by_cases hx : J.right e = x
  · rw [if_pos hx,hx,sub_self,add_zero]
  · rw [if_neg hx,add_zero]

theorem deleteLoops_supportGraph (J : CopiedGraph V E) :
    supportGraph (deleteLoops J).left (deleteLoops J).right =
      supportGraph J.left J.right := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  constructor
  · rintro ⟨hne,e,he⟩
    exact ⟨hne,e.val,he⟩
  · rintro ⟨hne,e,he⟩
    have he' : J.left e ≠ J.right e := by
      rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hne
      · exact hne.symm
    exact ⟨hne,⟨e,he'⟩,he⟩

theorem deleteLoops_conductance [Fintype E] (J : CopiedGraph V E) (x y : V) :
    conductance (deleteLoops J).left (deleteLoops J).right x y =
      conductance J.left J.right x y := by
  by_cases hxy : x = y
  · simp only [conductance,if_pos hxy]
  · simp only [conductance,if_neg hxy]
    apply sum_nonloop J (fun e => (if J.left e = x ∧ J.right e = y then 1 else 0) +
      (if J.right e = x ∧ J.left e = y then 1 else 0))
    intro e he
    have h1 : ¬(J.left e = x ∧ J.right e = y) :=
      fun h => hxy (h.1.symm.trans (he.trans h.2))
    have h2 : ¬(J.right e = x ∧ J.left e = y) :=
      fun h => hxy (h.1.symm.trans (he.symm.trans h.2))
    rw [if_neg h1,if_neg h2,add_zero]

theorem deleteLoops_boundary_reachable (J : CopiedGraph V E) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph J.left J.right).Reachable x y) :
    ∀ x, ∃ y ∈ B, (supportGraph (deleteLoops J).left (deleteLoops J).right).Reachable x y := by
  rw [deleteLoops_supportGraph]
  exact hB

theorem deleteLoops_harmonicExtension [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph J.left J.right).Reachable x y) (t : V → ℝ) :
    harmonicExtension (deleteLoops J).left (deleteLoops J).right B
      (deleteLoops_boundary_reachable J B hB) t =
      harmonicExtension J.left J.right B hB t := by
  apply harmonicExtension_eq J.left J.right B hB t
  have hs := harmonicExtension_spec (deleteLoops J).left (deleteLoops J).right B
    (deleteLoops_boundary_reachable J B hB) t
  refine ⟨hs.1,fun x hx => ?_⟩
  rw [← deleteLoops_laplacian]
  exact hs.2 x hx

theorem deleteLoops_preconnected (J : CopiedGraph V E)
    (hc : (supportGraph J.left J.right).Preconnected) :
    (supportGraph (deleteLoops J).left (deleteLoops J).right).Preconnected := by
  rw [deleteLoops_supportGraph]
  exact hc

namespace Source
/-- Effective conductance is the once-copy energy of the already characterized
unique unit voltage, exactly as for finite connected two-terminal networks. -/
def effectiveConductance [Fintype V] [Fintype E] (J : CopiedGraph V E)
    (ground source : V) (_hne : ground ≠ source)
    (hc : (supportGraph J.left J.right).Preconnected) : ℝ :=
  energy J.left J.right (voltage J ground source hc)

theorem effectiveConductance_eq_flux [Fintype V] [Fintype E] (J : CopiedGraph V E)
    (ground source : V) (hne : ground ≠ source)
    (hc : (supportGraph J.left J.right).Preconnected) :
    effectiveConductance J ground source hne hc = laplacian J.left J.right (voltage J ground source hc) source := by
  obtain ⟨hg,hs,hh⟩ := voltage_spec J ground source hne hc
  rw [effectiveConductance,energy_eq_incidence_sum,Finset.sum_eq_single source]
  · rw [hs,one_mul]
  · intro x _ hx
    by_cases hxg : x = ground
    · rw [hxg,hg,zero_mul]
    · rw [hh x hxg hx,mul_zero]
  · simp only [Finset.mem_univ,not_true_eq_false,false_implies]

theorem effectiveConductance_le_trial [Fintype V] [Fintype E] (J : CopiedGraph V E)
    (ground source : V) (hne : ground ≠ source)
    (hc : (supportGraph J.left J.right).Preconnected) (f : V → ℝ)
    (hg : f ground = 0) (hs : f source = 1) :
    effectiveConductance J ground source hne hc ≤ energy J.left J.right f := by
  apply energy_harmonicExtension_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rw [hg,if_neg hne]
  · rw [Finset.mem_singleton.mp hx,hs,if_pos rfl]

theorem effectiveConductance_pos [Fintype V] [Fintype E] (J : CopiedGraph V E)
    (ground source : V) (hne : ground ≠ source)
    (hc : (supportGraph J.left J.right).Preconnected) :
    0 < effectiveConductance J ground source hne hc := by
  have hn := energy_nonneg J.left J.right (voltage J ground source hc)
  by_contra h
  have hz : energy J.left J.right (voltage J ground source hc) = 0 :=
    le_antisymm (le_of_not_gt h) hn
  have he := eq_of_reachable J.left J.right (voltage J ground source hc)
    ((energy_eq_zero_iff _ _ _).mp hz) (hc ground source)
  obtain ⟨hg,hs,_⟩ := voltage_spec J ground source hne hc
  rw [hg,hs] at he
  exact zero_ne_one he

theorem deleteLoops_voltage [Fintype V] [Fintype E] (J : CopiedGraph V E)
    (ground source : V) (hne : ground ≠ source)
    (hc : (supportGraph J.left J.right).Preconnected) :
    voltage (deleteLoops J) ground source (deleteLoops_preconnected J hc) =
      voltage J ground source hc := by
  have hs := voltage_spec (deleteLoops J) ground source hne (deleteLoops_preconnected J hc)
  apply voltage_unique J ground source hne hc
  · exact hs.1
  · exact hs.2.1
  · intro x hg hs'
    rw [← deleteLoops_laplacian]
    exact hs.2.2 x hg hs'

theorem deleteLoops_effectiveConductance [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (ground source : V) (hne : ground ≠ source)
    (hc : (supportGraph J.left J.right).Preconnected) :
    effectiveConductance (deleteLoops J) ground source hne (deleteLoops_preconnected J hc) =
      effectiveConductance J ground source hne hc := by
  unfold effectiveConductance
  rw [deleteLoops_voltage J ground source hne hc,deleteLoops_energy]

end Source
end
end FiniteAvalanches.Electrical
