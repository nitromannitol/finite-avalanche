import FiniteAvalanches.Sandpile.Recurrence.RawGraphMaximal
import FiniteAvalanches.Sandpile.Recurrence.RawGraphPositiveScript
import FiniteAvalanches.Sandpile.Recurrence.RawGraphReverseFiring

/-! Full accessibility from every raw integer field, with no stability or
nonnegativity restriction on the input. The source recurrence criterion follows. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

/-- The positive script is constructed inside the proof, before choosing the grain word. -/
theorem no_fsc_accessible
    (hc : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected)
    {η : Field s} (hη : NoFSC G s η) : Accessible G s η := by
  obtain ⟨p, hps, hpl⟩ := exists_positive_script G s hc
  intro θ
  let K : ℕ := ∑ x : Burning.SourceVertex s, (θ x - η x).toNat
  let n : V → ℕ := fun y => K * p y
  have hns : n s = 0 := by simp only [n, hps, mul_zero]
  have hle : ∀ x, θ x ≤ raised G s η n x := by
    intro x
    have hp := hpl x.val (Burning.source_vertex_ne_sink s x)
    have hd : (θ x - η x).toNat ≤ K := by
      change (θ x - η x).toNat ≤ ∑ y : Burning.SourceVertex s, (θ y - η y).toNat
      exact Finset.single_le_sum (f := fun y : Burning.SourceVertex s => (θ y - η y).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    have hdelta : lapInt G (fun y => (n y : ℤ)) x.val =
        (K : ℤ) * lapInt G (fun y => (p y : ℤ)) x.val := by
      simp only [n, Nat.cast_mul, lap_int_nat_mul]
    have hK : (K : ℤ) ≤ (K : ℤ) * lapInt G (fun y => (p y : ℤ)) x.val := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg K)
    change θ x ≤ η x + lapInt G (fun y => (n y : ℤ)) x.val
    rw [hdelta]
    omega
  exact (reach_of_le G s θ _ hle).trans (reverse_firing G s η hη n hns)

/-- Exact raw integer criterion. Stability is needed only when naming a recurrent sandpile. -/
theorem no_fsc_iff_accessible
    (hc : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected)
    (η : Field s) : NoFSC G s η ↔ Accessible G s η :=
  ⟨no_fsc_accessible G s hc, accessible_no_fsc G s hc⟩

abbrev RecurrentState := {η : StableState G s // Accessible G s η.val}

/-- The accessibility carrier consumes the proven criterion; no characterization is a premise. -/
def recurrentAllowedEquiv
    (hc : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected) :
    RecurrentState G s ≃ AllowedState G s where
  toFun η := ⟨η.val, accessible_no_fsc G s hc η.property⟩
  invFun η := ⟨η.val, no_fsc_accessible G s hc η.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full unique Fin(original copied degree) encoding of actual accessibility recurrent fields. -/
def recurrentFieldEquiv
    (hc : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected) :
    RecurrentState G s ≃
      {h : Burning.SourceHeights G s // Burning.noForbidden G (Finset.univ.erase s) h} :=
  (recurrentAllowedEquiv G s hc).trans (allowedFieldEquiv G s)

end
end FiniteAvalanches.Sandpile.RawGraph
