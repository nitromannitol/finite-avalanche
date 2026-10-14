import FiniteAvalanches.Sandpile.Recurrence.RawGraphDynamics
import FiniteAvalanches.Electrical.Network

/-! Connectedness makes the maximal stable raw field NoFSC. Legal source
reachability then proves the necessity of the criterion for every target. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

def maximalStable : Field s := fun x => (Burning.degree G x.val : ℤ) - 1

theorem maximal_stable : Stable G s (maximalStable G s) := by
  intro x
  simp only [maximalStable]
  omega

theorem maximal_no_fsc
    (hc : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected) :
    NoFSC G s (maximalStable G s) := by
  intro A hf
  let B : Finset V := A.image Subtype.val
  have hb : ∀ x ∈ B, Burning.degreeInto G (Finset.univ \ B) x = 0 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have hh := hf.2 v hv
    have hd := Burning.degree_into_compl G B v.val
    change (Burning.degree G v.val : ℤ) - 1 < (Burning.degreeInto G B v.val : ℤ) at hh
    omega
  have hclosed : ∀ x ∈ B, ∀ y,
      (FiniteAvalanches.Electrical.supportGraph G.left G.right).Adj x y → y ∈ B := by
    intro x hx y hxy
    by_contra hyn
    obtain ⟨_, e, he⟩ := hxy
    have hem : e ∈ Burning.incidentInto G (Finset.univ \ B) x := by
      simp only [Burning.incidentInto, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases he with ⟨ha, hbb⟩ | ⟨hbb, ha⟩
      · exact Or.inl ⟨ha, by simpa only [hbb, Finset.mem_sdiff, Finset.mem_univ, true_and] using hyn⟩
      · exact Or.inr ⟨hbb, by simpa only [ha, Finset.mem_sdiff, Finset.mem_univ, true_and] using hyn⟩
    have he0 : Burning.incidentInto G (Finset.univ \ B) x = ∅ :=
      Finset.card_eq_zero.mp (hb x hx)
    rw [he0] at hem
    exact Finset.notMem_empty _ hem
  have hw : ∀ {x y}, (FiniteAvalanches.Electrical.supportGraph G.left G.right).Walk x y →
      x ∈ B → y ∈ B := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x z y hxz p ih => intro hx; exact ih (hclosed x hx z hxz)
  obtain ⟨v, hv⟩ := hf.1
  obtain ⟨p⟩ := hc v.val s
  have hsv : s ∈ B := hw p (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  exact Burning.source_shape_avoids_sink s A hsv

theorem accessible_no_fsc
    (hc : (FiniteAvalanches.Electrical.supportGraph G.left G.right).Preconnected)
    {η : Field s} (h : Accessible G s η) : NoFSC G s η :=
  reach_preserves_no_fsc G s (maximal_no_fsc G s hc) (h (maximalStable G s))

end
end FiniteAvalanches.Sandpile.RawGraph
