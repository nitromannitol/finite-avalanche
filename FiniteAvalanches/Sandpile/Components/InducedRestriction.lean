import FiniteAvalanches.Sandpile.Components.Graphs

/-! Internal degrees of every forbidden subset are restrictions of the actual component graph. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- Restricting an induced incident carrier again retains precisely the endpoints in the smaller support. -/
theorem induced_incident_copies_filter {N : ℕ}
    {U V : Set (FiniteWired.Vertex N)} (hUV : U ⊆ V) (x : FiniteWired.Active N) :
    inducedIncidentCopies U x = (inducedIncidentCopies V x).filter
      (fun e => (FiniteWired.endpoints e).1 ∈ U ∧ (FiniteWired.endpoints e).2 ∈ U) := by
  ext e
  simp only [inducedIncidentCopies, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, hl, hr⟩
    exact ⟨⟨hi, hUV hl, hUV hr⟩, hl, hr⟩
  · rintro ⟨⟨hi, _, _⟩, hl, hr⟩
    exact ⟨hi, hl, hr⟩

/-- Every source-free subset uses only the actual induced inside copies. -/
theorem inner_forbidden_copies {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (A : Finset Site2) (hA : A ⊆ C.val.erase (FiniteWired.site o))
    (x : FiniteWired.Active N) :
    inducedIncidentCopies {v | insideVertex A v} x =
      (inducedIncidentCopies (insideSupport C) x).filter
        (fun e => insideVertex A (FiniteWired.endpoints e).1 ∧
          insideVertex A (FiniteWired.endpoints e).2) := by
  apply induced_incident_copies_filter
  intro v hv
  cases v with
  | none => exact hv.elim
  | some y => exact (Finset.mem_erase.mp (hA hv)).2

/-- Every outside subset uses only the actual complementary copies, never a crossing edge. -/
theorem outer_forbidden_copies {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (A : Finset Site2) (hA : A ⊆ boxSites N \ C.val)
    (x : FiniteWired.Active N) :
    inducedIncidentCopies {v | insideVertex A v} x =
      (inducedIncidentCopies (outsideSupport C) x).filter
        (fun e => insideVertex A (FiniteWired.endpoints e).1 ∧
          insideVertex A (FiniteWired.endpoints e).2) := by
  apply induced_incident_copies_filter
  intro v hv
  cases v with
  | none => exact hv.elim
  | some y => exact (Finset.mem_sdiff.mp (hA hv)).2

end
end FiniteAvalanches.Sandpile.Components
