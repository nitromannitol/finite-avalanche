import FiniteAvalanches.Sandpile.Components.Fields

/-! The corrected source-shape and whole height carriers are genuinely finite. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

instance componentShapeFinite {N : ℕ} (o : FiniteWired.Active N) : Finite (ComponentShape o) :=
  Finite.of_injective
    (fun C : ComponentShape o =>
      (⟨C.val, Finset.mem_powerset.mpr C.property.1⟩ : {C // C ∈ (boxSites N).powerset}))
    (fun _ _ he => Subtype.ext (congrArg
      (fun s : {C : Finset Site2 // C ∈ (boxSites N).powerset} => s.val) he))

instance componentShapeFintype {N : ℕ} (o : FiniteWired.Active N) : Fintype (ComponentShape o) :=
  Fintype.ofFinite _

theorem finite_inner_allowed {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Finite (InnerAllowed o C) := inferInstance

theorem finite_outer_allowed {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Finite (OuterAllowed C) := inferInstance

theorem finite_core_field {N : ℕ} {o : FiniteWired.Active N} (C : Finset Site2) :
    Finite (CoreField o C) := inferInstance

end
end FiniteAvalanches.Sandpile.Components
