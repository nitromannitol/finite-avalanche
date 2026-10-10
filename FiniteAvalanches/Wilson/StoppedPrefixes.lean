import FiniteAvalanches.Wilson.StoppedLaw

/-! The complete least-hit copied word, before any chronological erasure.
The none outcome includes genuinely infinite paths that never hit the stop set. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork
open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

instance stoppedPrefixMeasurableSpace : MeasurableSpace (Option (PrefixRecord (V := V) (E := E))) := ⊤
instance stoppedPrefixMeasurableSingletonClass :
    MeasurableSingletonClass (Option (PrefixRecord (V := V) (E := E))) := ⟨fun _ => trivial⟩

def stoppedPrefix (B : Set V) (x : V) : Driver G → Option (PrefixRecord (V := V) (E := E)) :=
  firstHitOutput G B x (fun ω n => walkPrefix G x ω n)

theorem measurable_stoppedPrefix (B : Set V) (x : V) : Measurable (stoppedPrefix G B x) :=
  measurable_firstHitOutput G B x _ (measurable_walkPrefix G x)

variable [∀ v : V, MeasurableSpace (Incident G v)] [∀ v : V, MeasurableSingletonClass (Incident G v)]
variable (μ ν : Measure (Letter G)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem stoppedPrefix_law_eq
    (h : ∀ v : V, μ.map (fun a => a v) = ν.map (fun a => a v)) (B : Set V) (x : V) :
    (driverLaw G μ).map (stoppedPrefix G B x) = (driverLaw G ν).map (stoppedPrefix G B x) :=
  firstHitOutput_law_eq G μ ν h B x _ (measurable_walkPrefix G x) (fun _ _ _ hh => hh)

end
end FiniteAvalanches.Wilson.CopiedNetwork
