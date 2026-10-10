import FiniteAvalanches.Probability.Radius.WiredLimits
import FiniteAvalanches.Probability.UniformMap
import FiniteAvalanches.Sandpile.Waves.SourceExtension

namespace FiniteAvalanches.External.SandpileLimit

open LatticeProb MeasureTheory Filter FiniteAvalanches FiniteAvalanches.Sandpile
  FiniteAvalanches.Probability
open scoped ENNReal Classical

noncomputable section

/-- Stable fields vanishing off `Λ` that have no forbidden subset of `Λ`. -/
def allowedFields (Λ : Finset Site2) : Set StableField :=
  {η | (∀ x, x ∉ Λ → η x = 0) ∧ Waves.allowed Λ (fun x => ((η x).val : ℤ))}

theorem allowedFields_finite (Λ : Finset Site2) : (allowedFields Λ).Finite := by
  have hf : (Set.range (fun p : Λ → Fin 4 =>
      fun x : Site2 => if h : x ∈ Λ then p ⟨x, h⟩ else (0 : Fin 4))).Finite :=
    Set.finite_range _
  refine hf.subset ?_
  intro η hη
  refine ⟨fun x => η x.val, ?_⟩
  funext x
  by_cases h : x ∈ Λ
  · simp only [dif_pos h]
  · simp only [dif_neg h]
    exact (hη.1 x h).symm

theorem allowedFields_nonempty (Λ : Finset Site2) : (allowedFields Λ).Nonempty := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Λ ⊆ boxSites N :=
    ⟨Λ.sup (siteRadius 0), fun x hx =>
      (site_radius_zero_le_iff x _).mp (Finset.le_sup (f := siteRadius 0) hx)⟩
  let η0 : FiniteWired.Recurrent N := ⟨FiniteWired.allThree N, FiniteWired.allThree_recurrent N⟩
  have hbox : Waves.allowed (boxSites N) (fun x => ((FiniteWired.zeroExtend N η0 x).val : ℤ)) :=
    (Waves.recurrent_iff_allowed η0.val _
      (fun x => by simp only [FiniteWired.zeroExtend_site])).mp η0.property
  refine ⟨fun x => if x ∈ Λ then FiniteWired.zeroExtend N η0 x else 0,
    fun x hx => if_neg hx, ?_⟩
  intro A hA hf
  apply hbox A (hA.trans hN)
  refine ⟨hf.1, fun x hx => ?_⟩
  have h1 := hf.2 x hx
  simp only [if_pos (hA hx)] at h1
  exact h1

instance (Λ : Finset Site2) : Fintype (allowedFields Λ) := (allowedFields_finite Λ).fintype
instance (Λ : Finset Site2) : Nonempty (allowedFields Λ) := (allowedFields_nonempty Λ).to_subtype

/-- Uniform probability on the allowed fields of the wired volume `Λ` (zero outside `Λ`). -/
def finiteFieldLawOn (Λ : Finset Site2) : Measure StableField :=
  Measure.map (Subtype.val : allowedFields Λ → StableField) (uniformMeasure (allowedFields Λ))

instance finiteFieldLawOn_probability (Λ : Finset Site2) :
    IsProbabilityMeasure (finiteFieldLawOn Λ) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

def finiteFieldProbabilityOn (Λ : Finset Site2) : ProbabilityMeasure StableField :=
  ⟨finiteFieldLawOn Λ, inferInstance⟩

theorem zeroExtend_mem_allowedFields (N : ℕ) (η : FiniteWired.Recurrent N) :
    FiniteWired.zeroExtend N η ∈ allowedFields (boxSites N) :=
  ⟨fun x hx => FiniteWired.zeroExtend_outside N η x (fun h => hx ((mem_box_sites N x).mpr h)),
    (Waves.recurrent_iff_allowed η.val (fun x => ((FiniteWired.zeroExtend N η x).val : ℤ))
      (fun x => by simp only [FiniteWired.zeroExtend_site])).mp η.property⟩

/-- Zero extension identifies the recurrent heights of the wired box with its allowed fields. -/
def boxRecurrentEquiv (N : ℕ) : FiniteWired.Recurrent N ≃ allowedFields (boxSites N) :=
  Equiv.ofBijective
    (fun η => ⟨FiniteWired.zeroExtend N η, zeroExtend_mem_allowedFields N η⟩)
    ⟨by
      intro η η' h
      apply Subtype.ext
      funext x
      have hx := congrFun (congrArg Subtype.val h) (FiniteWired.site x)
      simpa only [FiniteWired.zeroExtend_site] using hx,
     by
      intro ζ
      have hrec : FiniteWired.recurrent
          (fun x : FiniteWired.Active N => ζ.val (FiniteWired.site x)) :=
        (Waves.recurrent_iff_allowed (fun x => ζ.val (FiniteWired.site x))
          (fun x => ((ζ.val x).val : ℤ)) (fun x => rfl)).mpr ζ.property.2
      refine ⟨⟨fun x => ζ.val (FiniteWired.site x), hrec⟩, Subtype.ext ?_⟩
      funext x
      by_cases hx : FiniteWired.inBox N x
      · change (if h : FiniteWired.inBox N x then
          ζ.val (FiniteWired.site (FiniteWired.activeOfSite N x h)) else 0) = ζ.val x
        rw [dif_pos hx]
        rfl
      · change (if h : FiniteWired.inBox N x then
          ζ.val (FiniteWired.site (FiniteWired.activeOfSite N x h)) else 0) = ζ.val x
        rw [dif_neg hx]
        exact (ζ.property.1 x (fun h => hx ((mem_box_sites N x).mp h))).symm⟩

/-- On boxes this is the repo's actual forbidden-subset finite law. -/
theorem finiteFieldLawOn_boxSites (N : ℕ) :
    finiteFieldLawOn (boxSites N) = FiniteWired.finiteFieldLaw N := by
  have hl : FiniteWired.law N = uniformMeasure (FiniteWired.Recurrent N) := by
    simp only [FiniteWired.law, uniformMeasure, Nat.card_eq_fintype_card]
  have hf : ((Subtype.val : allowedFields (boxSites N) → StableField) ∘ boxRecurrentEquiv N) =
      FiniteWired.zeroExtend N := rfl
  rw [finiteFieldLawOn, FiniteWired.finiteFieldLaw, hl,
    ← uniform_measure_map_equiv (boxRecurrentEquiv N),
    Measure.map_map measurable_subtype_coe (measurable_of_finite _), hf]

theorem finiteFieldProbabilityOn_boxSites (N : ℕ) :
    finiteFieldProbabilityOn (boxSites N) = finiteFieldProbability N :=
  Subtype.ext (finiteFieldLawOn_boxSites N)

end

end FiniteAvalanches.External.SandpileLimit
