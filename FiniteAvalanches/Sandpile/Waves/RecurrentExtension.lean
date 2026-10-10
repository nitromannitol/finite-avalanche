import FiniteAvalanches.Sandpile.Waves.SourceExtension

/-! The exact finite recurrent carrier splits into a punctured field and one
source height in its proved interval. This is a structural bijection, not yet
an inverse-excursion/predecessor bijection. -/

namespace FiniteAvalanches.Sandpile.Waves

open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

def restrictOff {N : ℕ} (o : FiniteWired.Active N) (η : FiniteWired.Heights N) : OffField N o :=
  fun x => η x.val

theorem source_extension_restrict {N : ℕ} (o : FiniteWired.Active N) (η : FiniteWired.Heights N) :
    sourceExtension (η o) (restrictOff o η) = η := by
  funext x
  unfold sourceExtension restrictOff
  split
  · rename_i hx; exact congrArg η hx.symm
  · rfl

theorem restrict_source_extension {N : ℕ} {o : FiniteWired.Active N}
    (a : Fin 4) (h : OffField N o) : restrictOff o (sourceExtension a h) = h := by
  funext x
  simp [restrictOff, sourceExtension, x.property]

theorem restrict_recurrent_allowed {N : ℕ} (o : FiniteWired.Active N)
    {η : FiniteWired.Heights N} (hη : FiniteWired.recurrent η) : punctured_allowed (restrictOff o η) := by
  let h := restrictOff o η
  have hfull : allowed (boxSites N) (wiredHeight (η o).val h) := by
    apply (recurrent_iff_allowed η (wiredHeight (η o).val h) ?_).mp hη
    intro x
    rw [wired_height_site, ← source_extension_height, source_extension_restrict]
  apply (allowed_congr (h := wiredHeight (η o).val h) (g := wiredHeight (-1) h)
    (fun x hx => wired_height_off _ _ h (Finset.mem_erase.mp hx).1)).mp
  intro A hA
  exact hfull A (hA.trans (Finset.erase_subset _ _))

/-- One punctured field, with one of its actual admissible source heights. -/
abbrev ExtensionPair (N : ℕ) (o : FiniteWired.Active N) :=
  (h : Punctured N o) × {a : Fin 4 // degree (core h.val) (FiniteWired.site o) ≤ a.val}

def recurrentToExtension {N : ℕ} (o : FiniteWired.Active N) (η : FiniteWired.Recurrent N) :
    ExtensionPair N o :=
  ⟨⟨restrictOff o η.val, restrict_recurrent_allowed o η.property⟩,
    ⟨η.val o, (source_extension_recurrent_iff (restrict_recurrent_allowed o η.property) (η.val o)).mp
      (by rw [source_extension_restrict]; exact η.property)⟩⟩

def extensionToRecurrent {N : ℕ} {o : FiniteWired.Active N} (p : ExtensionPair N o) :
    FiniteWired.Recurrent N :=
  ⟨sourceExtension p.2.val p.1.val, (source_extension_recurrent_iff p.1.property p.2.val).mpr p.2.property⟩

/-- The literal recurrent fields, including all empty-avalanche source extensions. -/
def recurrentExtensionEquiv {N : ℕ} (o : FiniteWired.Active N) :
    FiniteWired.Recurrent N ≃ ExtensionPair N o where
  toFun := recurrentToExtension o
  invFun := extensionToRecurrent
  left_inv η := Subtype.ext (source_extension_restrict o η.val)
  right_inv p := by
    have hf : (recurrentToExtension o (extensionToRecurrent p)).1 = p.1 := by
      apply Subtype.ext
      exact restrict_source_extension p.2.val p.1.val
    refine Sigma.ext hf ?_
    apply (Subtype.heq_iff_coe_eq (fun a => by rw [hf])).mpr
    change sourceExtension p.2.val p.1.val o = p.2.val
    simp [sourceExtension]

end
end FiniteAvalanches.Sandpile.Waves
