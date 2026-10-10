import FiniteAvalanches.Sandpile.Waves.WaveNumber

/-! Finite addition preserves the full allowed-field carrier. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

private abbrev HeightInterval {A : Type*} (lower : A → Fin 4) :=
  {p : A × Fin 4 // lower p.1 ≤ p.2}

private def intervalNext {A : Type*} (lower : A → Fin 4) (e : Equiv.Perm A)
    (p : HeightInterval lower) : HeightInterval lower :=
  if h : p.val.2.val + 1 < 4 then
    ⟨(p.val.1, ⟨p.val.2.val + 1, h⟩), by have hp := p.property; change (lower p.val.1).val ≤ p.val.2.val at hp; change (lower p.val.1).val ≤ p.val.2.val + 1; omega⟩
  else ⟨(e p.val.1, lower (e p.val.1)), le_rfl⟩

private def intervalPrev {A : Type*} (lower : A → Fin 4) (e : Equiv.Perm A)
    (p : HeightInterval lower) : HeightInterval lower :=
  if h : (lower p.val.1).val < p.val.2.val then
    ⟨(p.val.1, ⟨p.val.2.val - 1, by have hp := p.val.2.isLt; omega⟩), by change (lower p.val.1).val ≤ p.val.2.val - 1; omega⟩
  else ⟨(e.symm p.val.1, 3), by have hp := (lower (e.symm p.val.1)).isLt; change (lower (e.symm p.val.1)).val ≤ 3; omega⟩

private theorem intervalPrev_next {A : Type*} (lower : A → Fin 4) (e : Equiv.Perm A)
    (p : HeightInterval lower) : intervalPrev lower e (intervalNext lower e p) = p := by
  unfold intervalNext
  split
  · rename_i h
    have hp := p.property
    change (lower p.val.1).val ≤ p.val.2.val at hp
    have hs : (lower p.val.1).val < p.val.2.val + 1 := by omega
    simp only [intervalPrev, hs, dite_true]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Fin.ext
    simp
  · rename_i h
    simp only [intervalPrev, lt_self_iff_false, dite_false, Equiv.symm_apply_apply]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Fin.ext
    have hp := p.val.2.isLt
    change 3 = p.val.2.val
    omega

private theorem intervalNext_prev {A : Type*} (lower : A → Fin 4) (e : Equiv.Perm A)
    (p : HeightInterval lower) : intervalNext lower e (intervalPrev lower e p) = p := by
  unfold intervalPrev
  split
  · rename_i h
    have hp := p.val.2.isLt
    have ha : p.val.2.val - 1 + 1 < 4 := by omega
    simp only [intervalNext, ha, dite_true]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Fin.ext
    change p.val.2.val - 1 + 1 = p.val.2.val
    omega
  · rename_i h
    have ht : ¬ ((3 : Fin 4).val + 1 < 4) := by decide
    simp only [intervalNext, ht, dite_false, Equiv.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Fin.ext
    have hp := p.property
    change (lower p.val.1).val ≤ p.val.2.val at hp
    change (lower p.val.1).val = p.val.2.val
    omega

private def intervalEquiv {A : Type*} (lower : A → Fin 4) (e : Equiv.Perm A) :
    Equiv.Perm (HeightInterval lower) where
  toFun := intervalNext lower e
  invFun := intervalPrev lower e
  left_inv := intervalPrev_next lower e
  right_inv := intervalNext_prev lower e

private def terminalLower {N : ℕ} {o : FiniteWired.Active N} (h : TerminalState N o) : Fin 4 :=
  ⟨degree (core h.val.val) (FiniteWired.site o), h.property⟩

private def terminalExtensionEquiv {N : ℕ} {o : FiniteWired.Active N} :
    ExtensionPair N o ≃ HeightInterval (@terminalLower N o) where
  toFun p := ⟨(⟨p.1, by
    have hp := p.2.property
    have ha := p.2.val.isLt
    change degree (core p.1.val) (FiniteWired.site o) < 4
    omega⟩, p.2.val), p.2.property⟩
  invFun p := ⟨p.val.1.val, ⟨p.val.2, p.property⟩⟩
  left_inv p := by
    rcases p with ⟨h, a, ha⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨⟨h, ht⟩, a⟩, ha⟩
    rfl

/-- One-grain addition on all finite allowed recurrent fields, including empty avalanches. -/
def finiteAdditionEquiv {N : ℕ} (o : FiniteWired.Active N) : Equiv.Perm (FiniteWired.Recurrent N) :=
  let e := (recurrentExtensionEquiv o).trans terminalExtensionEquiv
  e.trans ((intervalEquiv terminalLower returnEquiv.symm).trans e.symm)

theorem finite_addition_of_source_lt {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) (hη : (η.val o).val < 3) :
    (finiteAdditionEquiv o η).val =
      sourceExtension ⟨(η.val o).val + 1, by omega⟩ (restrictOff o η.val) := by
  have hs : (η.val o).val + 1 < 4 := by omega
  simp only [finiteAdditionEquiv, Equiv.trans_apply, Equiv.symm_trans_apply,
    recurrentExtensionEquiv, terminalExtensionEquiv, intervalEquiv,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, recurrentToExtension, intervalNext,
    hs, dite_true, extensionToRecurrent]

theorem finite_addition_of_source_three {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) (hη : η.val o = 3) :
    finiteAdditionEquiv o η = lowestExtension
      (returnEquiv.symm (sourceThreeToTerminal ⟨η, hη⟩)) := by
  apply Subtype.ext
  simp only [finiteAdditionEquiv, Equiv.trans_apply, Equiv.symm_trans_apply,
    recurrentExtensionEquiv, terminalExtensionEquiv, intervalEquiv,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, recurrentToExtension, intervalNext, hη]
  rfl

/-- Every image under the permutation is the endpoint of an actual finite legal stabilization. -/
theorem exists_finite_addition_stabilization {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) :
    ∃ w : List Site2, WiredStabilizes (FiniteWired.zeroExtend N η)
      (oneGrain (FiniteWired.site o)) (boxSites N) w ∧
      ∀ x : FiniteWired.Active N,
        heightAfter (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o)))
          w (FiniteWired.site x) = (((finiteAdditionEquiv o η).val x).val : ℤ) := by
  by_cases hη : η.val o = 3
  · let z := inputExcursion (⟨η, hη⟩ : SourceThree N o)
    obtain ⟨ws, _, hw, hend, _⟩ := exists_excursion_wired_stabilization z
    have hp : excursionPredecessorEquiv z = (⟨η, hη⟩ : SourceThree N o) :=
      excursionPredecessorEquiv.apply_symm_apply _
    have hagree : ∀ y ∈ boxSites N,
        FiniteWired.zeroExtend N η y = wiredStable (returnMap z).val.val y := by
      intro y hy
      let v := FiniteWired.activeOfSite N y ((mem_box_sites N y).mp hy)
      change FiniteWired.zeroExtend N η (FiniteWired.site v) =
        wiredStable (returnMap z).val.val (FiniteWired.site v)
      rw [FiniteWired.zeroExtend_site, excursion_predecessor_height z v, hp]
    refine ⟨ws.flatten, wired_stabilizes_of_agree hw hagree, ?_⟩
    intro x
    calc
      heightAfter (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o)))
          ws.flatten (FiniteWired.site x) =
        heightAfter (initial (wiredStable (returnMap z).val.val) (oneGrain (FiniteWired.site o)))
          ws.flatten (FiniteWired.site x) := by
            simp only [heightAfter, initial, hagree _ (site_mem_box x)]
      _ = (((lowestExtension z).val x).val : ℤ) := hend x
      _ = (((finiteAdditionEquiv o η).val x).val : ℤ) := by
        rw [finite_addition_of_source_three o η hη]
        rfl
  · have hs : (η.val o).val < 3 := by
      have hb := (η.val o).isLt
      have hn : (η.val o).val ≠ 3 := fun he => hη (Fin.ext he)
      omega
    have hnil : WiredStabilizes (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))
        (boxSites N) [] := by
      refine ⟨by simp, ?_, ?_⟩
      · intro k hk
        simp at hk
      · intro y hy
        have hlo := initial_nonneg (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o)) y
        refine ⟨by simpa [listCounts, lap, nbrSumZ] using hlo, ?_⟩
        by_cases he : y = FiniteWired.site o
        · subst y
          simp only [initial, FiniteWired.zeroExtend_site, oneGrain, Finsupp.single_eq_same]
          simpa [listCounts, lap, nbrSumZ] using
            (show ((η.val o).val : ℤ) + 1 < 4 by omega)
        · simp only [initial, oneGrain, Finsupp.single_eq_of_ne he]
          simp [listCounts, lap, nbrSumZ]
    refine ⟨[], hnil, ?_⟩
    intro x
    rw [finite_addition_of_source_lt o η hs]
    by_cases hx : x = o
    · subst x
      simp [heightAfter, initial, oneGrain, FiniteWired.zeroExtend_site,
        listCounts, lap, nbrSumZ, sourceExtension]
    · have hsite : FiniteWired.site x ≠ FiniteWired.site o :=
        fun he => hx (FiniteWired.site_injective N he)
      simp [heightAfter, initial, oneGrain, FiniteWired.zeroExtend_site,
        listCounts, lap, nbrSumZ, sourceExtension, restrictOff, hx, hsite]

/-- Every legal stabilization has the same endpoint, namely the finite addition permutation. -/
theorem finite_addition_endpoint {N : ℕ} (o : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) {w : List Site2}
    (hw : WiredStabilizes (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))
      (boxSites N) w) (x : FiniteWired.Active N) :
    heightAfter (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o)))
      w (FiniteWired.site x) = (((finiteAdditionEquiv o η).val x).val : ℤ) := by
  obtain ⟨v, hv, hend⟩ := exists_finite_addition_stabilization o η
  rw [heightAfter, wiredStabilizes_counts_unique hw hv]
  exact hend x

theorem finite_addition_preserves_law {N : ℕ} (o : FiniteWired.Active N) :
    (FiniteWired.law N).map (finiteAdditionEquiv o) = FiniteWired.law N := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro η
  rw [MeasureTheory.Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have he : (finiteAdditionEquiv o) ⁻¹' {η} = {(finiteAdditionEquiv o).symm η} := by
    ext x
    exact (finiteAdditionEquiv o).apply_eq_iff_eq_symm_apply
  rw [he, FiniteWired.law_singleton, FiniteWired.law_singleton]

end
end FiniteAvalanches.Sandpile.Waves
