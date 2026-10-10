import FiniteAvalanches.Sandpile.Waves.FiniteAddition

/-! Sequential legal additions and finite commutation. -/
namespace FiniteAvalanches.Sandpile.Waves
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

private theorem legal_list_mono_on_list {s t : Site2 → ℤ} {w : List Site2}
    (hw : LegalList s w) (hst : ∀ x ∈ w, s x ≤ t x) : LegalList t w := by
  intro k hk
  have h := hw k hk
  have ht := hst w[k] (List.getElem_mem hk)
  linarith only [h,ht]

/-- Stabilizing one input, then another, is a legal stabilization of their sum. -/
theorem wired_stabilizes_consecutive {η η' : StableField} {ξ ζ : Counts}
    {V : Finset Site2} {w v : List Site2}
    (hw : WiredStabilizes η ξ V w)
    (he : ∀ x ∈ V, heightAfter (initial η ξ) w x = ((η' x).val : ℤ))
    (hv : WiredStabilizes η' ζ V v) :
    WiredStabilizes η (ξ+ζ) V (w++v) ∧
      ∀ x ∈ V, heightAfter (initial η (ξ+ζ)) (w++v) x =
        heightAfter (initial η' ζ) v x := by
  have hstate (x : Site2) (hx : x ∈ V) :
      heightAfter (initial η (ξ+ζ)) w x = initial η' ζ x := by
    have h := he x hx
    simp only [heightAfter,initial,Finsupp.add_apply,Nat.cast_add] at h ⊢
    linarith only [h]
  have hlw : LegalList (initial η (ξ+ζ)) w := by
    apply legal_list_mono_on_list hw.2.1
    intro x _
    simp only [initial,Finsupp.add_apply,Nat.cast_add]
    have hz : (0 : ℤ) ≤ ζ x := Nat.cast_nonneg _
    linarith only [hz]
  have hlv : LegalList (heightAfter (initial η (ξ+ζ)) w) v := by
    intro k hk
    rw [hstate v[k] (hv.1 _ (List.getElem_mem hk))]
    exact hv.2.1 k hk
  have hend (x : Site2) (hx : x ∈ V) :
      heightAfter (initial η (ξ+ζ)) (w++v) x = heightAfter (initial η' ζ) v x := by
    rw [height_after_append]
    exact congrArg (fun z => z + lap (fun y => (listCounts v y : ℤ)) x) (hstate x hx)
  refine ⟨⟨?_,legal_list_append hlw hlv,?_⟩,hend⟩
  · intro x hx
    exact (List.mem_append.mp hx).elim (hw.1 x) (hv.1 x)
  · intro x hx
    change 0 ≤ heightAfter (initial η (ξ+ζ)) (w++v) x ∧
      heightAfter (initial η (ξ+ζ)) (w++v) x < 4
    rw [hend x hx]
    exact hv.2.2 x hx

/-- The composed finite map is the endpoint of an actual legal two-grain stabilization. -/
theorem exists_two_addition_stabilization {N : ℕ} (o p : FiniteWired.Active N)
    (η : FiniteWired.Recurrent N) :
    ∃ w : List Site2,
      WiredStabilizes (FiniteWired.zeroExtend N η)
        (oneGrain (FiniteWired.site o)+oneGrain (FiniteWired.site p)) (boxSites N) w ∧
      ∀ x : FiniteWired.Active N,
        heightAfter (initial (FiniteWired.zeroExtend N η)
          (oneGrain (FiniteWired.site o)+oneGrain (FiniteWired.site p))) w (FiniteWired.site x) =
          (((finiteAdditionEquiv p (finiteAdditionEquiv o η)).val x).val : ℤ) := by
  obtain ⟨w,hw,he⟩ := exists_finite_addition_stabilization o η
  obtain ⟨v,hv,hf⟩ := exists_finite_addition_stabilization p (finiteAdditionEquiv o η)
  have hstate : ∀ x ∈ boxSites N,
      heightAfter (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o))) w x =
        ((FiniteWired.zeroExtend N (finiteAdditionEquiv o η) x).val : ℤ) := by
    intro x hx
    let a := FiniteWired.activeOfSite N x ((mem_box_sites N x).mp hx)
    change heightAfter (initial (FiniteWired.zeroExtend N η) (oneGrain (FiniteWired.site o)))
      w (FiniteWired.site a) = ((FiniteWired.zeroExtend N (finiteAdditionEquiv o η)
        (FiniteWired.site a)).val : ℤ)
    rw [FiniteWired.zeroExtend_site]
    exact he a
  obtain ⟨hfull,hend⟩ := wired_stabilizes_consecutive hw hstate hv
  exact ⟨w++v,hfull,fun x => (hend _ (site_mem_box x)).trans (hf x)⟩

theorem finite_addition_commute {N : ℕ} (o p : FiniteWired.Active N) :
    Function.Commute (finiteAdditionEquiv o) (finiteAdditionEquiv p) := by
  intro η
  obtain ⟨w,hw,he⟩ := exists_two_addition_stabilization o p η
  obtain ⟨v,hv,hf⟩ := exists_two_addition_stabilization p o η
  rw [add_comm (oneGrain (FiniteWired.site p))] at hv hf
  have hc := wiredStabilizes_counts_unique hw hv
  apply Subtype.ext
  funext x
  apply Fin.ext
  have h := hf x
  simp only [heightAfter] at h
  rw [← hc] at h
  have he' := he x
  simp only [heightAfter] at he'
  exact_mod_cast h.symm.trans he'

end
end FiniteAvalanches.Sandpile.Waves
