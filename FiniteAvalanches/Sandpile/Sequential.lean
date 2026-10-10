import FiniteAvalanches.Sandpile.Waves.Stabilization

/-! Sequential stabilization of arbitrary finite grain inputs. -/
namespace FiniteAvalanches.Sandpile
open LatticeProb LatticeProb.Sandpile FiniteAvalanches FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- Concatenating the two legal lists stabilizes the sum of their grain inputs. -/
theorem stabilizes_consecutive {η η' : StableField} {ξ ζ : Counts}
    {w v : List Site2} (hw : Stabilizes η ξ w)
    (he : ∀ x, heightAfter (initial η ξ) w x = ((η' x).val : ℤ))
    (hv : Stabilizes η' ζ v) : Stabilizes η (ξ+ζ) (w++v) ∧
      ∀ x, heightAfter (initial η (ξ+ζ)) (w++v) x = heightAfter (initial η' ζ) v x := by
  have hstate (x : Site2) :
      heightAfter (initial η (ξ+ζ)) w x = initial η' ζ x := by
    have h := he x
    simp only [heightAfter,initial,Finsupp.add_apply,Nat.cast_add] at h ⊢
    linarith only [h]
  have hlw : LegalList (initial η (ξ+ζ)) w := by
    intro k hk
    have h := hw.1 k hk
    have hz : (0 : ℤ) ≤ ζ w[k] := Nat.cast_nonneg _
    simp only [initial,Finsupp.add_apply,Nat.cast_add] at h ⊢
    linarith only [h,hz]
  have hlv : LegalList (heightAfter (initial η (ξ+ζ)) w) v := by
    intro k hk
    rw [hstate]
    exact hv.1 k hk
  have hend (x : Site2) :
      heightAfter (initial η (ξ+ζ)) (w++v) x = heightAfter (initial η' ζ) v x := by
    rw [height_after_append]
    exact congrArg (fun z => z + lap (fun y => (listCounts v y : ℤ)) x) (hstate x)
  refine ⟨⟨legal_list_append hlw hlv,?_⟩,hend⟩
  intro x
  change 0 ≤ heightAfter (initial η (ξ+ζ)) (w++v) x ∧
    heightAfter (initial η (ξ+ζ)) (w++v) x < 4
  rw [hend]
  exact hv.2 x

/-- Actual successive finite legal stabilizations give a finite stabilization of the sum. -/
theorem exists_stabilization_add_of_sequential (ξ ζ : Counts) (η : StabilizationDomain ξ)
    (hζ : ∃ v, Stabilizes (addition ξ η) ζ v) :
    ∃ w, Stabilizes η.val (ξ+ζ) w := by
  obtain ⟨w,hw,he⟩ := odometer_spec ξ η
  obtain ⟨v,hv⟩ := hζ
  have hs (x : Site2) :
      heightAfter (initial η.val ξ) w x = ((addition ξ η x).val : ℤ) := by
    rw [heightAfter,he,addition_eq]
  exact ⟨w++v,(stabilizes_consecutive hw hs hv).1⟩

/-- The full odometer records both successive legal lists. -/
theorem odometer_add_of_sequential (ξ ζ : Counts) (η : StabilizationDomain ξ)
    (hζ : ∃ v, Stabilizes (addition ξ η) ζ v) :
    odometer (ξ+ζ) ⟨η.val,exists_stabilization_add_of_sequential ξ ζ η hζ⟩ =
      odometer ξ η + odometer ζ ⟨addition ξ η,hζ⟩ := by
  obtain ⟨w,hw,he⟩ := odometer_spec ξ η
  obtain ⟨v,hv,hf⟩ := odometer_spec ζ ⟨addition ξ η,hζ⟩
  have hs (x : Site2) :
      heightAfter (initial η.val ξ) w x = ((addition ξ η x).val : ℤ) := by
    rw [heightAfter,he,addition_eq]
  rw [odometer_eq_counts (ξ+ζ) _ (stabilizes_consecutive hw hs hv).1,← he,← hf]
  ext x
  simp only [Finsupp.add_apply,listCounts_apply,List.count_append]

/-- The partial addition map agrees at every coordinate with successive addition. -/
theorem addition_add_of_sequential (ξ ζ : Counts) (η : StabilizationDomain ξ)
    (hζ : ∃ v, Stabilizes (addition ξ η) ζ v) :
    addition (ξ+ζ) ⟨η.val,exists_stabilization_add_of_sequential ξ ζ η hζ⟩ =
      addition ζ ⟨addition ξ η,hζ⟩ := by
  obtain ⟨w,hw,he⟩ := odometer_spec ξ η
  obtain ⟨v,hv,hf⟩ := odometer_spec ζ ⟨addition ξ η,hζ⟩
  have hs (x : Site2) :
      heightAfter (initial η.val ξ) w x = ((addition ξ η x).val : ℤ) := by
    rw [heightAfter,he,addition_eq]
  obtain ⟨hc,hend⟩ := stabilizes_consecutive hw hs hv
  funext x
  apply Fin.ext
  have ha := addition_eq (ξ+ζ)
    ⟨η.val,exists_stabilization_add_of_sequential ξ ζ η hζ⟩ x
  have hb := addition_eq ζ ⟨addition ξ η,hζ⟩ x
  have hau := odometer_eq_counts (ξ+ζ)
    ⟨η.val,exists_stabilization_add_of_sequential ξ ζ η hζ⟩ hc
  rw [hau] at ha
  rw [← hf] at hb
  have h := ha.trans ((hend x).trans hb.symm)
  exact_mod_cast h

end
end FiniteAvalanches.Sandpile
