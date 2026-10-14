import FiniteAvalanches.Electrical.Reference.CutConnectivity

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentRegularCut
open LatticeProb
open scoped Classical BigOperators
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)

/-- Original surviving IDs incident at the actual regular vertex. -/
def regularStar (x : {x : D // x ∉ P.val}) : Finset (Copy D P marked) :=
  Finset.univ.filter fun e => copyA D P marked e = .inr x ∨ copyB D P marked e = .inr x

/-- The copied star counts each original ID once, even for parallel neighbors. -/
theorem regularStar_card (x : {x : D // x ∉ P.val}) :
    (regularStar D P marked x).card = 4 := by
  classical
  have heq : Geometry.degree (copyA D P marked) (copyB D P marked) (.inr x) =
      ((regularStar D P marked x).card : ℝ) := by
    simp only [Geometry.degree, regularStar, Finset.card_eq_sum_ones,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases ha : copyA D P marked e = .inr x
    · have hb : copyB D P marked e ≠ .inr x :=
        fun hb => copy_loopless D P marked e (ha.trans hb.symm)
      simp [ha,hb]
    · by_cases hb : copyB D P marked e = .inr x <;> simp [ha,hb]
  have h := free_degree D P marked x
  rw [heq] at h
  exact_mod_cast h

/-- The raw quotient singleton cut is exactly the image of the surviving copied star. -/
theorem singleton_cut_eq_star_image (x : {x : D // x ∉ P.val}) :
    quotientCut D P {.inr x} = (regularStar D P marked x).image Subtype.val := by
  ext e
  constructor
  · intro he
    obtain ⟨hp,hcross⟩ := Finset.mem_filter.mp he
    have hi : project D P (originalA e) = .inr x ∨
        project D P (originalB e) = .inr x := by
      simpa only [Finset.mem_singleton] using hcross.elim
        (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    have hraw : originalA e = x.val.val ∨ originalB e = x.val.val :=
      hi.elim (fun h => Or.inl ((project_eq_free_iff D P x _).mp h))
        (fun h => Or.inr ((project_eq_free_iff D P x _).mp h))
    have hm := (free_incident_survives D P marked x e hraw).2
    let c : Copy D P marked := ⟨e, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2, hm⟩⟩
    exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  · intro he
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp he
    have hi := (Finset.mem_filter.mp hc).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp c.property).1,(Finset.mem_filter.mp c.property).2.1⟩,?_⟩
    change (copyA D P marked c ∈ ({.inr x} : Finset (Vertex D P)) ∧
      copyB D P marked c ∉ ({.inr x} : Finset (Vertex D P))) ∨
      (copyB D P marked c ∈ ({.inr x} : Finset (Vertex D P)) ∧
      copyA D P marked c ∉ ({.inr x} : Finset (Vertex D P)))
    rcases hi with hi | hi
    · exact Or.inl ⟨by simpa using hi, by simpa only [Finset.mem_singleton] using
        (fun hb => copy_loopless D P marked c (hi.trans hb.symm))⟩
    · exact Or.inr ⟨by simpa using hi, by simpa only [Finset.mem_singleton] using
        (fun ha => copy_loopless D P marked c (ha.trans hi.symm))⟩

theorem singleton_cut_card (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val}) :
    (quotientCut D P {.inr x}).card = 4 := by
  rw [singleton_cut_eq_star_image D P marked x]
  rw [Finset.card_image_of_injective _ Subtype.val_injective, regularStar_card]

/-- Actual retained copies whose two endpoints avoid the removed regular vertex. -/
def withoutRegular (x : {x : D // x ∉ P.val}) : Finset (Copy D P marked) :=
  Finset.univ.filter fun e => copyA D P marked e ≠ .inr x ∧ copyB D P marked e ≠ .inr x

/-- The two non-marked cuts adjacent to a separated component fit disjointly in the four-ID star. -/
theorem separated_side_impossible (x : {x : D // x ∉ P.val})
    (U : Finset (Vertex D P)) (ha : alpha D P ∉ U) (hx : Sum.inr x ∉ U)
    (hU : U.Nonempty)
    (hcross : ∀ e ∈ quotientCut D P U, e ≠ marked.val →
      project D P (originalA e) = .inr x ∨ project D P (originalB e) = .inr x) : False := by
  let A := (quotientCut D P U).erase marked.val
  let B := (quotientCut D P (insert (.inr x) U)).erase marked.val
  have ha' : alpha D P ∉ insert (.inr x) U := by
    simp only [Finset.mem_insert,not_or]
    exact ⟨by simp [alpha],ha⟩
  have lowerA := quotientCut_card_ge_four D P U ha hU
  have lowerB := quotientCut_card_ge_four D P (insert (.inr x) U) ha' (Finset.insert_nonempty _ _)
  have erase_loss (s : Finset OriginalCopy) : s.card ≤ (s.erase marked.val).card + 1 := by
    by_cases hm : marked.val ∈ s
    · exact (Finset.card_erase_add_one hm).ge
    · rw [Finset.erase_eq_of_notMem hm]; omega
  have la := erase_loss (quotientCut D P U)
  have lb := erase_loss (quotientCut D P (insert (.inr x) U))
  have union_sub : A ∪ B ⊆ quotientCut D P {.inr x} := by
    intro e he
    have hh : e ≠ marked.val ∧ e ∈ quotientCut D P U ∨
        e ≠ marked.val ∧ e ∈ quotientCut D P (insert (.inr x) U) := by
      simpa only [A,B,Finset.mem_union,Finset.mem_erase] using he
    have hp : e ∈ primalCopies D P := by
      rcases hh with h | h <;> exact (Finset.mem_filter.mp h.2).1
    have hne := (Finset.mem_filter.mp hp).2
    have hi : project D P (originalA e) = .inr x ∨ project D P (originalB e) = .inr x := by
      rcases hh with h | h
      · exact hcross e h.2 h.1
      · by_contra hn
        have hn' : project D P (originalA e) ≠ .inr x ∧
            project D P (originalB e) ≠ .inr x := not_or.mp hn
        have hu : e ∈ quotientCut D P U := by
          simpa only [quotientCut,Finset.mem_filter,Finset.mem_insert,hn'.1,hn'.2,
            false_or] using h.2
        exact hn (hcross e hu h.1)
    apply Finset.mem_filter.mpr
    refine ⟨hp,?_⟩
    simp only [Finset.mem_singleton]
    rcases hi with hi | hi
    · exact Or.inl ⟨hi,fun hb => hne (hi.trans hb.symm)⟩
    · exact Or.inr ⟨hi,fun ha => hne (ha.trans hi.symm)⟩
  have disj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    have hA := (Finset.mem_erase.mp heA).2
    have hB := (Finset.mem_erase.mp heB).2
    have hi := hcross e hA (Finset.mem_erase.mp heA).1
    have crA := (Finset.mem_filter.mp hA).2
    have crB := (Finset.mem_filter.mp hB).2
    rcases hi with hi | hi
    · simp only [hi,hx,false_and,or_false,Finset.mem_insert,true_and,
        not_true_eq_false,and_false] at crA crB
      tauto
    · simp only [hi,hx,and_false,false_or,Finset.mem_insert,true_or,true_and,
        not_true_eq_false,false_and] at crA crB
      tauto
  have upper := Finset.card_le_card union_sub
  rw [Finset.card_union_of_disjoint disj, singleton_cut_card D P marked x] at upper
  change (quotientCut D P U).card ≤ A.card + 1 at la
  change (quotientCut D P (insert (.inr x) U)).card ≤ B.card + 1 at lb
  omega

/-- Every remaining genuine source vertex reaches alpha without visiting the removed regular site. -/
theorem reaches_alpha_without_regular (x : {x : D // x ∉ P.val})
    (v : Vertex D P) (hv : v ≠ .inr x) :
    (StatementTypes.graph D P marked).reaches (withoutRegular D P marked x) (alpha D P) v := by
  let G := StatementTypes.graph D P marked
  let s := withoutRegular D P marked x
  by_contra hr
  let U : Finset (Vertex D P) := Finset.univ.filter fun z =>
    z ≠ .inr x ∧ ¬G.reaches s (alpha D P) z
  have memU (z : Vertex D P) : z ∈ U ↔ z ≠ .inr x ∧ ¬G.reaches s (alpha D P) z := by
    simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]
  have ha : alpha D P ∉ U := by
    intro hh
    exact ((memU _).mp hh).2 .refl
  have hx : .inr x ∉ U := by simp only [memU,ne_eq,not_true_eq_false,false_and,not_false_eq_true]
  have hU : U.Nonempty := ⟨v,(memU v).mpr ⟨hv,hr⟩⟩
  apply separated_side_impossible D P marked x U ha hx hU
  intro e he hm
  by_contra hn
  have hn' := not_or.mp hn
  obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp he
  let c : Copy D P marked := ⟨e,Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2,hm⟩⟩
  have hc : c ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn'⟩
  have hedge : G.reaches s (project D P (originalA e)) (project D P (originalB e)) :=
    .single ⟨c,hc,Or.inl ⟨rfl,rfl⟩⟩
  rcases hcut with ⟨hA,hB⟩ | ⟨hB,hA⟩
  · have hrB : G.reaches s (alpha D P) (project D P (originalB e)) := by
      by_contra hh
      exact hB ((memU _).mpr ⟨hn'.2,hh⟩)
    exact ((memU _).mp hA).2 (hrB.trans (G.reaches_symm hedge))
  · have hrA : G.reaches s (alpha D P) (project D P (originalA e)) := by
      by_contra hh
      exact hA ((memU _).mpr ⟨hn'.1,hh⟩)
    exact ((memU _).mp hB).2 (hrA.trans hedge)

/-- Vertex deletion preserves all copy identities and joins every remaining vertex pair. -/
theorem reaches_without_regular (x : {x : D // x ∉ P.val})
    (u v : Vertex D P) (hu : u ≠ .inr x) (hv : v ≠ .inr x) :
    (StatementTypes.graph D P marked).reaches (withoutRegular D P marked x) u v :=
  ((StatementTypes.graph D P marked).reaches_symm
    (reaches_alpha_without_regular D P marked x u hu)).trans
    (reaches_alpha_without_regular D P marked x v hv)

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.CurrentRegularCut
