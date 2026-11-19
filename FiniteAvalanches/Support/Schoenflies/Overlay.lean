/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License, Version 2.0.
Source: https://github.com/alonamaloh/schoenflies-lean, commit 05a43d29cde026618777db3d4e4316204ccca237, Schoenflies/Overlay.lean.
-/
import FiniteAvalanches.Support.Schoenflies.Subdivide
import FiniteAvalanches.Support.Schoenflies.SegmentOrder
import FiniteAvalanches.Support.Schoenflies.SegmentMeet
import FiniteAvalanches.Support.Schoenflies.Polygonal
import FiniteAvalanches.Support.Schoenflies.Graph.Drawing

/-! Plane geometry for the Jordan–Schönflies theorem. -/

 










open Metric Set

namespace Schoenflies

 












 
theorem splitAt_subset (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  classical
  unfold splitAt
  split_ifs with h
  · have hp : p ∈ P.seg := openSegment_subset_segment ℝ _ _ h
    intro Q hQ
    rcases List.mem_cons.1 hQ with rfl | hQ
    · exact ⟨(convex_segment P.1 P.2).segment_subset (left_mem_segment ℝ _ _) hp,
        openSegment_left_subset h⟩
    · rcases List.mem_singleton.1 hQ with rfl
      exact ⟨(convex_segment P.1 P.2).segment_subset hp (right_mem_segment ℝ _ _),
        openSegment_right_subset h⟩
  · intro Q hQ
    rcases List.mem_singleton.1 hQ with rfl
    exact ⟨subset_rfl, subset_rfl⟩

theorem splitAllAt_subset (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  intro Q hQ
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  exact ⟨P, hP, splitAt_subset p P Q hQP⟩

 

theorem subdivide_subset (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∃ P ∈ pieces, Q.seg ⊆ P.seg ∧ Q.interior ⊆ P.interior := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ => ⟨Q, hQ, subset_rfl, subset_rfl⟩
  | cons p ps ih =>
    intro Q hQ
    obtain ⟨R, hR, hQR, hQR'⟩ := ih (pieces := splitAllAt p pieces) Q hQ
    obtain ⟨P, hP, hRP, hRP'⟩ := splitAllAt_subset p pieces R hR
    exact ⟨P, hP, hQR.trans hRP, hQR'.trans hRP'⟩

 
theorem splitAt_ends (p : Plane) (P : Piece) :
    ∀ Q ∈ splitAt p P, ∀ z, (z = Q.1 ∨ z = Q.2) → z = p ∨ (z = P.1 ∨ z = P.2) := by
  classical
  unfold splitAt
  split_ifs with h
  · intro Q hQ z hz
    rcases List.mem_cons.1 hQ with rfl | hQ
    · rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · rcases List.mem_singleton.1 hQ with rfl
      rcases hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
  · intro Q hQ z hz
    rcases List.mem_singleton.1 hQ with rfl
    exact Or.inr hz

theorem splitAllAt_ends (p : Plane) (pieces : List Piece) :
    ∀ Q ∈ splitAllAt p pieces, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z = p ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  intro Q hQ z hz
  obtain ⟨P, hP, hQP⟩ := List.mem_flatMap.1 hQ
  rcases splitAt_ends p P Q hQP z hz with h | h
  · exact Or.inl h
  · exact Or.inr ⟨P, hP, h⟩

 

theorem subdivide_ends (pieces : List Piece) (points : List Plane) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) →
      z ∈ points ∨ ∃ P ∈ pieces, (z = P.1 ∨ z = P.2) := by
  induction points generalizing pieces with
  | nil => exact fun Q hQ z hz => Or.inr ⟨Q, hQ, hz⟩
  | cons p ps ih =>
    intro Q hQ z hz
    rcases ih (pieces := splitAllAt p pieces) Q hQ z hz with h | ⟨R, hR, hzR⟩
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases splitAllAt_ends p pieces R hR z hzR with rfl | ⟨P, hP, hzP⟩
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr ⟨P, hP, hzP⟩

 








 
def meetOf (P Q : Piece) : Set Plane := P.seg ∩ Q.seg

theorem meetOf_comm (P Q : Piece) : meetOf P Q = meetOf Q P := inter_comm _ _

 
def EndsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ z, (z = P.1 ∨ z = P.2) → z ∈ points

 

def MeetsAreCut (pieces : List Piece) (points : List Plane) : Prop :=
  ∀ P ∈ pieces, ∀ Q ∈ pieces, P ≠ Q → (meetOf P Q).Nonempty →
    ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points

 

theorem subdivide_ends_are_cuts {pieces : List Piece} {points : List Plane}
    (h : EndsAreCut pieces points) :
    ∀ Q ∈ subdivide pieces points, ∀ z, (z = Q.1 ∨ z = Q.2) → z ∈ points := by
  intro Q hQ z hz
  rcases subdivide_ends pieces points Q hQ z hz with h' | ⟨P, hP, hzP⟩
  · exact h'
  · exact h P hP z hzP

 






 
theorem exists_meet_points (P : Piece) (others : List Piece) :
    ∃ points : List Plane, ∀ Q ∈ others, (meetOf P Q).Nonempty →
      ∃ u v, meetOf P Q = segment ℝ u v ∧ u ∈ points ∧ v ∈ points := by
  induction others with
  | nil => exact ⟨[], by simp⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, htail⟩ := ih
    by_cases hR : (meetOf P R).Nonempty
    · obtain ⟨u, v, huv⟩ := segment_inter_segment P.1 P.2 R.1 R.2 hR
      refine ⟨u :: v :: tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact ⟨u, v, huv, by simp, by simp⟩
      · obtain ⟨s, t, hst, hs, ht⟩ := htail Q hQ hne
        exact ⟨s, t, hst, by simp [hs], by simp [ht]⟩
    · refine ⟨tailPoints, fun Q hQ hne => ?_⟩
      rcases List.mem_cons.1 hQ with rfl | hQ
      · exact absurd hne hR
      · exact htail Q hQ hne

 

theorem exists_cut_points (pieces : List Piece) :
    ∃ points : List Plane, EndsAreCut pieces points ∧ MeetsAreCut pieces points := by
  induction pieces with
  | nil => exact ⟨[], by simp [EndsAreCut], by simp [MeetsAreCut]⟩
  | cons R rs ih =>
    obtain ⟨tailPoints, hEnds, hMeets⟩ := ih
    obtain ⟨meetPoints, hHead⟩ := exists_meet_points R rs
    refine ⟨R.1 :: R.2 :: (meetPoints ++ tailPoints), fun P hP z hz => ?_,
      fun P hP Q hQ hPQ hne => ?_⟩
    · 
      rcases List.mem_cons.1 hP with rfl | hPt
      · rcases hz with rfl | rfl <;> simp
      · have := hEnds P hPt z hz
        simp [this]
    · 
      
      rcases List.mem_cons.1 hP with hPh | hPt
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · exact absurd (hPh.trans hQh.symm) hPQ
        · subst hPh
          obtain ⟨u, v, huv, hu, hv⟩ := hHead Q hQt hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩
      · rcases List.mem_cons.1 hQ with hQh | hQt
        · subst hQh
          have hne' : (meetOf Q P).Nonempty := by rwa [meetOf_comm]
          obtain ⟨u, v, huv, hu, hv⟩ := hHead P hPt hne'
          exact ⟨u, v, by rw [meetOf_comm]; exact huv, by simp [hu], by simp [hv]⟩
        · obtain ⟨u, v, huv, hu, hv⟩ := hMeets P hPt Q hQt hPQ hne
          exact ⟨u, v, huv, by simp [hu], by simp [hv]⟩

 






 



theorem subdivide_common_segment {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    ∃ A : Piece, A.Nondeg ∧ P.seg ⊆ A.seg ∧ Q.seg ⊆ A.seg := by
  obtain ⟨p, hp, hPseg, hPint⟩ := subdivide_subset pieces points P hP
  obtain ⟨q, hq, hQseg, hQint⟩ := subdivide_subset pieces points Q hQ
  by_cases hpq : p = q
  · subst hpq
    exact ⟨p, hnd p hp, hPseg, hQseg⟩
  
  have hxp : x ∈ p.seg := openSegment_subset_segment ℝ _ _ (hPint hxP)
  have hxq : x ∈ q.seg := openSegment_subset_segment ℝ _ _ (hQint hxQ)
  obtain ⟨u, v, huv, hu, hv⟩ := hMeets p hp q hq hpq ⟨x, hxp, hxq⟩
  have hux : u ∉ P.interior := subdivide_avoids points hnd u hu P hP
  have hvx : v ∉ P.interior := subdivide_avoids points hnd v hv P hP
  have huy : u ∉ Q.interior := subdivide_avoids points hnd u hu Q hQ
  have hvy : v ∉ Q.interior := subdivide_avoids points hnd v hv Q hQ
  
  have hxuv : x ∈ segment ℝ u v := huv ▸ ⟨hxp, hxq⟩
  have hxu : u ≠ x := fun h => hux (h ▸ hxP)
  have hxv : v ≠ x := fun h => hvx (h ▸ hxP)
  have hxopen : x ∈ openSegment ℝ u v := mem_openSegment_of_ne_left_right hxu hxv hxuv
  have huvne : u ≠ v := by
    rintro rfl
    rw [openSegment_same, mem_singleton_iff] at hxopen
    exact hxu hxopen.symm
  
  
  have hsubp : segment ℝ u v ⊆ p.seg := huv ▸ inter_subset_left
  have hsubq : segment ℝ u v ⊆ q.seg := huv ▸ inter_subset_right
  refine ⟨(u, v), huvne, ?_, ?_⟩
  · exact segment_inside_of_ends_outside (hnd p hp)
      (hPseg (left_mem_segment ℝ _ _)) (hPseg (right_mem_segment ℝ _ _))
      (hsubp (left_mem_segment ℝ _ _)) (hsubp (right_mem_segment ℝ _ _))
      hxP hxopen hux hvx
  · exact segment_inside_of_ends_outside (hnd q hq)
      (hQseg (left_mem_segment ℝ _ _)) (hQseg (right_mem_segment ℝ _ _))
      (hsubq (left_mem_segment ℝ _ _)) (hsubq (right_mem_segment ℝ _ _))
      hxQ hxopen huy hvy

 

theorem subdivide_separated {pieces : List Piece} {points : List Plane}
    (hnd : ∀ P ∈ pieces, P.Nondeg) (hEnds : EndsAreCut pieces points)
    (hMeets : MeetsAreCut pieces points)
    {P Q : Piece} (hP : P ∈ subdivide pieces points) (hQ : Q ∈ subdivide pieces points)
    {x : Plane} (hxP : x ∈ P.interior) (hxQ : x ∈ Q.interior) :
    P = Q ∨ P = (Q.2, Q.1) := by
  
  have cut : ∀ R ∈ subdivide pieces points, ∀ z, (z = R.1 ∨ z = R.2) → z ∈ points :=
    subdivide_ends_are_cuts hEnds
  have h₁ : Q.1 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inl rfl)) P hP
  have h₂ : Q.2 ∉ P.interior :=
    subdivide_avoids points hnd _ (cut Q hQ _ (Or.inr rfl)) P hP
  have h₃ : P.1 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inl rfl)) Q hQ
  have h₄ : P.2 ∉ Q.interior :=
    subdivide_avoids points hnd _ (cut P hP _ (Or.inr rfl)) Q hQ
  obtain ⟨A, hA, hPA, hQA⟩ := subdivide_common_segment hnd hMeets hP hQ hxP hxQ
  rcases same_ends_of_meeting_interiors hA
      (hPA (left_mem_segment ℝ _ _)) (hPA (right_mem_segment ℝ _ _))
      (hQA (left_mem_segment ℝ _ _)) (hQA (right_mem_segment ℝ _ _))
      hxP hxQ h₁ h₂ h₃ h₄ with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · exact Or.inl (Prod.ext e₁ e₂)
  · exact Or.inr (Prod.ext e₁ e₂)

end Schoenflies
