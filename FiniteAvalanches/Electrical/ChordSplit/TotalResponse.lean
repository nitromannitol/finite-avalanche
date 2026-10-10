import FiniteAvalanches.Electrical.SplitResponse

namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E]

theorem split_total_response_eq_energy (a b : E → V) (alpha beta : V)
    (hbeta : beta ≠ alpha) (side : E → Bool) (hc : (supportGraph a b).Preconnected) :
    responseEntry (fun e => splitEndpoint alpha side (a e) e)
      (fun e => splitEndpoint alpha side (b e) e) (splitTerminals alpha beta hbeta)
      (split_terminal_reachable a b alpha beta hbeta side hc) 1 1 =
    energy (fun e => splitEndpoint alpha side (a e) e)
      (fun e => splitEndpoint alpha side (b e) e)
      (responseBasis (fun e => splitEndpoint alpha side (a e) e)
        (fun e => splitEndpoint alpha side (b e) e) (splitTerminals alpha beta hbeta)
        (split_terminal_reachable a b alpha beta hbeta side hc) 1) := by
  have hr := splitTerminals_injective alpha beta hbeta
  have hE := three_terminal_response_energy (fun e => splitEndpoint alpha side (a e) e)
    (fun e => splitEndpoint alpha side (b e) e) (splitTerminals alpha beta hbeta) hr
    (split_terminal_reachable a b alpha beta hbeta side hc) (![0, 1, 0] : Fin 3 → ℝ)
  have hsum : (fun x => ∑ j : Fin 3, (![0, 1, 0] : Fin 3 → ℝ) j *
      responseBasis (fun e => splitEndpoint alpha side (a e) e)
        (fun e => splitEndpoint alpha side (b e) e) (splitTerminals alpha beta hbeta)
        (split_terminal_reachable a b alpha beta hbeta side hc) j x) =
      responseBasis (fun e => splitEndpoint alpha side (a e) e)
        (fun e => splitEndpoint alpha side (b e) e) (splitTerminals alpha beta hbeta)
        (split_terminal_reachable a b alpha beta hbeta side hc) 1 := by
    funext x
    simp [Fin.sum_univ_three]
  rw [hsum] at hE
  have hs := sum_responseEntry_eq_zero (fun e => splitEndpoint alpha side (a e) e)
    (fun e => splitEndpoint alpha side (b e) e) (splitTerminals alpha beta hbeta) hr
    (split_terminal_reachable a b alpha beta hbeta side hc) 1
  have h21 := responseEntry_comm (fun e => splitEndpoint alpha side (a e) e)
    (fun e => splitEndpoint alpha side (b e) e) (splitTerminals alpha beta hbeta) hr
    (split_terminal_reachable a b alpha beta hbeta side hc) 2 1
  simp only [Fin.sum_univ_three] at hs
  have ht2 : (![0, 1, 0] : Fin 3 → ℝ) 2 = 0 := rfl
  rw [ht2] at hE
  norm_num at hE
  linarith only [hE, hs, h21]

end FiniteAvalanches.Electrical
