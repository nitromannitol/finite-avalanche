import FiniteAvalanches.Paper.Current.RawPuncturedWave

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanchesCurrent.Punctured
open FiniteAvalanches.Sandpile
open FiniteAvalanches.Paper.RawPunctured

/-- The first-wave firing counts are the indicator of the forbidden core of
the resulting recurrent sandpile on the punctured box. -/
theorem inverse_waves {N : ℕ} {o : FiniteWired.Active N} (η : State o) :
    ∀ x : Site2, waveCounts η x = if x ∈ W (U η) then 1 else 0 := by
  exact FiniteAvalanches.Paper.RawPunctured.inverse_waves η

end FiniteAvalanchesCurrent.Punctured
