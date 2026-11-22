import Thesis.PalindromeRecords
import Thesis.OneReturns

namespace Thesis.Words

/-- The defence statement §1.3(7), pp. 7–8, for one pair of
limiting streams. All specializations use the same explicit slope. -/
theorem claim7 : Claim7 := by
  intro a b ha hb
  have hw := limitWord_isLimit ha hb
  have hv := limitWord_isLimit hb ha
  have ⟨hmech,hcf⟩ := characteristic_slope ha hb hw
  have ⟨hf₁,hf₀⟩ := mechanical_frequencies hmech
  exact ⟨limitWord a b, limitWord b a, hw, hv, hmech, hcf, hf₁, hf₀,
    morph_limit ha hb hv hw, zero_returns ha hb hw, one_returns ha hb hw,
    truncated_palindrome ha hb hw, palindrome_iff_record hmech, unbounded_palindromes ha hb hw⟩

end Thesis.Words
