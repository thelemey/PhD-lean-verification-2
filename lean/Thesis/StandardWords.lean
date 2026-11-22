import Thesis.WordMorphism

namespace Thesis.Words

/-- Truncation of [0; 1+d₁,d₂,d₃,…]. The extra one appears at the first digit only. -/
noncomputable def standardFraction (d : ℕ → ℕ) (j : ℕ) : ℕ → ℝ
  | 0 => 0
  | n+1 => 1 / ((d (j+1) + (if j = 0 then 1 else 0) : ℕ) + standardFraction d (j+1) n)

namespace Literature

/-- M. Lothaire, Algebraic Combinatorics on Words (Cambridge, 2002),
chapter 2, proposition 2.2.24, with the lower mechanical coding of cₜ.
For a positive directive sequence, the standard limit is characteristic at
the irrational slope determined by its continued fraction. The index n+1
below denotes sₙ; this excludes s₋₁ from the nested prefixes.
Source: https://ii.uni.wroc.pl/~aje/WordEq2017/papers/Lothaire_Algebraic.pdf -/
axiom standard_sequence_characteristic (d : ℕ → ℕ) (hd : ∀ i ≥ 1, 0 < d i)
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) (hirr : Irrational t)
    (hcf : Converges (standardFraction d 0) t) (w : Stream)
    (hw : ∀ n, let s := standardWord d (n+1)
               segment w 0 s.length = s) :
    ∀ i : ℕ, (if w i then (1 : ℤ) else 0) = ⌊((i : ℝ)+2)*t⌋ - ⌊((i : ℝ)+1)*t⌋

end Literature
end Thesis.Words
