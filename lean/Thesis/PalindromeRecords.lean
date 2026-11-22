import Thesis.WordFrequency
import Thesis.WordPalindromes

namespace Thesis.Words

private theorem palindrome_mirror (w : Stream) (L : ℕ) :
    Palindrome (segment w 0 L) ↔ ∀ i < L, w i = w (L-1-i) := by
  constructor
  · intro h i hi
    have e := List.getElem_of_eq h (i:=i) (by simpa using hi)
    simpa using e.symm
  · intro h
    apply List.ext_getElem
    · simp
    · intro i hi _
      simpa using (h i (by simpa using hi)).symm

/-- Equal counts in every prefix and its reflected suffix characterize a palindrome. -/
private theorem palindrome_counts (w : Stream) (L : ℕ) :
    Palindrome (segment w 0 L) ↔
    ∀ j ≤ L, oneCount w 0 j + oneCount w 0 (L-j) = oneCount w 0 L := by
  rw [palindrome_mirror]
  have step (i : ℕ) : oneCount w 0 (i+1) =
      oneCount w 0 i + (if w i then 1 else 0) := by simpa using oneCount_succ w 0 i
  constructor
  · intro h j
    induction j with
    | zero => simp [oneCount, segment]
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hmirror := h j (by omega)
      have hback := step (L-1-j)
      rw [show L-1-j+1 = L-j by omega] at hback
      rw [step, hmirror, show L-(j+1)=L-1-j by omega]
      omega
  · intro h j hj
    have hfirst := h j hj.le
    have hnext := h (j+1) hj
    have hback := step (L-1-j)
    rw [show L-1-j+1 = L-j by omega] at hback
    rw [step, show L-(j+1) = L-1-j by omega] at hnext
    cases h₁ : w j <;> cases h₂ : w (L-1-j) <;> simp_all <;> omega

private theorem floor_split (u v : ℝ) :
    ⌊v⌋ + ⌊u-v⌋ = ⌊u⌋ - (if Int.fract u < Int.fract v then 1 else 0) := by
  have hu := Int.fract_nonneg u
  have hv := Int.fract_nonneg v
  have hu' := Int.fract_lt_one u
  have hv' := Int.fract_lt_one v
  unfold Int.fract at *
  split <;> rename_i h
  · have he : ⌊u-v⌋ = ⌊u⌋-⌊v⌋-1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    omega
  · have he : ⌊u-v⌋ = ⌊u⌋-⌊v⌋ := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    omega

private theorem distinct_fract {t : ℝ} (ht : Irrational t) {i j : ℕ} (hij : i < j) :
    Int.fract ((i:ℝ)*t) ≠ Int.fract ((j:ℝ)*t) := by
  intro h
  apply (ht.natCast_mul (m:=j-i) (by omega)).ne_int (⌊(j:ℝ)*t⌋-⌊(i:ℝ)*t⌋)
  rw [Nat.cast_sub hij.le]
  unfold Int.fract at h
  push_cast
  linarith

/-- For a characteristic mechanical word, palindromic prefixes end exactly at a
new strict minimum or maximum of the sequence of fractional parts, including L=0. -/
theorem palindrome_iff_record {w : Stream} {t : ℝ} (hw : Mechanical w t) (L : ℕ) :
    Palindrome (segment w 0 L) ↔ RecordFraction t L := by
  classical
  let f (k : ℕ) := Int.fract ((k:ℝ)*t)
  let U := (((L:ℝ)+2)*t)
  have hU : f (L+2) = Int.fract U := by simp [f,U]
  let carry (k : ℕ) : ℤ := if f (L+2) < f k then 1 else 0
  have sum (j : ℕ) (hj : j ≤ L) :
      (oneCount w 0 j : ℤ) + (oneCount w 0 (L-j) : ℤ) = ⌊U⌋ - carry (j+1) := by
    rw [prefix_ones hw, prefix_ones hw, Nat.cast_sub hj]
    have e := floor_split U (((j:ℝ)+1)*t)
    rw [show U - (((j:ℝ)+1)*t) = (((L:ℝ)-j)+1)*t by dsimp [U]; ring] at e
    simpa [carry,hU,f] using e
  have hzero := sum 0 (Nat.zero_le _)
  have first : (oneCount w 0 L : ℤ) = ⌊U⌋ - carry 1 := by simpa [oneCount, segment] using hzero
  have key : Palindrome (segment w 0 L) ↔ ∀ k, 1 ≤ k → k ≤ L+1 → carry k = carry 1 := by
    rw [palindrome_counts]
    constructor
    · intro h k hk hk'
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hj : j ≤ L := by omega
      have eqn : (oneCount w 0 j : ℤ) + (oneCount w 0 (L-j) : ℤ) = (oneCount w 0 L : ℤ) := by
        exact_mod_cast h j hj
      change carry (j+1) = carry 1
      have hs := sum j hj
      rw [eqn, first] at hs
      omega
    · intro h j hj
      have e := sum j hj
      rw [h (j+1) (by omega) (by omega), ← first] at e
      exact_mod_cast e
  rw [key]
  change (∀ k, 1 ≤ k → k ≤ L+1 → carry k = carry 1) ↔
    (∀ k, 1 ≤ k → k ≤ L+1 → f (L+2) < f k) ∨
    (∀ k, 1 ≤ k → k ≤ L+1 → f k < f (L+2))
  have ne (k : ℕ) (hk : k ≤ L+1) : f k ≠ f (L+2) := distinct_fract hw.2.2.1 (by omega)
  constructor
  · intro h
    by_cases h₁ : f (L+2) < f 1
    · left
      intro k hk hk'
      simpa [carry, h₁] using h k hk hk'
    · right
      intro k hk hk'
      exact lt_of_le_of_ne (by simpa [carry, h₁] using h k hk hk') (ne k hk')
  · rintro (h | h) k hk hk'
    · simp [carry, h k hk hk', h 1 (by omega) (by omega)]
    · simp [carry, (h k hk hk').asymm, (h 1 (by omega) (by omega)).asymm]

/-- Corollary 6.2.2, including the existence of arbitrarily long palindromic prefixes. -/
theorem palindrome_records {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {w : Stream} (hw : IsLimit a b w) :
    (∀ L, Palindrome (segment w 0 L) ↔ RecordFraction (slope a b) L) ∧
    ∀ N, ∃ L ≥ N, Palindrome (segment w 0 L) :=
  ⟨palindrome_iff_record (characteristic_slope ha hb hw).1, unbounded_palindromes ha hb hw⟩

end Thesis.Words
