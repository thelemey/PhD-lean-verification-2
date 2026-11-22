import Thesis.StandardWords
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Thesis.Words

noncomputable def alpha (a b : ℕ) : ℝ :=
  let P : ℝ := (a : ℝ) * b
  (P + Real.sqrt (P^2 + 4*P))/2

private theorem alpha_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < alpha a b := by
  unfold alpha
  positivity

private theorem alpha_quadratic {a b : ℕ} :
    alpha a b * alpha a b = (a : ℝ)*b*(alpha a b + 1) := by
  let P : ℝ := (a : ℝ)*b
  have h : 0 ≤ P^2 + 4*P := by dsimp [P]; positivity
  have hs := Real.sq_sqrt h
  change ((P + √(P^2+4*P))/2) * ((P + √(P^2+4*P))/2) = P * ((P + √(P^2+4*P))/2+1)
  nlinarith

private theorem discriminant_not_square (p : ℕ) (hp : 0 < p) : ¬ IsSquare (p^2 + 4*p) := by
  rintro ⟨k, hk⟩
  by_cases h : k ≤ p+1
  · have := Nat.mul_self_le_mul_self h
    nlinarith
  · have h₂ : p+2 ≤ k := by omega
    have := Nat.mul_self_le_mul_self h₂
    nlinarith

theorem alpha_irrational {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : Irrational (alpha a b) := by
  let P := a*b
  have hi := irrational_sqrt_natCast_iff.mpr (discriminant_not_square P (Nat.mul_pos ha hb))
  have h := ((hi.natCast_add P).div_natCast (m:=2) (by decide))
  simpa [P, alpha] using h

theorem slope_irrational {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : Irrational (slope a b) :=
  ((alpha_irrational ha hb).add_natCast b).natCast_div (Nat.ne_of_gt hb)

theorem slope_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < slope a b ∧ slope a b < 1 := by
  change 0 < (b : ℝ)/(alpha a b+b) ∧ (b : ℝ)/(alpha a b+b) < 1
  have hA := alpha_pos ha hb
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).2
    linarith

/-- Finite continued-fraction tail [0; b,a,b,a,…]. -/
private noncomputable def tail (b a : ℕ) : ℕ → ℝ
  | 0 => 0
  | n+1 => 1 / ((b : ℝ) + tail a b n)

private theorem tail_nonneg (a b n : ℕ) : 0 ≤ tail a b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [tail]
    exact div_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (ih b a))

private theorem cfTail_pos_index (a b j : ℕ) (hj : 0 < j) (n : ℕ) :
    cfTail a b j n = if j % 2 = 1 then tail b a n else tail a b n := by
  induction n generalizing j with
  | zero => split <;> rfl
  | succ n ih =>
    rw [cfTail, if_neg (Nat.ne_of_gt hj), ih (j+1) (by omega)]
    split <;> rename_i h
    · simp [h, show (j+1)%2 ≠ 1 by omega, tail]
    · simp [h, show (j+1)%2 = 1 by omega, tail]

private noncomputable def twoDigits (a b x : ℝ) := (a+x)/(b*(a+x)+1)

private theorem tail_two {a b : ℕ} (ha : 0 < a) (n : ℕ) :
    tail b a (n+2) = twoDigits a b (tail b a n) := by
  have hn := tail_nonneg b a n
  have h : 0 < (a : ℝ) + tail b a n := by positivity
  rw [tail, tail, twoDigits]
  field_simp

/-- Each pair of positive partial quotients contracts differences by at least a factor 4. -/
private theorem contract {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |twoDigits a b x - twoDigits a b y| ≤ |x-y|/4 := by
  have hd (z : ℝ) (hz : 0 ≤ z) : 2 ≤ b*(a+z)+1 := by
    have := mul_le_mul hb (show 1 ≤ a+z by linarith) zero_le_one (by linarith : 0 ≤ b)
    linarith
  have hx' := hd x hx
  have hy' := hd y hy
  have H : 4 ≤ (b*(a+x)+1)*(b*(a+y)+1) := by
    have := mul_le_mul hx' hy' (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ b*(a+x)+1)
    linarith
  have eq : twoDigits a b x - twoDigits a b y = (x-y)/((b*(a+x)+1)*(b*(a+y)+1)) := by
    unfold twoDigits
    field_simp [show b*(a+x)+1 ≠ 0 by linarith, show b*(a+y)+1 ≠ 0 by linarith]
    ring
  rw [eq, abs_div, abs_of_pos (show 0 < (b*(a+x)+1)*(b*(a+y)+1) by linarith)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) H

private noncomputable def fixedTail (a b : ℕ) := (a : ℝ) / alpha a b

private theorem fixedTail_properties {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ fixedTail a b ∧ fixedTail a b ≤ 1 ∧
    twoDigits a b (fixedTail a b) = fixedTail a b ∧
    1 / ((a : ℝ)+1+fixedTail a b) = slope a b := by
  have hA := alpha_pos ha hb
  have hQ := @alpha_quadratic a b
  have hα : (a : ℝ)*b < alpha a b := by
    by_contra! h
    have := mul_le_mul_of_nonneg_right h hA.le
    nlinarith [show (0 : ℝ) < (a : ℝ)*b by positivity]
  have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hf : 0 < fixedTail a b := div_pos ha' hA
  have he : (a : ℝ) + fixedTail a b = alpha a b / b := by
    unfold fixedTail
    field_simp [hA.ne', (show (b:ℝ) ≠ 0 by positivity)]
    nlinarith
  refine ⟨hf.le, (div_le_one hA).2 (by nlinarith [mul_le_mul_of_nonneg_left hb' ha'.le]), ?_, ?_⟩
  · rw [twoDigits, he, mul_div_cancel₀ _ (show (b:ℝ) ≠ 0 by positivity)]
    unfold fixedTail
    field_simp [hA.ne', (show (b:ℝ) ≠ 0 by positivity), (show alpha a b + 1 ≠ 0 by positivity)]
    nlinarith
  · rw [show (a:ℝ)+1+fixedTail a b = alpha a b / b + 1 by linarith]
    change 1 / (alpha a b / b + 1) = (b:ℝ)/(alpha a b+b)
    field_simp [hA.ne', (show (b:ℝ) ≠ 0 by positivity)]

theorem continued_fraction_slope {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Converges (cfTail a b 0) (slope a b) := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb
  obtain ⟨hf, hf₁, hfix, houter⟩ := fixedTail_properties ha hb
  have rate (n : ℕ) : |tail b a n - fixedTail a b| ≤ (1/4:ℝ)^(n/2) := by
    induction n using Nat.twoStepInduction with
    | zero => simpa [tail, abs_of_nonneg hf] using hf₁
    | one =>
      have h : (1:ℝ)/(b:ℝ) ≤ 1 := (div_le_one (by positivity)).2 hb'
      simp only [tail, add_zero, Nat.reduceDiv, pow_zero]
      rw [abs_le]; constructor <;> linarith [show 0 ≤ (1:ℝ)/(b:ℝ) by positivity]
    | more n ih _ =>
      rw [tail_two ha, ← hfix]
      have hc := contract ha' hb' (tail_nonneg b a n) hf
      rw [hfix] at hc ⊢
      rw [show (n+2)/2 = n/2+1 by omega, pow_succ]
      linarith
  intro ε hε
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/4:ℝ)<1)
  refine ⟨2*k+1, ?_⟩
  intro n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [cfTail, if_pos rfl, cfTail_pos_index a b 1 (by decide), if_pos (by decide : 1%2=1),
      Nat.cast_add, Nat.cast_one, ← houter]
  have ht := tail_nonneg b a n
  let d := (a:ℝ)+1
  have h₁ : 1 ≤ d + tail b a n := by dsimp [d]; linarith
  have h₂ : 1 ≤ d + fixedTail a b := by dsimp [d]; linarith
  have hprod : 1 ≤ (d+tail b a n)*(d+fixedTail a b) := by
    simpa only [one_mul] using mul_le_mul h₁ h₂ zero_le_one (by linarith : 0 ≤ d+tail b a n)
  have hdiff : 1/(d+tail b a n) - 1/(d+fixedTail a b) =
      - (tail b a n - fixedTail a b) / ((d+tail b a n)*(d+fixedTail a b)) := by
    field_simp [show d+tail b a n ≠ 0 by linarith, show d+fixedTail a b ≠ 0 by linarith]
  rw [hdiff, abs_div, abs_neg, abs_of_pos (by linarith : 0 < (d+tail b a n)*(d+fixedTail a b))]
  apply lt_of_le_of_lt (div_le_self (abs_nonneg _) hprod)
  exact (rate n).trans_lt ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : k ≤ n/2)).trans_lt hk)

private theorem alternating_fraction (a b j n : ℕ) :
    standardFraction (alternatingDirective a b) j n = cfTail a b j n := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [standardFraction, cfTail, ih]
    cases j with
    | zero => simp [alternatingDirective]
    | succ j =>
      simp only [Nat.succ_ne_zero, if_false, Nat.add_zero, alternatingDirective]
      split <;> split <;> first | rfl | omega

/-- Corollary 6.1.1 and theorem 6.3.2: the word is characteristic, with both
the continued-fraction expansion and the explicit radical value of the slope. -/
theorem characteristic_slope {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {w : Stream}
    (hw : IsLimit a b w) : Mechanical w (slope a b) ∧ Converges (cfTail a b 0) (slope a b) := by
  have hcf := continued_fraction_slope ha hb
  refine ⟨⟨(slope_bounds ha hb).1, (slope_bounds ha hb).2, slope_irrational ha hb, ?_⟩, hcf⟩
  apply Literature.standard_sequence_characteristic (alternatingDirective a b)
  · intro i _; unfold alternatingDirective; split <;> assumption
  · exact (slope_bounds ha hb).1
  · exact (slope_bounds ha hb).2
  · exact slope_irrational ha hb
  · simpa only [Converges, alternating_fraction] using hcf
  · intro n
    simpa only [← (alternating_standard ha hb).1] using hw n

end Thesis.Words
