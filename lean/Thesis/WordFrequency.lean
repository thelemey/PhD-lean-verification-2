import Thesis.WordSlope

namespace Thesis.Words

theorem segment_succ (w : Stream) (s n : ℕ) :
    segment w s (n+1) = segment w s n ++ [w (s+n)] := by
  simp [segment, List.range_succ]

def oneCount (w : Stream) (s n : ℕ) : ℕ := (segment w s n).count true

theorem oneCount_succ (w : Stream) (s n : ℕ) :
    oneCount w s (n+1) = oneCount w s n + (if w (s+n) then 1 else 0) := by
  cases h : w (s+n) <;> simp [oneCount, segment_succ, h]

theorem mechanical_count {w : Stream} {t : ℝ} (hw : Mechanical w t) (s n : ℕ) :
    (oneCount w s n : ℤ) = ⌊((s:ℝ) + n + 1)*t⌋ - ⌊((s:ℝ)+1)*t⌋ := by
  induction n with
  | zero => simp [oneCount, segment]
  | succ n ih =>
    rw [oneCount_succ, Nat.cast_add, ih]
    have hd := hw.2.2.2 (s+n)
    push_cast at hd ⊢
    rw [show (s:ℝ)+(n+1)+1 = (s:ℝ)+n+2 by ring]
    cases h : w (s+n) <;> simp [h] at hd ⊢ <;> omega

theorem prefix_ones {w : Stream} {t : ℝ} (hw : Mechanical w t) (n : ℕ) :
    (oneCount w 0 n : ℤ) = ⌊((n:ℝ)+1)*t⌋ := by
  have hz : ⌊t⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hw.1.le, hw.2.1⟩
  simpa [hz] using mechanical_count hw 0 n

theorem count_letters (x : Word) : x.count false + x.count true = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [List.count_cons, ih] <;> omega

private theorem frequency_of_discrepancy {w : Stream} {bit : Bool} {t : ℝ}
    (h : ∀ n : ℕ, |(((segment w 0 n).count bit : ℕ) : ℝ) - (n:ℝ)*t| ≤ 1) :
    Frequency w bit t := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1/ε)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : 1/ε < (n:ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hnpos : 0 < (n:ℝ) := lt_trans (by positivity : 0 < 1/ε) hn'
  have hεn : 1/(n:ℝ) < ε := (div_lt_iff₀ hnpos).mpr (by linarith [(div_lt_iff₀ hε).mp hn'])
  rw [show (((segment w 0 n).count bit : ℕ) : ℝ)/n - t =
      ((((segment w 0 n).count bit : ℕ) : ℝ) - n*t)/n by field_simp [hnpos.ne'], abs_div, abs_of_pos hnpos]
  exact (div_le_div_of_nonneg_right (h n) hnpos.le).trans_lt hεn

theorem mechanical_frequencies {w : Stream} {t : ℝ} (hw : Mechanical w t) :
    Frequency w true t ∧ Frequency w false (1-t) := by
  have bound (n : ℕ) : |(((segment w 0 n).count true : ℕ) : ℝ) - (n:ℝ)*t| ≤ 1 := by
    have hc := congrArg (Int.cast (R := ℝ)) (prefix_ones hw n)
    simp only [Int.cast_natCast] at hc
    change (((segment w 0 n).count true : ℕ) : ℝ) = _ at hc
    rw [hc, abs_le]
    constructor <;> linarith [Int.floor_le (((n:ℝ)+1)*t), Int.lt_floor_add_one (((n:ℝ)+1)*t), hw.1, hw.2.1]
  refine ⟨frequency_of_discrepancy bound, frequency_of_discrepancy (fun n => ?_)⟩
  have hc := count_letters (segment w 0 n)
  rw [segment_length] at hc
  have hc' : (((segment w 0 n).count false : ℕ) : ℝ) + ((segment w 0 n).count true : ℕ) = n := by
    exact_mod_cast hc
  rw [show (((segment w 0 n).count false : ℕ) : ℝ) - n*(1-t) =
        -((((segment w 0 n).count true : ℕ) : ℝ) - n*t) by linarith, abs_neg]
  exact bound n

/-- Theorem 6.2.1. Both frequencies are limits over all prefix lengths. -/
theorem letter_frequencies {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {w : Stream} (hw : IsLimit a b w) :
    Frequency w true ((b:ℝ)/(alpha a b+b)) ∧
    Frequency w false (alpha a b/(alpha a b+b)) := by
  have hf := mechanical_frequencies (characteristic_slope ha hb hw).1
  have hα : 0 < alpha a b := by unfold alpha; positivity
  change Frequency w true ((b:ℝ)/(alpha a b+b)) ∧ Frequency w false (1-(b:ℝ)/(alpha a b+b)) at hf
  rwa [show 1-(b:ℝ)/(alpha a b+b) = alpha a b/(alpha a b+b) by
    field_simp [show alpha a b + b ≠ 0 by positivity]] at hf

end Thesis.Words
