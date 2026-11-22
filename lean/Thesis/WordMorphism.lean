import Thesis.Words

namespace Thesis.Words

/-- The exponent on the step from Fₙ₊₁ to Fₙ₊₂. -/
private def copies (a b n : ℕ) := if n % 2 = 0 then a else b

private theorem copies_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    0 < copies a b n := by unfold copies; split <;> assumption

private theorem finiteWord_step (a b n : ℕ) :
    finiteWord a b (n+2) =
      (List.replicate (copies a b n) (finiteWord a b (n+1))).flatten ++ finiteWord a b n := rfl

theorem finiteWord_length_lower {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    max 1 n ≤ (finiteWord a b n).length := by
  induction n using Nat.twoStepInduction with
  | zero => simp [finiteWord]
  | one => simp [finiteWord]
  | more n ih₀ ih₁ =>
    rw [finiteWord_step]
    simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate_nat]
    have h := Nat.mul_le_mul_right (finiteWord a b (n+1)).length (copies_pos ha hb n)
    simp only [Nat.one_mul] at h
    omega

private theorem step_prefix {a b} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    (finiteWord a b (n+1)).IsPrefix (finiteWord a b (n+2)) := by
  rw [finiteWord_step]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (copies_pos ha hb n))
  rw [hk, List.replicate_succ, List.flatten_cons, List.append_assoc]
  exact ⟨_, rfl⟩

theorem finiteWord_prefix {a b} (ha : 0 < a) (hb : 0 < b) {m n : ℕ} (hmn : m ≤ n) :
    (finiteWord a b (m+1)).IsPrefix (finiteWord a b (n+1)) := by
  induction n, hmn using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (step_prefix ha hb n)

@[simp] theorem segment_length (w : Stream) (start len : ℕ) :
    (segment w start len).length = len := by simp [segment]

@[simp] theorem segment_getElem (w : Stream) (start len i : ℕ) (h : i < (segment w start len).length) :
    (segment w start len)[i] = w (start+i) := by simp [segment]

theorem take_segment (w : Stream) (start m n : ℕ) (h : m ≤ n) :
    (segment w start n).take m = segment w start m := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intros; simp

/-- At position i, Fᵢ₊₁ already contains a letter. All later iterates agree there. -/
def limitWord (a b : ℕ) (i : ℕ) : Bool := (finiteWord a b (i+1))[i]!

private theorem stabilized {a b} (ha : 0 < a) (hb : 0 < b) (n i : ℕ)
    (hi : i < (finiteWord a b (n+1)).length) :
    limitWord a b i = (finiteWord a b (n+1))[i] := by
  have ilen : i < (finiteWord a b (i+1)).length := by
    have := finiteWord_length_lower ha hb (i+1)
    omega
  rw [limitWord, getElem!_pos (finiteWord a b (i+1)) i ilen]
  rcases le_total i n with h | h
  · exact (finiteWord_prefix ha hb h).getElem ilen
  · exact ((finiteWord_prefix ha hb h).getElem hi).symm

theorem limitWord_isLimit {a b} (ha : 0 < a) (hb : 0 < b) :
    IsLimit a b (limitWord a b) := by
  intro n
  apply List.ext_getElem
  · simp
  · intro i _ hi
    simpa using stabilized ha hb n i hi

theorem limitWord_unique {a b} (ha : 0 < a) (hb : 0 < b) :
    ∃! w : Stream, IsLimit a b w := by
  refine ⟨limitWord a b, limitWord_isLimit ha hb, ?_⟩
  intro w hw
  funext i
  have hi : i < (finiteWord a b (i+1)).length := by
    have := finiteWord_length_lower ha hb (i+1)
    omega
  have e := congrArg (fun l : Word => l[i]!) (hw i)
  have hs : i < (segment w 0 (finiteWord a b (i+1)).length).length := by simpa
  change (segment w 0 (finiteWord a b (i+1)).length)[i]! = (finiteWord a b (i+1))[i]! at e
  rw [getElem!_pos (segment w 0 _) i hs, segment_getElem, Nat.zero_add] at e
  exact e

/-- Standard sequence (definition 6.1.1). Index n represents sₙ₋₁, starting with s₋₁. -/
def standardWord (directive : ℕ → ℕ) : ℕ → Word
  | 0 => [true]
  | 1 => [false]
  | n+2 => (List.replicate (directive (n+1)) (standardWord directive (n+1))).flatten ++
      standardWord directive n

def alternatingDirective (a b k : ℕ) : ℕ := if k % 2 = 1 then a else b

/-- Proposition 6.1.1. The finite standard words agree at every index and define
the same unique infinite word (using the prefix convention from F₁ onward). -/
theorem alternating_standard {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (∀ n, finiteWord a b n = standardWord (alternatingDirective a b) n) ∧
      ∃! w : Stream, ∀ n, let s := standardWord (alternatingDirective a b) (n+1)
                          segment w 0 s.length = s := by
  have heq : ∀ n, finiteWord a b n = standardWord (alternatingDirective a b) n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => rfl
    | more n ih₀ ih₁ =>
      rw [finiteWord_step, standardWord, ih₀, ih₁]
      have hd : copies a b n = alternatingDirective a b (n+1) := by
        unfold copies alternatingDirective
        split <;> split <;> first | rfl | omega
      rw [hd]
  refine ⟨heq, ?_⟩
  simpa only [IsLimit, heq] using limitWord_unique ha hb

@[simp] theorem morph_append (a : ℕ) (x y : Word) :
    morph a (x ++ y) = morph a x ++ morph a y := by simp [morph]

private theorem morph_power (a k : ℕ) (x : Word) :
    morph a (List.replicate k x).flatten = (List.replicate k (morph a x)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- Lemma 6.2.1. Each 0 contributes exactly d extra letters. -/
theorem morph_length (d : ℕ) (x : Word) :
    (morph d x).length = d * x.count false + x.length := by
  induction x with
  | nil => simp [morph]
  | cons bit tail ih =>
    cases bit <;> simp [morph, List.count_cons, Nat.mul_add] at ih ⊢ <;> omega

theorem morph_finiteWord (a b n : ℕ) :
    morph a (finiteWord b a n) = finiteWord a b (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [finiteWord, morph]
  | more n ih₀ ih₁ =>
    rw [finiteWord_step b a n, finiteWord_step a b (n+1), morph_append, morph_power, ih₀, ih₁]
    have hc : copies b a n = copies a b (n+1) := by
      unfold copies
      split <;> split <;> first | rfl | omega
    rw [hc]

private theorem prefix_of_image (a : ℕ) {x y : Word} (h : x.IsPrefix y) :
    (morph a x).IsPrefix (morph a y) := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨morph a t, (morph_append ..).symm⟩

/-- The image of every finite source prefix can be read in a sufficiently long target iterate. -/
theorem morph_limit {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {w out : Stream}
    (hw : IsLimit b a w) (hout : IsLimit a b out) : MapsStream a w out := by
  intro n
  let x := finiteWord b a (n+1)
  have hn : n ≤ x.length := by
    have := finiteWord_length_lower hb ha (n+1)
    dsimp [x]; omega
  have hs : (segment w 0 n).IsPrefix x := by
    rw [← take_segment w 0 n x.length hn, hw n]
    exact List.take_prefix ..
  have h := prefix_of_image a hs
  change (morph a (segment w 0 n)).IsPrefix (morph a (finiteWord b a (n+1))) at h
  rw [morph_finiteWord, ← hout (n+1)] at h
  rw [List.prefix_iff_eq_take] at h
  dsimp
  conv_rhs => rw [h]
  exact (take_segment out 0 _ _ (by simpa using (List.prefix_iff_eq_take.mpr h).length_le)).symm

/-- Theorem 6.1.1, both the finite identities and the equality of infinite words. -/
theorem word_morphism {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (∀ n, morph a (finiteWord b a n) = finiteWord a b (n+1)) ∧
      MapsStream a (limitWord b a) (limitWord a b) :=
  ⟨morph_finiteWord a b, morph_limit ha hb (limitWord_isLimit hb ha) (limitWord_isLimit ha hb)⟩

end Thesis.Words
