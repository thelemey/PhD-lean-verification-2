import Thesis.WordFrequency

namespace Thesis.Words

def NextHit (w : Stream) (c : Bool) (i j : ℕ) : Prop :=
  i < j ∧ w i = c ∧ w j = c ∧ ∀ k, i < k → k < j → w k ≠ c

def GapLength (w : Stream) (c : Bool) (n : ℕ) : Prop := ∃ i, NextHit w c i (i+n)

private theorem return_segment {w : Stream} {c : Bool} {i j : ℕ} (h : NextHit w c i j) :
    segment w i (j-i) = c :: List.replicate (j-i-1) (!c) := by
  obtain ⟨hij, hi, _, hmid⟩ := h
  apply List.ext_getElem
  · simp; omega
  · intro k hk _
    rw [segment_getElem]
    rw [segment_length] at hk
    cases k with
    | zero => simpa using hi
    | succ k =>
      simp only [List.getElem_cons_succ, List.getElem_replicate]
      have H := hmid (i+(k+1)) (by omega) (by omega)
      cases c <;> cases e : w (i+(k+1)) <;> simp_all

theorem returns_of_gap_lengths {w : Stream} {c : Bool} {g : ℕ}
    (hg : ∀ n, GapLength w c n ↔ n=g+1 ∨ n=g+2) (x : Word) :
    Returns w c x ↔ x = c :: List.replicate g (!c) ∨ x = c :: List.replicate (g+1) (!c) := by
  constructor
  · rintro ⟨i,j,hij,hi,hj,hmid,rfl⟩
    have h : NextHit w c i j := ⟨hij,hi,hj,hmid⟩
    have hp : GapLength w c (j-i) := ⟨i, by simpa [Nat.add_sub_of_le hij.le] using h⟩
    rw [return_segment h]
    rcases (hg _).mp hp with H | H <;> simp [H]
  · have realize (n : ℕ) (hn : GapLength w c n) :
        Returns w c (c :: List.replicate (n-1) (!c)) := by
      obtain ⟨i,h⟩ := hn
      exact ⟨i,i+n,h.1,h.2.1,h.2.2.1,h.2.2.2,by simpa using return_segment h⟩
    rintro (rfl | rfl)
    · simpa using realize (g+1) ((hg _).mpr (Or.inl rfl))
    · simpa using realize (g+2) ((hg _).mpr (Or.inr rfl))

theorem segment_add (w : Stream) (s n m : ℕ) :
    segment w s (n+m) = segment w s n ++ segment w (s+n) m := by
  simp [segment, List.range_add, List.map_map, Function.comp_def, Nat.add_assoc]

/-- The image of the ith source letter starts at this offset. -/
def boundary (a : ℕ) (src : Stream) (i : ℕ) := (morph a (segment src 0 i)).length

@[simp] theorem boundary_zero (a : ℕ) (src : Stream) : boundary a src 0 = 0 := rfl

theorem boundary_succ (a : ℕ) (src : Stream) (i : ℕ) :
    boundary a src (i+1) = boundary a src i + (if src i then 1 else a+1) := by
  simp only [boundary, segment_succ, Nat.zero_add, morph_append, List.length_append]
  cases h : src i <;> simp [morph]

theorem boundary_mono (a : ℕ) (src : Stream) : StrictMono (boundary a src) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [boundary_succ]
  split <;> omega

private theorem locate (a : ℕ) (src : Stream) (p : ℕ) :
    ∃ i, boundary a src i ≤ p ∧ p < boundary a src (i+1) := by
  induction p with
  | zero => exact ⟨0, by simp, by simpa using (boundary_mono a src) (Nat.zero_lt_succ 0)⟩
  | succ p ih =>
    obtain ⟨i,hle,hlt⟩ := ih
    by_cases h : p+1 < boundary a src (i+1)
    · exact ⟨i,by omega,h⟩
    · have eqp : p+1 = boundary a src (i+1) := by omega
      exact ⟨i+1,by omega,eqp ▸ (boundary_mono a src) (by omega)⟩

private theorem block_segment {a : ℕ} {src out : Stream} (hm : MapsStream a src out) (i : ℕ) :
    segment out (boundary a src i) (morph a [src i]).length = morph a [src i] := by
  have h := hm (i+1)
  dsimp only at h
  simp only [segment_succ src 0 i, Nat.zero_add, morph_append, List.length_append] at h
  rw [segment_add, hm i, Nat.zero_add] at h
  exact List.append_cancel_left h

theorem block_start {a : ℕ} (ha : 0 < a) {src out : Stream} (hm : MapsStream a src out) (i : ℕ) :
    out (boundary a src i) = false := by
  have h := block_segment hm i
  cases he : src i
  · obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    rw [he] at h
    have e := List.getElem_of_eq h (i:=0) (by simp [morph])
    simpa [morph, List.replicate_succ] using e
  · rw [he] at h
    have e := List.getElem_of_eq h (i:=0) (by simp [morph])
    simpa [morph] using e

theorem one_positions {a : ℕ} {src out : Stream} (hm : MapsStream a src out) (p : ℕ) :
    out p = true ↔ ∃ i, src i = false ∧ p = boundary a src i + a := by
  constructor
  · intro hp
    obtain ⟨i,hlo,hhi⟩ := locate a src p
    have hi := block_segment hm i
    rw [boundary_succ] at hhi
    cases he : src i
    · refine ⟨i,he,?_⟩
      simp [he] at hhi
      by_contra h
      have hoff : p - boundary a src i < a := by omega
      rw [he] at hi
      have e := List.getElem_of_eq hi (i:=p-boundary a src i) (by simp [morph]; omega)
      simp only [segment_getElem, Nat.add_sub_of_le hlo, morph, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Bool.false_eq_true, if_false] at e
      rw [List.getElem_append_left (by simpa using hoff), List.getElem_replicate] at e
      simp_all
    · simp [he] at hhi
      rw [he] at hi
      have e := List.getElem_of_eq hi (i:=0) (by simp [morph])
      have eqp : p = boundary a src i := by omega
      simp [morph, ← eqp] at e
      simp_all
  · rintro ⟨i,he,rfl⟩
    have h := block_segment hm i
    rw [he] at h
    have e := List.getElem_of_eq h (i:=a) (by simp [morph])
    simpa [morph, List.getElem_append_right] using e

theorem both_letters {a b : ℕ} {w : Stream} (hw : IsLimit a b w) :
    (∃ i, w i = false) ∧ ∃ i, w i = true := by
  have h₁ := hw 0
  have h₂ := hw 1
  have hword : finiteWord a b 2 = List.replicate a false ++ [true] := by simp [finiteWord]
  rw [hword] at h₂
  have f := List.getElem_of_eq h₁ (i:=0) (by simp [finiteWord])
  have t := List.getElem_of_eq h₂ (i:=a) (by simp)
  exact ⟨⟨0,by simpa [finiteWord] using f⟩,⟨a,by simpa [List.getElem_append_right] using t⟩⟩

theorem zero_gap_lengths {a : ℕ} (ha : 0 < a) {src out : Stream} (hm : MapsStream a src out)
    (hsrc : (∃ i, src i = false) ∧ ∃ i, src i = true) (n : ℕ) :
    GapLength out false n ↔ n=1 ∨ n=2 := by
  have next (p : ℕ) (hp : out p = true) : out (p+1) = false := by
    obtain ⟨i,hi,rfl⟩ := (one_positions hm p).mp hp
    simpa [boundary_succ, hi, Nat.add_assoc] using block_start ha hm (i+1)
  constructor
  · rintro ⟨i,hi,h₁,h₂,hmid⟩
    by_contra! hn
    have a₁ := hmid (i+1) (by omega) (by omega)
    have a₂ := hmid (i+2) (by omega) (by omega)
    exact a₂ (next (i+1) (by simpa using a₁))
  · rintro (rfl | rfl)
    · obtain ⟨i,hi⟩ := hsrc.2
      refine ⟨boundary a src i,by omega,block_start ha hm i,?_,by intros; omega⟩
      simpa [boundary_succ, hi] using block_start ha hm (i+1)
    · obtain ⟨i,hi⟩ := hsrc.1
      let p := boundary a src i + a
      have hp : out p = true := (one_positions hm p).mpr ⟨i,hi,rfl⟩
      have hp' : 0 < p := by dsimp [p]; omega
      refine ⟨p-1,by omega,?_,?_,?_⟩
      · cases H : out (p-1) with
        | false => rfl
        | true =>
          have E := next (p-1) H
          rw [show p-1+1=p by omega, hp] at E
          contradiction
      · simpa [show p-1+2=p+1 by omega] using next p hp
      · intro k hk hk'
        simp [show k = p by omega, hp]

/-- Theorem 6.2.4. The singleton 0 and the two-letter word 01 both actually occur. -/
theorem zero_returns {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {w : Stream} (hw : IsLimit a b w)
    (x : Word) : Returns w false x ↔ x=[false] ∨ x=[false,true] := by
  have hsrc := limitWord_isLimit hb ha
  have hm := morph_limit ha hb hsrc hw
  simpa using returns_of_gap_lengths (g:=0) (zero_gap_lengths ha hm (both_letters hsrc)) x

end Thesis.Words
