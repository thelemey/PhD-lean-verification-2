import Thesis.ZeroReturns

namespace Thesis.Words

private def lastPosition (a : ℕ) (src : Stream) (i : ℕ) := boundary a src i + a

private theorem lastPosition_mono (a : ℕ) (src : Stream) : StrictMono (lastPosition a src) :=
  fun _ _ h => Nat.add_lt_add_right ((boundary_mono a src) h) a

/-- Consecutive source zeros correspond to consecutive target ones. -/
private theorem next_correspondence {a : ℕ} {src out : Stream} (hm : MapsStream a src out)
    {i j : ℕ} (hi : src i = false) (hj : src j = false) :
    NextHit out true (lastPosition a src i) (lastPosition a src j) ↔ NextHit src false i j := by
  have hs := lastPosition_mono a src
  have atOne {k : ℕ} (hk : src k = false) : out (lastPosition a src k) = true :=
    (one_positions hm _).mpr ⟨k,hk,rfl⟩
  constructor
  · rintro ⟨hij,_,_,hmid⟩
    exact ⟨hs.lt_iff_lt.mp hij,hi,hj,fun k hk hk' he =>
      hmid (lastPosition a src k) (hs hk) (hs hk') (atOne he)⟩
  · rintro ⟨hij,_,_,hmid⟩
    refine ⟨hs hij,atOne hi,atOne hj,?_⟩
    intro p hp hp' he
    obtain ⟨k,hk,hp₀⟩ := (one_positions hm p).mp he
    change p = lastPosition a src k at hp₀
    subst p
    exact hmid k (hs.lt_iff_lt.mp hp) (hs.lt_iff_lt.mp hp') hk

private theorem lastPosition_gap {a : ℕ} {src : Stream} {i j : ℕ} (h : NextHit src false i j)
    (hg : j-i = 1 ∨ j-i = 2) : lastPosition a src j = lastPosition a src i + (a+(j-i)) := by
  have hi := h.2.1
  have hij := h.1
  unfold lastPosition
  rcases hg with hg | hg
  · have e : j=i+1 := by omega
    rw [hg,e,boundary_succ,hi]
    simp; omega
  · have e : j=i+1+1 := by omega
    have he : src (i+1) = true := by simpa using h.2.2.2 (i+1) (by omega) (by omega)
    rw [hg,e,boundary_succ,he,boundary_succ,hi]
    simp; omega

private theorem one_gap_lengths {a : ℕ} {src out : Stream} (hm : MapsStream a src out)
    (hg : ∀ n, GapLength src false n ↔ n = 1 ∨ n = 2) (n : ℕ) :
    GapLength out true n ↔ n=a+1 ∨ n=a+2 := by
  constructor
  · rintro ⟨p,h⟩
    obtain ⟨i,hi,pi⟩ := (one_positions hm _).mp h.2.1
    obtain ⟨j,hj,pj⟩ := (one_positions hm _).mp h.2.2.1
    change p = lastPosition a src i at pi
    change p+n = lastPosition a src j at pj
    have h' : NextHit out true (lastPosition a src i) (lastPosition a src j) := by rwa [← pi, ← pj]
    have H := (next_correspondence hm hi hj).mp h'
    have hg' := (hg (j-i)).mp ⟨i,by simpa [Nat.add_sub_of_le H.1.le] using H⟩
    have E := lastPosition_gap (a:=a) H hg'
    omega
  · have realize (d : ℕ) (hd : d=1 ∨ d=2) : GapLength out true (a+d) := by
      obtain ⟨i,H⟩ := (hg _).mpr hd
      have h' := (next_correspondence hm H.2.1 H.2.2.1).mpr H
      have E := lastPosition_gap (a:=a) H (by simpa using hd)
      simp only [Nat.add_sub_cancel_left] at E
      exact ⟨lastPosition a src i, by rwa [← E]⟩
    rintro (rfl | rfl)
    · exact realize 1 (Or.inl rfl)
    · exact realize 2 (Or.inr rfl)

/-- Theorem 6.2.5. There are exactly two returns to 1, and both lengths are realized. -/
theorem one_returns {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {w : Stream} (hw : IsLimit a b w)
    (x : Word) : Returns w true x ↔ x = true :: List.replicate a false ∨
      x = true :: List.replicate (a+1) false := by
  have hs := limitWord_isLimit hb ha
  have hswap := morph_limit hb ha hw hs
  have hm := morph_limit ha hb hs hw
  simpa using returns_of_gap_lengths (g:=a)
    (one_gap_lengths hm (zero_gap_lengths hb hswap (both_letters hw))) x

/-- Corollary 6.2.1. Swapping parameters leaves zero returns fixed and replaces
the exponent a by b in the two one returns. -/
theorem return_duality {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {w v : Stream}
    (hw : IsLimit a b w) (hv : IsLimit b a v) (x : Word) :
    (Returns w false x ↔ Returns v false x) ∧
    (Returns w true x ↔ x = true :: List.replicate a false ∨ x = true :: List.replicate (a+1) false) ∧
    (Returns v true x ↔ x = true :: List.replicate b false ∨ x = true :: List.replicate (b+1) false) :=
  ⟨(zero_returns ha hb hw x).trans (zero_returns hb ha hv x).symm,
    one_returns ha hb hw x, one_returns hb ha hv x⟩

end Thesis.Words
