import Thesis.WordMorphism

namespace Thesis.Words

private def power (x : Word) (k : ℕ) : Word := (List.replicate k x).flatten

private theorem power_left (x : Word) (k : ℕ) :
    power x (k+1) = x ++ power x k := by simp [power, List.replicate_succ]

private theorem power_right (x : Word) (k : ℕ) :
    power x (k+1) = power x k ++ x := by
  induction k with
  | zero => simp [power]
  | succ k ih => rw [power_left, ih, ← List.append_assoc, ← power_left, ih]

private theorem reverse_power (x : Word) (k : ℕ) : (power x k).reverse = power x.reverse k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [power_left, List.reverse_append, ih, ← power_right]

/-- If x moves across q as its reversal, so does any power of x. -/
private theorem slide (x q : Word) (h : x ++ q = q ++ x.reverse) (k : ℕ) :
    power x k ++ q = q ++ power x.reverse k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    rw [power_left, List.append_assoc, ih, ← List.append_assoc, h, List.append_assoc, ← power_left]

private theorem palindrome_power_append {x q : Word} (hq : Palindrome q)
    (h : x ++ q = q ++ x.reverse) (k : ℕ) : Palindrome (power x k ++ q) := by
  unfold Palindrome at *
  rw [List.reverse_append, reverse_power, hq, slide x q h]

/-- x and y end in opposite letter pairs. Their central parts p and q
are palindromes, and xq = yp is the common prefix of xy and yx. -/
private def CentralPair (x y : Word) : Prop :=
  ∃ (p q : Word) (u v : Bool), x = p ++ [u,v] ∧ y = q ++ [v,u] ∧
    Palindrome p ∧ Palindrome q ∧ x ++ q = y ++ p

private theorem central_step {x y : Word} (h : CentralPair x y) (k : ℕ) :
    CentralPair (power x k ++ y) x := by
  obtain ⟨p,q,u,v,hx,hy,hp,hq,hxy⟩ := h
  have hs : x ++ q = q ++ x.reverse := by
    rw [hxy, hy, hx, List.reverse_append, show p.reverse = p from hp]
    simp [List.append_assoc]
  refine ⟨power x k ++ q, p, v, u, ?_, hx, palindrome_power_append hq hs k, hp, ?_⟩
  · rw [hy, List.append_assoc]
  · rw [List.append_assoc, ← hxy, ← List.append_assoc, ← power_right,
        power_left, List.append_assoc]

private theorem central_base (a b : ℕ) :
    CentralPair (finiteWord (a+1) (b+1) 3) (finiteWord (a+1) (b+1) 2) := by
  let p : Word := List.replicate a false
  let A : Word := List.replicate (a+1) false
  let x := A ++ [true]
  have hp : p.reverse = p := List.reverse_replicate ..
  have hA : A.reverse = A := List.reverse_replicate ..
  have hA₁ : A = false :: p := List.replicate_succ
  have hA₂ : A = p ++ [false] := by rw [← hA, hA₁, List.reverse_cons, hp]
  have hs : x ++ A = A ++ x.reverse := by simp [x, hA, List.append_assoc]
  have h₂ : finiteWord (a+1) (b+1) 2 = x := by simp [finiteWord, x, A]
  have h₃ : finiteWord (a+1) (b+1) 3 = power x (b+1) ++ [false] := by
    rw [show (3 : ℕ) = 1+2 from rfl, finiteWord.eq_3, h₂]
    rfl
  rw [h₃, h₂]
  refine ⟨power x b ++ A, p, true, false, ?_, ?_, palindrome_power_append hA hs b, hp, ?_⟩
  · rw [power_right]; simp [x, List.append_assoc]
  · rw [show x = A ++ [true] from rfl, hA₂, List.append_assoc]; rfl
  · rw [List.append_assoc, List.singleton_append, ← hA₁, ← List.append_assoc, ← power_left]

private theorem central_iterates {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    CentralPair (finiteWord a b (n+3)) (finiteWord a b (n+2)) := by
  induction n with
  | zero =>
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
    exact central_base a b
  | succ n ih => exact central_step ih _

/-- Theorem 6.2.6. Removing two terminal letters from Fₙ gives a palindromic
prefix of the limiting word, including n=2 and a=1 (the empty prefix). -/
theorem truncated_palindrome {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {w : Stream} (hw : IsLimit a b w) (n : ℕ) (hn : 2 ≤ n) :
    let x := finiteWord a b n
    let y := x.take (x.length-2)
    segment w 0 y.length = y ∧ Palindrome y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 n]
  obtain ⟨_, q, _, _, _, hy, _, hq, _⟩ := central_iterates ha hb n
  have htake : (finiteWord a b (n+2)).take ((finiteWord a b (n+2)).length - 2) = q := by
    rw [hy]
    simp
  dsimp only
  rw [htake]
  refine ⟨?_, hq⟩
  have hlen : q.length ≤ (finiteWord a b (n+2)).length := by simp [hy]
  rw [← take_segment w 0 _ _ hlen, hw (n+1), hy, List.take_left]

theorem unbounded_palindromes {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {w : Stream} (hw : IsLimit a b w) (N : ℕ) :
    ∃ L ≥ N, Palindrome (segment w 0 L) := by
  let x := finiteWord a b (N+2)
  have hl : N+2 ≤ x.length := by
    have := finiteWord_length_lower ha hb (N+2)
    dsimp [x]; omega
  obtain ⟨heq, hp⟩ := truncated_palindrome ha hb hw (N+2) (by omega)
  refine ⟨(x.take (x.length-2)).length, ?_, heq.symm ▸ hp⟩
  simp only [List.length_take]
  omega

end Thesis.Words
