import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Irrational

namespace Thesis.Words

abbrev Word := List Bool
abbrev Stream := ℕ → Bool

/-- false is 0; true is 1. The first exponent, at n = 2, is a. -/
def finiteWord (a b : ℕ) : ℕ → Word
  | 0 => [true]
  | 1 => [false]
  | n + 2 => (List.replicate (if n % 2 = 0 then a else b) (finiteWord a b (n+1))).flatten
      ++ finiteWord a b n

def segment (w : Stream) (start len : ℕ) : Word :=
  (List.range len).map (fun i => w (start + i))

/-- The nested-prefix definition starts at F₁; F₀ has a different first letter. -/
def IsLimit (a b : ℕ) (w : Stream) : Prop :=
  ∀ n, segment w 0 (finiteWord a b (n+1)).length = finiteWord a b (n+1)

def morph (a : ℕ) (x : Word) : Word :=
  x.flatMap fun bit => if bit then [false] else List.replicate a false ++ [true]

/-- Every image of a finite prefix occurs at the beginning of the output stream. -/
def MapsStream (a : ℕ) (w out : Stream) : Prop :=
  ∀ n, let image := morph a (segment w 0 n)
       segment out 0 image.length = image

def Returns (w : Stream) (bit : Bool) (x : Word) : Prop :=
  ∃ i j, i < j ∧ w i = bit ∧ w j = bit ∧
    (∀ k, i < k → k < j → w k ≠ bit) ∧ segment w i (j-i) = x

def Converges (f : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, |f n - t| < ε

noncomputable def slope (a b : ℕ) : ℝ :=
  let P : ℝ := (a : ℝ) * b
  let α := (P + Real.sqrt (P^2 + 4*P)) / 2
  b / (α + b)

/-- [0; a+1,b,a,b,a,…] truncated after exactly len partial quotients. -/
noncomputable def cfTail (a b : ℕ) (j : ℕ) : ℕ → ℝ
  | 0 => 0
  | n+1 =>
    let digit := if j = 0 then a+1 else if j % 2 = 1 then b else a
    1 / ((digit : ℝ) + cfTail a b (j+1) n)

def Frequency (w : Stream) (bit : Bool) (t : ℝ) : Prop :=
  Converges (fun n => (((segment w 0 n).count bit : ℕ) : ℝ) / n) t

def Mechanical (w : Stream) (t : ℝ) : Prop :=
  0 < t ∧ t < 1 ∧ Irrational t ∧ ∀ i : ℕ,
    (if w i then (1 : ℤ) else 0) = ⌊((i : ℝ) + 2)*t⌋ - ⌊((i : ℝ) + 1)*t⌋

def Palindrome (x : Word) : Prop := x.reverse = x

def RecordFraction (t : ℝ) (L : ℕ) : Prop :=
  let f := fun j : ℕ => Int.fract ((j : ℝ) * t)
  (∀ j, 1 ≤ j → j ≤ L+1 → f (L+2) < f j) ∨
  (∀ j, 1 ≤ j → j ≤ L+1 → f j < f (L+2))

/-- §1.3(7), pp. 7–8. The limit word and its swapped-parameter counterpart exist.
All clauses use the same streams and slope. -/
def Claim7 : Prop :=
  ∀ (a b : ℕ), 0 < a → 0 < b →
    ∃ w w' : Stream, IsLimit a b w ∧ IsLimit b a w' ∧
      let t := slope a b
      Mechanical w t ∧ Converges (cfTail a b 0) t ∧
      Frequency w true t ∧ Frequency w false (1-t) ∧ MapsStream a w' w ∧
      (∀ x, Returns w false x ↔ x = [false] ∨ x = [false, true]) ∧
      (∀ x, Returns w true x ↔ x = true :: List.replicate a false ∨
        x = true :: List.replicate (a+1) false) ∧
      (∀ n ≥ 2, let x := finiteWord a b n
                let y := x.take (x.length-2)
                segment w 0 y.length = y ∧ Palindrome y) ∧
      (∀ L, Palindrome (segment w 0 L) ↔ RecordFraction t L) ∧
      (∀ N, ∃ L ≥ N, Palindrome (segment w 0 L))

end Thesis.Words
