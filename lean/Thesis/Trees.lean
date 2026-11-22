import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Order.Bounds.Basic

namespace Thesis.Trees

open Finset
open scoped BigOperators

/-- Vertex labels let the test u < v count each unordered pair once. -/
abbrev Graph (n : ℕ) := SimpleGraph (Fin n)

noncomputable def degree {n} (G : Graph n) (v : Fin n) : ℕ := by
  classical exact G.degree v

noncomputable def edgeIndex {n} (G : Graph n) (r : ℕ) : ℤ := by
  classical exact ∑ u, ∑ v, if u < v ∧ G.Adj u v then
    |(degree G u : ℤ) - degree G v| ^ r else 0

noncomputable def gutman {n} (G : Graph n) : ℤ := by
  classical exact ∑ u, ∑ v, if u < v then
    (degree G u : ℤ) * degree G v * G.dist u v else 0

/-- The ordered spine lists exactly the non-leaves of a tree, with their full degrees. -/
def Realizes {n} (G : Graph n) (x : List ℕ) : Prop :=
  G.IsTree ∧ ∃ s : List (Fin n), s.Nodup ∧ s.map (degree G) = x ∧
    (∀ v, v ∈ s ↔ 2 ≤ degree G v) ∧
    ∀ i (h : i + 1 < s.length), G.Adj (s.get ⟨i, by omega⟩) (s.get ⟨i+1, h⟩)

def Admissible (d : List ℕ) : Prop := 2 ≤ d.length ∧ ∀ a ∈ d, 2 ≤ a

/-- The set includes every labelled realization and every ordering of this multiset. -/
def values (f : {n : ℕ} → Graph n → ℤ) (d : List ℕ) : Set ℤ :=
  {v | ∃ (n : ℕ) (G : Graph n) (x : List ℕ), x.Perm d ∧ Realizes G x ∧ f G = v}

def spineTerms (x : List ℕ) (r : ℕ) : ℤ :=
  (x.map (fun d => ((d : ℤ) - 2) * ((d : ℤ) - 1) ^ r)).sum +
  ((x.head! : ℤ) - 1) ^ r + ((x.getLast! : ℤ) - 1) ^ r +
  (x.zipWith (fun a b => |(b : ℤ) - a| ^ r) x.tail).sum

/-- §1.3(1), propositions 2.2.1 and 3.1.1. -/
def Claim1 : Prop :=
  ∀ {n} (G : Graph n) (x : List ℕ), Admissible x → Realizes G x →
    ∀ r ∈ [1, 2], edgeIndex G r = spineTerms x r

/-- §1.3(2), theorem 2.2.2. The integer constant B can be negative. -/
def Claim2 : Prop :=
  ∀ d : List ℕ, Admissible d → d.Pairwise (· ≥ ·) →
    let h := (d.length + 1) / 2
    let B := (d.map (fun a => ((a : ℤ) - 1) * ((a : ℤ) - 2))).sum - 2
    let S := values (fun G => edgeIndex G 1) d
    IsLeast S (B + 2 * d.head!) ∧ IsGreatest S
      (B + 2 * (((d.take h).sum : ℤ) - (d.drop (d.length + 1 - h)).sum))

def Star {n} (G : Graph n) : Prop :=
  ∃ c, ∀ u v, G.Adj u v ↔ u ≠ v ∧ (u = c ∨ v = c)

/-- §1.3(3), proposition 2.1.2. Walk.support records the vertices in path order. -/
def Claim3 : Prop :=
  ∀ (n : ℕ) (_ : 3 ≤ n) (G : Graph n), G.IsTree →
    let Δ := univ.sup (degree G)
    let M₁ := ∑ v, (degree G v : ℤ) ^ 2
    let lo := M₁ - 4 * ((n : ℤ) - 1) + 2 * Δ
    let hi := M₁ - 2 * ((n : ℤ) - 1)
    let irr := edgeIndex G 1
    lo ≤ irr ∧ irr ≤ hi ∧ (irr = hi ↔ Star G) ∧
      (irr = lo ↔ ∃ root, degree G root = Δ ∧
        ∀ v (w : G.Walk root v), w.IsPath → (w.support.map (degree G)).Pairwise (· ≥ ·))

/-- Ranks start at 1. Rank 0 closes the cycle and has shifted degree 0. -/
def zigzagRanks (k : ℕ) : List ℕ :=
  let ranks := List.range' 1 k
  ranks.filter (fun i => i % 2 == 1) ++ (ranks.filter (fun i => i % 2 == 0)).reverse

def rankOrder (d ranks : List ℕ) : List ℕ := ranks.map (fun i => d[i-1]!)

def crossings (ranks : List ℕ) (j l : ℕ) : ℕ :=
  let cycle := 0 :: (ranks ++ [0])
  ((cycle.zip cycle.tail).filter (fun (a, b) =>
    min a b ≤ min j l && max j l < max a b)).length

def cutCriterion (d ranks : List ℕ) : Prop :=
  let z := 0 :: d.map (· - 1)
  let g := fun j : ℕ => z[j+1]! - z[j]!
  (∀ j < d.length, 0 < g j → crossings ranks j j = 2) ∧
  (∀ j, j + 1 < d.length → 0 < g j * g (j+1) → crossings ranks j (j+1) = 1) ∧
  ∀ j l, j + 2 ≤ l → l < d.length → 0 < g j * g l → crossings ranks j l = 0

/-- §1.3(4), theorem 3.3.3. Quantifying over labelled ranks covers ties. -/
def Claim4 : Prop :=
  ∀ d : List ℕ, Admissible d → d.Pairwise (· ≤ ·) →
    let z := rankOrder d (zigzagRanks d.length)
    let S := values (fun G => edgeIndex G 2) d
    (∃ (n : ℕ) (G : Graph n), Realizes G z ∧ IsLeast S (edgeIndex G 2)) ∧
    ∀ ranks : List ℕ, ranks.Perm (List.range' 1 d.length) →
      ∀ {n} (G : Graph n), Realizes G (rankOrder d ranks) →
        (IsLeast S (edgeIndex G 2) ↔ cutCriterion d ranks) ∧
        (d.Nodup → (IsLeast S (edgeIndex G 2) ↔
          rankOrder d ranks = z ∨ rankOrder d ranks = z.reverse))

def swapAt (x : List ℕ) (u v : ℕ) : List ℕ := (x.set u x[v]!).set v x[u]!

/-- With zero-based u and v, the changed cuts follow positions u through v-1. -/
def swapDifference (x : List ℕ) (u v : ℕ) : ℤ :=
  let weights := x.map (fun t => (t : ℤ) - 1)
  let n := 2 + weights.sum
  let δ := (x[v]! : ℤ) - x[u]!
  4 * δ * ((List.range' u (v-u)).map fun i => n - 2 * (1 + (weights.take (i+1)).sum) - δ).sum

def LocallyMaximal {n} (G : Graph n) (x : List ℕ) : Prop :=
  ∀ u v, u < v → v < x.length → ∀ H : Graph n, Realizes H (swapAt x u v) → gutman H ≤ gutman G

/-- §1.3(5), lemma 4.2.1 and example 4.2.1. -/
def Claim5 : Prop :=
  (∀ {n} (G : Graph n) (x : List ℕ), Admissible x → Realizes G x →
    (∀ u v, u < v → v < x.length → ∀ H : Graph n, Realizes H (swapAt x u v) →
      gutman H - gutman G = swapDifference x u v) ∧
    (IsGreatest (values gutman x) (gutman G) → LocallyMaximal G x)) ∧
  ∃ (n : ℕ) (G : Graph n) (x : List ℕ), Admissible x ∧ Realizes G x ∧
    LocallyMaximal G x ∧ ∃ y ∈ values gutman x, gutman G < y

end Thesis.Trees
