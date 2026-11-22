import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Thesis.Bipartite

/-- A simple bipartite graph with labelled sides. Each pair represents one edge. -/
abbrev Edges (p q : ℕ) := Finset (Fin p × Fin q)

def rowDegree {p q} (E : Edges p q) (i : Fin p) : ℕ :=
  (Finset.univ.filter fun j => (i, j) ∈ E).card

def colDegree {p q} (E : Edges p q) (j : Fin q) : ℕ :=
  (Finset.univ.filter fun i => (i, j) ∈ E).card

def NoIsolates {p q} (E : Edges p q) : Prop :=
  (∀ i, 0 < rowDegree E i) ∧ ∀ j, 0 < colDegree E j

/-- Absolute degree difference in natural numbers. -/
def gap (x y : ℕ) : ℕ := max x y - min x y

def index {p q} (E : Edges p q) (r : ℕ) : ℕ :=
  ∑ e ∈ E, gap (rowDegree E e.1) (colDegree E e.2) ^ r

/-- In a bipartite presentation of K₁,M one side is a singleton and all pairs are edges. -/
def IsStar {p q} (E : Edges p q) : Prop :=
  E = Finset.univ ∧ min p q = 1

/-- §1.3(6), proposition 5.3.1. Each exponent has its own equality criterion. -/
def Claim6 : Prop :=
  ∀ (p q : ℕ) (_ : 0 < p) (_ : 0 < q) (E : Edges p q), NoIsolates E →
    ∀ r ∈ [1, 2], index E r ≤ p * q * (max p q - 1) ^ r ∧
      (index E r = p * q * (max p q - 1) ^ r ↔ IsStar E)

end Thesis.Bipartite
