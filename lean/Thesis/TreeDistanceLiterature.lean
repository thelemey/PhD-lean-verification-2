import Thesis.Trees

namespace Thesis.Trees

open Finset

noncomputable def wiener {n : ℕ} (G : Graph n) : ℤ :=
  ∑ u, ∑ v, if u<v then (G.dist u v : ℤ) else 0

def spineWeights (x : List ℕ) : List ℤ := x.map (fun (d:ℕ) => (d:ℤ)-1)

def cutProducts (w : List ℤ) : ℤ := ((List.range (w.length-1)).map fun i =>
  (w.take (i+1)).sum * (w.drop (i+1)).sum).sum

namespace Literature

/-- X.-D. Zhang, Y. Liu & M.-X. Han, The Maximum Wiener Index of Trees with
Given Degree Sequences, lemma 2.2, equations (2) and (3), pp. 4–5.
https://arxiv.org/pdf/0907.3772 -/
axiom caterpillar_wiener {n : ℕ} (G : Graph n) (x : List ℕ)
    (hx : Admissible x) (h : Realizes G x) :
  wiener G = ((n:ℤ)-1)^2 + cutProducts (spineWeights x)

end Literature
end Thesis.Trees
