import Thesis.SigmaGeneralBounds
import Thesis.ZagrebBounds

namespace Thesis.Trees

open Finset

/-- Proposition 3.3.3. The sigma index inherits the sharp Zagreb lower bound
for the Albertson irregularity. -/
theorem sigma_zagreb_lower {n : ℕ} (hn : 3≤n) (G : Graph n) (ht : G.IsTree) :
    (∑ v, (degree G v:ℤ)^2) - 4*((n:ℤ)-1) + 2*univ.sup (degree G) ≤ edgeIndex G 2 := by
  exact (max_degree_lower hn G ht).1.trans (sigma_irregularity_bounds hn G ht).1

end Thesis.Trees
