import Thesis.RootedTree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Thesis.Trees

open Finset

private noncomputable def edgeTerm {n : ℕ} (G : Graph n) (r : ℕ) (u v : Fin n) : ℤ := by
  classical
  exact if u<v ∧ G.Adj u v then |(degree G u:ℤ)-degree G v|^r else 0

private theorem linear_le_square (z : ℤ) (hz : 0≤z) : z≤z^2 := by
  rcases hz.eq_or_lt with h|h
  · subst z; norm_num
  · nlinarith

private theorem degree_gap_le {n : ℕ} (hn : 2≤n) (G : Graph n) (ht : G.IsTree)
    (u v : Fin n) :
    |(degree G u:ℤ)-degree G v| ≤ ((univ.sup (degree G):ℕ):ℤ)-1 := by
  have up_u : degree G u≤univ.sup (degree G) := Finset.le_sup (Finset.mem_univ u)
  have up_v : degree G v≤univ.sup (degree G) := Finset.le_sup (Finset.mem_univ v)
  have pos_u := tree_degree_pos hn G ht u
  have pos_v := tree_degree_pos hn G ht v
  have up_u' : (degree G u:ℤ)≤univ.sup (degree G) := by exact_mod_cast up_u
  have up_v' : (degree G v:ℤ)≤univ.sup (degree G) := by exact_mod_cast up_v
  have pos_u' : (1:ℤ)≤degree G u := by exact_mod_cast pos_u
  have pos_v' : (1:ℤ)≤degree G v := by exact_mod_cast pos_v
  by_cases h : degree G u≤degree G v
  · have h' : (degree G u:ℤ)≤degree G v := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr h')]
    nlinarith
  · have h' : (degree G v:ℤ)≤degree G u := by exact_mod_cast Nat.le_of_not_ge h
    rw [abs_of_nonneg (sub_nonneg.mpr h')]
    nlinarith

/-- Theorem 3.3.2. On every tree, the sigma index lies between the
Albertson irregularity and `(Δ-1)` times that irregularity. -/
theorem sigma_irregularity_bounds {n : ℕ} (hn : 3≤n) (G : Graph n) (ht : G.IsTree) :
    edgeIndex G 1≤edgeIndex G 2 ∧
      edgeIndex G 2≤(((univ.sup (degree G):ℕ):ℤ)-1)*edgeIndex G 1 := by
  let Δ := univ.sup (degree G)
  have lower (u v : Fin n) : edgeTerm G 1 u v≤edgeTerm G 2 u v := by
    by_cases h : u<v ∧ G.Adj u v
    · simp only [edgeTerm,h,if_true,pow_one]
      exact linear_le_square _ (abs_nonneg _)
    · simp [edgeTerm,h]
  have upper (u v : Fin n) : edgeTerm G 2 u v≤((Δ:ℤ)-1)*edgeTerm G 1 u v := by
    by_cases h : u<v ∧ G.Adj u v
    · simp only [edgeTerm,h,if_true,pow_one]
      have nonneg := abs_nonneg ((degree G u:ℤ)-degree G v)
      have bound := degree_gap_le (by omega) G ht u v
      dsimp [Δ]
      nlinarith
    · simp [edgeTerm,h]
  change (∑ u,∑ v,edgeTerm G 1 u v)≤(∑ u,∑ v,edgeTerm G 2 u v) ∧
    (∑ u,∑ v,edgeTerm G 2 u v)≤((Δ:ℤ)-1)*(∑ u,∑ v,edgeTerm G 1 u v)
  refine ⟨sum_le_sum (fun u _ => sum_le_sum (fun v _ => lower u v)),?_⟩
  calc
    (∑ u,∑ v,edgeTerm G 2 u v) ≤ ∑ u,∑ v,((Δ:ℤ)-1)*edgeTerm G 1 u v :=
      sum_le_sum (fun u _ => sum_le_sum (fun v _ => upper u v))
    _ = ((Δ:ℤ)-1)*(∑ u,∑ v,edgeTerm G 1 u v) := by
      simp only [mul_sum]

end Thesis.Trees
