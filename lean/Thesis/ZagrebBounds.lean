import Thesis.TreeEquality
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Thesis.Trees

open Finset
open scoped Classical

private theorem equal_sum_iff {V : Type*} (s : Finset V) (f g : V → ℤ) (h : ∀ v ∈ s, f v ≤ g v) :
    (∑ v ∈ s, f v) = ∑ v ∈ s, g v ↔ ∀ v ∈ s, f v = g v := by
  constructor
  · intro e v hv
    by_contra ne
    exact (Finset.sum_lt_sum h ⟨v,hv,lt_of_le_of_ne (h v hv) ne⟩).ne e
  · exact Finset.sum_congr rfl

private theorem degree_pair_sum {n : ℕ} (G : Graph n) (ht : G.IsTree) (root : Fin n) :
    (∑ u ∈ univ.erase root, ((degree G u:ℤ) + degree G (parent ht root u))) =
    ∑ v, (degree G v : ℤ)^2 := by
  classical
  let d (v : Fin n) : ℤ := degree G v
  let A (u v : Fin n) : ℤ := if G.Adj u v then d u else 0
  have h := rooted_edge_sum ht root (fun u v => d u+d v) (fun _ _ => add_comm ..)
  have point (u v : Fin n) : (if G.Adj u v then d u + d v else 0) = A u v + A v u := by
    by_cases ha : G.Adj u v
    · simp [A,ha,ha.symm]
    · simp [A,ha,show ¬ G.Adj v u from fun e => ha e.symm]
  simp_rw [point,Finset.sum_add_distrib] at h
  rw [Finset.sum_comm (f:=fun u v => A v u)] at h
  have row (u : Fin n) : (∑ v, A u v) = (degree G u:ℤ)^2 := by
    simpa [A,d,pow_two] using (sum_incidence G d u)
  simp_rw [row] at h
  change (∑ u ∈ univ.erase root, (d u + d (parent ht root u))) = _
  rw [Finset.sum_add_distrib]
  linarith

/-- Proposition 2.1.2 before maximizing the root degree. Each bound comes with its equality criterion. -/
theorem irregularity_at_root {n : ℕ} (hn : 3 ≤ n) (G : Graph n) (ht : G.IsTree) (root : Fin n) :
    let M := ∑ v, (degree G v : ℤ)^2
    let lo := M-4*((n:ℤ)-1)+2*degree G root
    let hi := M-2*((n:ℤ)-1)
    lo ≤ edgeIndex G 1 ∧ edgeIndex G 1 ≤ hi ∧ (edgeIndex G 1=hi ↔ Star G) ∧
      (edgeIndex G 1=lo ↔ ∀ v (p : G.Walk root v), p.IsPath →
        (p.support.map (degree G)).Pairwise (· ≥ ·)) := by
  classical
  intro M lo hi
  let d (v : Fin n) : ℤ := degree G v
  let P := parent ht root
  let C := univ.erase root
  let m (v : Fin n) := min (d v) (d (P v))
  let H := ∑ v ∈ C, m v
  have pos (u : Fin n) : 1 ≤ d u := by
    dsimp [d]; exact_mod_cast (show 1 ≤ degree G u from tree_degree_pos (by omega) G ht u)
  have mlo (u : Fin n) : 1 ≤ m u := le_min (pos _) (pos _)
  have mhi (u : Fin n) : m u ≤ d u := min_le_left ..
  have irr : edgeIndex G 1 = M - 2*H := by
    have a := twice_edgeIndex G 1
    simp only [pow_one] at a
    have b := rooted_edge_sum ht root (fun u v => |d u-d v|) (fun u v => abs_sub_comm ..)
    change 2*edgeIndex G 1 = ∑ u, ∑ v, if G.Adj u v then |d u-d v| else 0 at a
    rw [b] at a
    have pt (v : Fin n) : |d v-d (P v)| = (d v+d (P v)) - 2*m v := by
      dsimp only [m]
      rcases le_total (d v) (d (P v)) with h|h
      · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]; ring
      · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]; ring
    change 2*edgeIndex G 1 = 2*∑ u ∈ C, |d u-d (P u)| at a
    simp_rw [pt] at a
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at a
    have hpair : (∑ u ∈ C, (d u + d (P u))) = M := degree_pair_sum G ht root
    rw [hpair] at a
    change 2*edgeIndex G 1 = 2*(M-2*H) at a
    omega
  have cardC : (∑ _ ∈ C,(1:ℤ)) = (n:ℤ)-1 := by simp [C,Nat.cast_sub (by omega : 1 ≤ n)]
  have childsum : (∑ v ∈ C,d v) = 2*((n:ℤ)-1)-d root := by
    have h := Finset.sum_erase_add univ d (Finset.mem_univ root)
    rw [tree_degree_sum G ht root] at h
    change (∑ v ∈ C, d v) + d root = 2*((n:ℤ)-1) at h
    omega
  have hcount : (n:ℤ)-1 ≤ H := cardC ▸ Finset.sum_le_sum (fun u _ => mlo u)
  have hcap : H ≤ 2*((n:ℤ)-1)-d root := childsum ▸ Finset.sum_le_sum (fun u _ => mhi u)
  change M-4*((n:ℤ)-1)+2*d root ≤ _ ∧ _ ≤ M-2*((n:ℤ)-1) ∧
    (_ = M-2*((n:ℤ)-1) ↔ _) ∧ (_ = M-4*((n:ℤ)-1)+2*d root ↔ _)
  refine ⟨by omega,by omega,?_,?_⟩
  · rw [← leaf_edges_iff_star hn G ht]
    have eq1 : edgeIndex G 1 = M-2*((n:ℤ)-1) ↔ (∑ _ ∈ C,(1:ℤ)) = H := by rw [cardC]; omega
    rw [eq1, equal_sum_iff C (fun _ => 1) m (fun v _ => mlo v)]
    have at_edge (u : Fin n) : (1:ℤ)=m u ↔ degree G u=1 ∨ degree G (P u)=1 := by
      have h := pos u
      have h' := pos (P u)
      dsimp [m,d] at *
      omega
    constructor
    · intro h u v hadj
      rcases edge_orientation ht root hadj with ⟨hu,he⟩|⟨hv,he⟩
      · have hh := (at_edge u).mp (h u (by simp [C,hu]))
        change P u=v at he
        rwa [he] at hh
      · have hh := (at_edge v).mp (h v (by simp [C,hv]))
        change P v=u at he
        rw [he] at hh
        exact hh.symm
    · intro h u hu
      exact (at_edge u).mpr (h u (P u) (parent_adj ht root (Finset.mem_erase.mp hu).1))
  · rw [← monotone_root_paths ht (degree G) root]
    have eq2 : edgeIndex G 1 = M-4*((n:ℤ)-1)+2*d root ↔ H = ∑ v ∈ C,d v := by rw [childsum]; omega
    rw [eq2, equal_sum_iff C m d (fun v _ => mhi v)]
    have pair (u : Fin n) : m u=d u ↔ degree G u ≤ degree G (P u) := by
      dsimp [m,d]
      exact_mod_cast (min_eq_left_iff (a:=degree G u) (b:=degree G (P u)))
    constructor
    · exact fun h u hu => (pair u).mp (h u (by simp [C, hu]))
    · exact fun h u hu => (pair u).mpr (h u (Finset.mem_erase.mp hu).1)

/-- Both bounds, with both directions of each equality case in §1.3(3). -/
theorem claim3 : Claim3 := by
  intro n hn G ht
  have hnon : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,by omega⟩,mem_univ _⟩
  obtain ⟨r,_,hr⟩ := Finset.exists_mem_eq_sup univ hnon (degree G)
  have H := irregularity_at_root hn G ht r
  dsimp only at H ⊢
  rw [hr]
  refine ⟨H.1,H.2.1,H.2.2.1,?_,?_⟩
  · intro h
    exact ⟨r,rfl,H.2.2.2.1 h⟩
  · rintro ⟨v,hv,hp⟩
    have e := (irregularity_at_root hn G ht v).2.2.2.2 hp
    rwa [hv] at e

/-- Theorem 2.1.1, including the lower equality criterion. -/
theorem max_degree_lower {n : ℕ} (hn : 3 ≤ n) (G : Graph n) (ht : G.IsTree) :
    let lo := (∑ v, (degree G v : ℤ)^2) - 4*((n:ℤ)-1) + 2*univ.sup (degree G)
    lo ≤ edgeIndex G 1 ∧ (edgeIndex G 1 = lo ↔ ∃ root, degree G root = univ.sup (degree G) ∧
      ∀ v (p : G.Walk root v), p.IsPath → (p.support.map (degree G)).Pairwise (· ≥ ·)) := by
  have h := claim3 n hn G ht
  exact ⟨h.1,h.2.2.2⟩

end Thesis.Trees
