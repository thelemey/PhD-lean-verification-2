import Thesis.Bipartite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Thesis.Bipartite

open Finset

private theorem index_le_edge_count {p q} (E : Edges p q) (h : NoIsolates E) (r : ℕ) :
    index E r ≤ E.card * (max p q - 1) ^ r := by
  calc
    index E r ≤ ∑ _e ∈ E, (max p q - 1) ^ r := by
      apply Finset.sum_le_sum
      intro e _
      have hrow : rowDegree E e.1 ≤ q := by
        simpa [rowDegree] using (Finset.card_filter_le univ (fun j => (e.1, j) ∈ E))
      have hcol : colDegree E e.2 ≤ p := by
        simpa [colDegree] using (Finset.card_filter_le univ (fun i => (i, e.2) ∈ E))
      have := h.1 e.1
      have := h.2 e.2
      apply Nat.pow_le_pow_left
      unfold gap
      omega
    _ = _ := by simp

private theorem complete_index (p q r : ℕ) :
    index (univ : Edges p q) r = p * q * (max p q - min p q) ^ r := by
  simp [index, rowDegree, colDegree, gap, max_comm q p, min_comm q p]

/-- Theorem 5.2.3. Squaring the absolute gap gives the squared signed difference. -/
theorem sigma_complete (p q : ℕ) :
    index (univ : Edges p q) 2 = p * q * (gap p q) ^ 2 :=
  complete_index p q 2

/-- Proposition 5.3.1. The argument works for every positive integral power. -/
theorem bounds_and_equality {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (E : Edges p q) (h : NoIsolates E) {r : ℕ} (hr : 0 < r) :
    index E r ≤ p * q * (max p q - 1) ^ r ∧
      (index E r = p * q * (max p q - 1) ^ r ↔ IsStar E) := by
  have hcard : E.card ≤ p*q := by simpa using E.card_le_univ
  have edgeBound := index_le_edge_count E h r
  refine ⟨edgeBound.trans (Nat.mul_le_mul_right _ hcard), ?_⟩
  constructor
  · intro heq
    have hfull : E = univ := by
      apply E.eq_univ_of_card
      simp only [Fintype.card_prod, Fintype.card_fin]
      apply le_antisymm hcard
      by_cases hM : 1 < max p q
      · by_contra! fewer
        have hweight : 0 < (max p q - 1)^r := Nat.pow_pos (by omega)
        have strict := Nat.mul_lt_mul_of_pos_right fewer hweight
        omega
      · -- M = 1. The nonisolated vertex in the first part supplies the unique edge.
        obtain ⟨j, hj⟩ := Finset.card_pos.mp (h.1 ⟨0, hp⟩)
        have edge : ((⟨0, hp⟩ : Fin p), j) ∈ E := (Finset.mem_filter.mp hj).2
        have nonempty : 0 < E.card := Finset.card_pos.mpr ⟨_, edge⟩
        have hp1 : p = 1 := by omega
        have hq1 : q = 1 := by omega
        simpa [hp1, hq1] using nonempty
    refine ⟨hfull, ?_⟩
    rw [hfull, complete_index] at heq
    have hprod := Nat.mul_pos hp hq
    have hpow := Nat.eq_of_mul_eq_mul_left hprod heq
    have hgap := (Nat.pow_left_inj (Nat.ne_of_gt hr)).mp hpow
    omega
  · rintro ⟨rfl, hmin⟩
    rw [complete_index, hmin]

/-- Defence claim 6 uses the Albertson and sigma exponents separately. -/
theorem claim6 : Claim6 := by
  intro p q hp hq E h r hr
  apply bounds_and_equality hp hq E h
  simp at hr
  omega

end Thesis.Bipartite
