import Thesis.SigmaMinimum

namespace Thesis.Trees

private theorem value_succ {d : List ℕ} {i : ℕ} (hi : i<d.length) :
    rankValue d (i+1)=d[i]-1 := by
  unfold rankValue
  rw [getElem!_pos _ (i+1) (by simp; omega)]
  simp

theorem strict_gap {d : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·)) (hn : d.Nodup)
    {i : ℕ} (hi : i<d.length) : 0<rankGap d i := by
  unfold rankGap
  cases i with
  | zero =>
    rw [value_succ hi,rankValue_zero]
    have h := hd.2 _ (List.getElem_mem hi)
    omega
  | succ i =>
    have h₁ : i<d.length := by omega
    rw [value_succ hi,value_succ h₁]
    have le := List.pairwise_iff_getElem.mp hs i (i+1) h₁ hi (by omega)
    have ne := List.pairwise_iff_getElem.mp (show d.Pairwise (· ≠ ·) from hn) i (i+1) h₁ hi (by omega)
    have deg := hd.2 _ (List.getElem_mem h₁)
    omega

/-- Every edge of the closed rank order, including the two incident to zero. -/
def nearRanks (a b : ℕ) : Prop := a≤b+2 ∧ b≤a+2

def nearRoute (a : ℕ) : List ℕ → ℕ → Prop
  | [], b => nearRanks a b
  | v::s,b => nearRanks a v ∧ nearRoute v s b

theorem near_split (a : ℕ) (s : List ℕ) (v : ℕ) (t : List ℕ) (b : ℕ) :
    nearRoute a (s++v::t) b ↔ nearRoute a s v ∧ nearRoute v t b := by
  induction s generalizing a with
  | nil => rfl
  | cons u s ih => simp only [List.cons_append,nearRoute,ih,and_assoc]

private theorem near_edge {k a b : ℕ} (ha : a≤k) (hb : b≤k)
    (h : ∀ j, j+2<k → cutWeight j (j+2) a b=0) : nearRanks a b := by
  by_contra hn
  unfold nearRanks at hn
  have hj : min a b+2<max a b := by omega
  have eq := h (min a b) (by omega)
  have hc : covered a b (min a b) (min a b+2) := by unfold covered; omega
  simp [cutWeight,hc] at eq

private theorem near_route_zero {k : ℕ} (a : ℕ) (s : List ℕ) (b : ℕ) (ha : a≤k) (hb : b≤k)
    (hs : ∀ v ∈ s,v≤k)
    (hz : ∀ j, j+2<k → route (cutWeight j (j+2)) a s b=0) : nearRoute a s b := by
  induction s generalizing a with
  | nil => exact near_edge ha hb hz
  | cons v s ih =>
    have hv := hs v List.mem_cons_self
    have eq (j : ℕ) (hj : j+2<k) := Nat.add_eq_zero_iff.mp (hz j hj)
    exact ⟨near_edge ha hv (fun j hj => (eq j hj).1),ih v hv
      (fun u hu => hs u (List.mem_cons_of_mem _ hu)) (fun j hj => (eq j hj).2)⟩

theorem near_of_criterion {d r : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·))
    (hn : d.Nodup) (hr : r.Perm (List.range' 1 d.length)) (hc : cutCriterion d r) : nearRoute 0 r 0 := by
  apply near_route_zero (k:=d.length) 0 r 0 (Nat.zero_le _) (Nat.zero_le _)
    (fun v hv => ((rank_mem hr v).mp hv).2)
  intro j hj
  rw [← cuts_as_route]
  exact hc.2.2 j (j+2) le_rfl hj (Nat.mul_pos (strict_gap hd hs hn (by omega)) (strict_gap hd hs hn hj))

end Thesis.Trees
