import Thesis.RankCuts
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Thesis.Trees

open Finset

def rankValue (d : List ℕ) (i : ℕ) := (0 :: d.map (·-1))[i]!
def rankGap (d : List ℕ) (j : ℕ) := rankValue d (j+1) - rankValue d j

@[simp] theorem rankValue_zero (d : List ℕ) : rankValue d 0=0 := rfl

theorem value_mono {d : List ℕ} (hs : d.Pairwise (· ≤ ·)) {i j : ℕ} (h : i ≤ j)
    (hj : j ≤ d.length) : rankValue d i ≤ rankValue d j := by
  by_cases eq : i=j
  · simp [eq]
  let z := 0::d.map (·-1)
  have sorted : z.Pairwise (· ≤ ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨fun _ _ => Nat.zero_le _,?_⟩
    rw [List.pairwise_map]
    exact hs.imp (fun h => Nat.sub_le_sub_right h 1)
  have h₁ : i<z.length := by simp [z]; omega
  have h₂ : j<z.length := by simp [z]; omega
  change z[i]! ≤ z[j]!
  rw [getElem!_pos z i h₁,getElem!_pos z j h₂]
  exact List.pairwise_iff_getElem.mp sorted i j h₁ h₂ (by omega)

private theorem positive_rank_value {d : List ℕ} (hd : Admissible d) {i : ℕ} (hi : 1 ≤ i) (hk : i ≤ d.length) :
    (rankValue d i : ℤ) = (d[i-1]!:ℤ)-1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  have hj : j<d.length := by omega
  have hdeg := hd.2 _ (List.getElem_mem hj)
  unfold rankValue
  rw [getElem!_pos _ (j+1) (by simp; omega)]
  simp [getElem!_pos d j hj,List.getElem?_eq_getElem hj,Nat.cast_sub (by omega : 1 ≤ d[j])]

def rankEnergy (d r : List ℕ) : ℤ :=
  route (fun i j => squareDiff (rankValue d i) (rankValue d j)) 0 r 0

theorem sigma_rank_score {d r : List ℕ} (hd : Admissible d) (hr : r.Perm (List.range' 1 d.length))
    {n : ℕ} (G : Graph n) (hG : Realizes G (rankOrder d r)) :
    edgeIndex G 2 = sigmaBase d + rankEnergy d r := by
  have hp := rank_order_perm hr
  have hx : Admissible (rankOrder d r) := ⟨hd.1.trans_eq hp.length_eq.symm,fun _ h => hd.2 _ (hp.mem_iff.mp h)⟩
  rw [sigma_cycle G _ hx hG]
  have base : sigmaBase (rankOrder d r) = sigmaBase d := (hp.map _).sum_eq
  rw [base]
  have eq : (rankOrder d r).map (fun (a:ℕ) => (a:ℤ)-1) = r.map (fun i => (rankValue d i:ℤ)) := by
    simp only [rankOrder,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro i hi
    have H := (rank_mem hr i).mp hi
    exact (positive_rank_value hd H.1 H.2).symm
  rw [eq]
  have h := route_map squareDiff (fun i => (rankValue d i:ℤ)) 0 r 0
  simpa [rankEnergy] using congrArg (sigmaBase d + ·) h

private theorem prefix_mask (f : ℕ → ℤ) {k i : ℕ} (hi : i ≤ k) :
    (∑ j ∈ range k, if j < i then f j else 0) = ∑ j ∈ range i, f j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp; omega

private theorem gap_telescope {d : List ℕ} (hs : d.Pairwise (· ≤ ·)) {i : ℕ} (hi : i ≤ d.length) :
    (∑ j ∈ range i,(rankGap d j:ℤ)) = rankValue d i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ,ih (by omega),rankGap,Nat.cast_sub (value_mono hs (Nat.le_succ _) hi)]
    simp only [Nat.succ_eq_add_one]
    omega

private theorem edge_ordered {d : List ℕ} (hs : d.Pairwise (· ≤ ·)) {u v : ℕ} (huv : u≤v) (hv : v≤d.length) :
    squareDiff (rankValue d u) (rankValue d v) = ∑ j ∈ range d.length, ∑ l ∈ range d.length,
      (rankGap d j:ℤ)*rankGap d l*cutWeight j l u v := by
  let g (j : ℕ) : ℤ := rankGap d j
  let h (j : ℕ) : ℤ := if u≤j ∧ j < v then g j else 0
  have point (j : ℕ) : h j=(if j < v then g j else 0)-(if j < u then g j else 0) := by
    dsimp [h]; split_ifs <;> omega
  have val : (∑ j ∈ range d.length,h j) = (rankValue d v:ℤ)-rankValue d u := by
    simp_rw [point]
    rw [Finset.sum_sub_distrib,prefix_mask _ hv,prefix_mask _ (huv.trans hv),gap_telescope hs hv,
      gap_telescope hs (huv.trans hv)]
  have prod (j l : ℕ) : h j*h l=g j*g l*cutWeight j l u v := by
    have cover : covered u v j l ↔ (u≤j ∧ j < v) ∧ (u≤l ∧ l<v) := by
      unfold covered; omega
    by_cases hj : u≤j ∧ j < v <;> by_cases hl : u≤l ∧ l<v <;> simp [h,cutWeight,cover,hj,hl]
  rw [show squareDiff (rankValue d u) (rankValue d v) = (∑ j ∈ range d.length,h j)^2 by rw [val,squareDiff]; ring,
    pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum,prod,g]

private theorem edge_expansion {d : List ℕ} (hs : d.Pairwise (· ≤ ·)) {u v : ℕ} (hu : u≤d.length) (hv : v≤d.length) :
    squareDiff (rankValue d u) (rankValue d v) = ∑ j ∈ range d.length, ∑ l ∈ range d.length,
      (rankGap d j:ℤ)*rankGap d l*cutWeight j l u v := by
  rcases le_total u v with h|h
  · exact edge_ordered hs h hv
  · have eq := edge_ordered hs h hu
    simp_rw [cutWeight_symm _ _ v u] at eq
    rw [← eq,squareDiff,squareDiff]; ring

/-- Equation (3.6) with an ordered double sum, including both off-diagonal terms. -/
theorem sigma_cut_expansion {d r : List ℕ} (hs : d.Pairwise (· ≤ ·)) (hr : r.Perm (List.range' 1 d.length)) :
    rankEnergy d r = ∑ j ∈ range d.length, ∑ l ∈ range d.length,
      (rankGap d j:ℤ)*rankGap d l*crossings r j l := by
  let W (u v : ℕ) := squareDiff (rankValue d u) (rankValue d v)
  have general (a : ℕ) (s : List ℕ) (b : ℕ) (ha : a≤d.length) (hb : b≤d.length) (h : ∀ z ∈ s,z≤d.length) :
      route W a s b = ∑ j ∈ range d.length, ∑ l ∈ range d.length,
      (rankGap d j:ℤ)*rankGap d l*(route (cutWeight j l) a s b : ℕ) := by
    induction s generalizing a with
    | nil => exact edge_expansion hs ha hb
    | cons u s ih =>
      have hu := h u List.mem_cons_self
      rw [route,show W a u = _ from edge_expansion hs ha hu, ih u hu (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _
      rw [route,Nat.cast_add,mul_add]
  simp_rw [cuts_as_route]
  exact general 0 r 0 (Nat.zero_le _) (Nat.zero_le _) (fun z hz => ((rank_mem hr z).mp hz).2)

end Thesis.Trees
