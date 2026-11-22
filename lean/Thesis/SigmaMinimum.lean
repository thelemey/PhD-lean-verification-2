import Thesis.SigmaExpansion
import Thesis.ZigzagCuts
import Thesis.CaterpillarModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Thesis.Trees

open Finset

theorem crossings_symm (r : List ℕ) (i j : ℕ) : crossings r i j=crossings r j i := by
  simp only [crossings,min_comm i j,max_comm i j]

private theorem zigzag_below {k : ℕ} (hk : 2 ≤ k) {r : List ℕ} (hr : r.Perm (List.range' 1 k))
    (j l : ℕ) (hj : j<k) (hl : l<k) : crossings (zigzagRanks k) j l ≤ crossings r j l := by
  wlog h : j ≤ l generalizing j l
  · rw [crossings_symm _ j l,crossings_symm r j l]
    exact this l j hl hj (by omega)
  obtain ⟨n,he⟩ : ∃ n, k=n+2 := ⟨k-2,by omega⟩
  subst k
  rw [zigzag_crossings_ordered n j l h]
  simp only [zigzagCount,max_eq_right h,if_pos hl]
  split
  · rename_i e; subst l; exact diagonal_cut_lower hr j hj
  · split
    · rename_i e; have eq : l=j+1 := by omega
      subst l; exact next_cut_lower hr j hl
    · omega

private theorem strict_sum {ι : Type*} (s : Finset ι) (f g : ι → ℤ) (h : ∀ i ∈ s, f i ≤ g i) :
    (∑ i ∈ s, f i) = ∑ i ∈ s, g i ↔ ∀ i ∈ s, f i=g i := by
  constructor
  · intro e i hi
    by_contra ne
    exact (Finset.sum_lt_sum h ⟨i,hi,lt_of_le_of_ne (h i hi) ne⟩).ne e
  · exact Finset.sum_congr rfl

private theorem energy_comparison {d r : List ℕ} (hk : 2 ≤ d.length) (hs : d.Pairwise (· ≤ ·))
    (hr : r.Perm (List.range' 1 d.length)) :
    let z := zigzagRanks d.length
    rankEnergy d z ≤ rankEnergy d r ∧
      (rankEnergy d z=rankEnergy d r ↔
        ∀ j < d.length, ∀ l < d.length, 0 < rankGap d j*rankGap d l →
          crossings r j l = crossings z j l) := by
  intro z
  rw [sigma_cut_expansion hs (zigzag_perm d.length),sigma_cut_expansion hs hr]
  let C := range d.length
  let A (s : List ℕ) (j l : ℕ) : ℤ := (rankGap d j:ℤ)*rankGap d l*crossings s j l
  have point (j : ℕ) (hj : j ∈ C) (l : ℕ) (hl : l ∈ C) : A z j l ≤ A r j l := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast zigzag_below hk hr j l (mem_range.mp hj) (mem_range.mp hl)
  have row (j : ℕ) (hj : j ∈ C) : (∑ l ∈ C,A z j l) ≤ ∑ l ∈ C,A r j l :=
    sum_le_sum (point j hj)
  refine ⟨sum_le_sum row,?_⟩
  change ((∑ j ∈ C,∑ l ∈ C,A z j l)=∑ j ∈ C,∑ l ∈ C,A r j l) ↔ _
  rw [strict_sum C _ _ row]
  constructor
  · intro e j hj l hl hp
    have hj' : j∈C := mem_range.mpr hj
    have h := (strict_sum C _ _ (point j hj')).mp (e j hj') l (mem_range.mpr hl)
    have hpos : (0:ℤ)<(rankGap d j:ℤ)*rankGap d l := by exact_mod_cast hp
    dsimp [A] at h
    exact_mod_cast (mul_left_cancel₀ hpos.ne' h).symm
  · intro e j hj
    apply (strict_sum C _ _ (point j hj)).mpr
    intro l hl
    by_cases h : 0<rankGap d j*rankGap d l
    · exact congrArg (fun (v:ℕ) => (rankGap d j:ℤ)*rankGap d l*v)
        (e j (mem_range.mp hj) l (mem_range.mp hl) h).symm
    · have eq : (rankGap d j:ℤ)*rankGap d l=0 := by exact_mod_cast Nat.eq_zero_of_not_pos h
      simp [A,eq]

theorem energy_criterion {d r : List ℕ} (hk : 2≤d.length) (hs : d.Pairwise (· ≤ ·))
    (hr : r.Perm (List.range' 1 d.length)) :
    rankEnergy d (zigzagRanks d.length)=rankEnergy d r ↔ cutCriterion d r := by
  rw [(energy_comparison hk hs hr).2]
  change _ ↔ (∀ j<d.length, 0<rankGap d j → crossings r j j=2) ∧
    (∀ j, j+1<d.length → 0<rankGap d j*rankGap d (j+1) → crossings r j (j+1)=1) ∧
    ∀ j l, j+2≤l → l<d.length → 0<rankGap d j*rankGap d l → crossings r j l=0
  have formula (j l : ℕ) (h : j≤l) (hl : l<d.length) :
      crossings (zigzagRanks d.length) j l = if j=l then 2 else if j+1=l then 1 else 0 := by
    have he : d.length=(d.length-2)+2 := by omega
    have hh := zigzag_crossings_ordered (d.length-2) j l h
    rw [← he] at hh
    simpa [zigzagCount,max_eq_right h,hl,show ¬l+1=j by omega] using hh
  constructor
  · intro h
    refine ⟨fun j hj hp => ?_,fun j hj hp => ?_,fun j l hj hl hp => ?_⟩
    · rw [h j hj j hj (Nat.mul_pos hp hp),formula j j le_rfl hj,if_pos rfl]
    · rw [h j (by omega) (j+1) hj hp,formula j (j+1) (by omega) hj,if_neg (by omega),if_pos rfl]
    · rw [h j (by omega) l hl hp,formula j l (by omega) hl,if_neg (by omega),if_neg (by omega)]
  · rintro ⟨diag,adj,far⟩ j hj l hl hp
    have ordered (u v : ℕ) (huv : u ≤ v) (hv : v<d.length) (hgap : 0<rankGap d u*rankGap d v) :
        crossings r u v = crossings (zigzagRanks d.length) u v := by
      rw [formula u v huv hv]
      split
      · rename_i H; subst v; exact diag u hv (Nat.pos_of_mul_pos_left hgap)
      · split
        · rename_i H; subst v; exact adj u hv hgap
        · exact far u v (by omega) hv hgap
    rcases le_total j l with H|H
    · exact ordered j l H hl hp
    · rw [crossings_symm r j l,crossings_symm _ j l]
      exact ordered l j H hj (Nat.mul_comm .. ▸ hp)

def minSigmaValue (d : List ℕ) : ℤ := sigmaBase d + rankEnergy d (zigzagRanks d.length)

theorem sigma_minimum (d : List ℕ) (hd : Admissible d) (hs : d.Pairwise (· ≤ ·)) :
    let z := rankOrder d (zigzagRanks d.length)
    (∃ (n : ℕ) (G : Graph n), Realizes G z ∧ edgeIndex G 2 = minSigmaValue d) ∧
      IsLeast (values (fun G => edgeIndex G 2) d) (minSigmaValue d) := by
  intro z
  have hz := zigzag_perm d.length
  have hp := rank_order_perm (d:=d) hz
  obtain ⟨n,G,hG⟩ := perm_realization hp hd
  have eq := sigma_rank_score hd hz G hG
  refine ⟨⟨n,G,hG,eq⟩,⟨n,G,z,hp,hG,eq⟩,?_⟩
  rintro y ⟨_,F,x,hx,hF,rfl⟩
  obtain ⟨r,hr,rfl⟩ := label_permutation hx
  change minSigmaValue d ≤ edgeIndex F 2
  rw [sigma_rank_score hd hr F hF]
  exact add_le_add_left (energy_comparison hd.1 hs hr).1 _

theorem optimal_iff_cuts {d r : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·))
    (hr : r.Perm (List.range' 1 d.length)) {n : ℕ} (G : Graph n) (hG : Realizes G (rankOrder d r)) :
    IsLeast (values (fun G => edgeIndex G 2) d) (edgeIndex G 2) ↔ cutCriterion d r := by
  rw [← energy_criterion hd.1 hs hr]
  have hm := (sigma_minimum d hd hs).2
  have eq := sigma_rank_score hd hr G hG
  constructor
  · intro h
    have e := hm.unique h
    unfold minSigmaValue at e
    rw [eq] at e
    omega
  · intro h
    have e : minSigmaValue d=edgeIndex G 2 := by rw [eq,minSigmaValue,h]
    rwa [← e]

/-- Theorem 3.1.2. The term with rank zero contributes the second endpoint square. -/
theorem sigma_minimum_formula (d : List ℕ) (hd : Admissible d) (hs : d.Pairwise (· ≤ ·))
    (n : ℕ) (hn : d.length=n+2) :
    let v (i : ℕ) : ℤ := rankValue d i
    let m := sigmaBase d + ((v 1)^2 + (v (n+1)-v (n+2))^2 +
      ((List.range (n+1)).map (fun i => (v i-v (i+2))^2)).sum)
    (∃ (k : ℕ) (G : Graph k), Realizes G (rankOrder d (zigzagRanks d.length)) ∧ edgeIndex G 2=m) ∧
      IsLeast (values (fun G => edgeIndex G 2) d) m := by
  intro v m
  have eq : minSigmaValue d=m := by
    unfold minSigmaValue rankEnergy
    rw [hn,zigzag_route _ (fun a b => by unfold squareDiff; ring)]
    simp [m,v,squareDiff]
  rw [← eq]
  exact sigma_minimum d hd hs

/-- Theorem 3.3.4. Dropping the nonnegative interior terms from the exact minimum
leaves the two smallest shifted degrees and the gap between the two largest ones. -/
theorem sigma_endpoint_lower {d x : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·))
    (hx : x.Perm d) {k : ℕ} (G : Graph k) (hG : Realizes G x) (n : ℕ)
    (hn : d.length=n+2) :
    sigmaBase d + (rankValue d 1)^2 + (rankValue d 2)^2 +
      (rankValue d (n+1)-rankValue d (n+2))^2 ≤ edgeIndex G 2 := by
  let v (i : ℕ) : ℤ := rankValue d i
  let tail := ((List.range (n+1)).map (fun i => (v i-v (i+2))^2)).sum
  let m := sigmaBase d + ((v 1)^2 + (v (n+1)-v (n+2))^2 + tail)
  have least := (sigma_minimum_formula d hd hs n hn).2
  have hm : m ≤ edgeIndex G 2 := least.2 ⟨k,G,x,hx,hG,rfl⟩
  have zero_mem : 0 ∈ List.range (n+1) := by simp
  have term_mem : (v 0-v 2)^2 ∈ (List.range (n+1)).map (fun i => (v i-v (i+2))^2) :=
    List.mem_map.mpr ⟨0,zero_mem,rfl⟩
  have htail : (v 2)^2 ≤ tail := by
    have h := List.single_le_sum (fun z hz => by
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact sq_nonneg _) _ term_mem
    simpa [tail,v] using h
  dsimp [m] at hm
  change sigmaBase d + (v 1)^2 + (v 2)^2 + (v (n+1)-v (n+2))^2 ≤ edgeIndex G 2
  linarith

/-- The same lower bound in the degree notation of Theorem 3.3.4. -/
theorem sigma_degree_lower {d x : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·))
    (hx : x.Perm d) {k : ℕ} (G : Graph k) (hG : Realizes G x) (n : ℕ)
    (hn : d.length=n+2) :
    sigmaBase d + ((d[0]!:ℤ)-1)^2 + ((d[1]!:ℤ)-1)^2 +
      ((d[n+1]!:ℤ)-d[n]!)^2 ≤ edgeIndex G 2 := by
  have h := sigma_endpoint_lower hd hs hx G hG n hn
  rw [rankValue_succ_int hd (i:=1) (by omega) (by omega),
    rankValue_succ_int hd (i:=2) (by omega) (by omega),
    rankValue_succ_int hd (i:=n+1) (by omega) (by omega),
    rankValue_succ_int hd (i:=n+2) (by omega) (by omega)] at h
  norm_num at h
  simp only [List.getElem!_eq_getElem?_getD]
  change sigmaBase d + (((d[0]?.getD 0:ℕ):ℤ)-1)^2 +
    (((d[1]?.getD 0:ℕ):ℤ)-1)^2 +
    (((d[n+1]?.getD 0:ℕ):ℤ)-(d[n]?.getD 0:ℕ))^2 ≤ edgeIndex G 2
  nlinarith

/-- Proposition 3.3.5 compares any two realizations with the prescribed orders. -/
theorem zigzag_score_le {d x : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·)) (hx : x.Perm d)
    {n m : ℕ} (G : Graph n) (F : Graph m) (hG : Realizes G (rankOrder d (zigzagRanks d.length)))
    (hF : Realizes F x) : edgeIndex G 2 ≤ edgeIndex F 2 := by
  have h := (sigma_minimum d hd hs).2.2 (show edgeIndex F 2 ∈ values (fun T => edgeIndex T 2) d from
    ⟨m,F,x,hx,hF,rfl⟩)
  rw [sigma_rank_score hd (zigzag_perm _) G hG]
  exact h

end Thesis.Trees
