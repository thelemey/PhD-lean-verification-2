import Thesis.SpinePath
import Mathlib.Tactic.Linarith

namespace Thesis.Trees

open Finset
open scoped Classical

private theorem sum_list {V : Type*} [DecidableEq V] (f : V → ℤ) (s : List V) (hn : s.Nodup) :
    (∑ u ∈ s.toFinset, f u) = (s.map f).sum := by
  induction s with
  | nil => simp
  | cons u s ih => simp [List.toFinset_cons, (List.nodup_cons.mp hn).1, ih hn.tail]

/-- Taking the two orientations of each edge doubles the index defined by u < v. -/
theorem twice_edgeIndex {n : ℕ} (G : Graph n) (r : ℕ) :
    2*edgeIndex G r = ∑ u, ∑ v, (if G.Adj u v then |(degree G u : ℤ)-degree G v|^r else 0) := by
  classical
  let A (u v : Fin n) := if u < v ∧ G.Adj u v then |(degree G u : ℤ)-degree G v|^r else 0
  have h (u v : Fin n) : (if G.Adj u v then |(degree G u : ℤ)-degree G v|^r else 0) = A u v + A v u := by
    rcases lt_trichotomy u v with h|rfl|h
    · simp [A,h,h.asymm]
    · simp [A]
    · simp [A,h,h.asymm,G.adj_comm v u, abs_sub_comm (degree G v : ℤ) (degree G u)]
  simp_rw [h, Finset.sum_add_distrib]
  change 2*(∑ u, ∑ v, A u v) = (∑ u, ∑ v, A u v) + ∑ u, ∑ v, A v u
  rw [Finset.sum_comm (f:=fun u v => A v u)]
  ring

private def leafWeight (d r : ℕ) : ℤ := ((d:ℤ)-1)^r

private def correction (r u v : ℕ) : ℤ :=
  |(u:ℤ)-v|^r - leafWeight u r - leafWeight v r

private theorem along_map {V X : Type*} (W : V → V → ℤ) (B : X → X → ℤ) (f : V → X)
    (s : List V) (he : s.Chain' (fun u v => W u v = B (f u) (f v))) :
    along W s = along B (s.map f) := by
  induction s with
  | nil => rfl
  | cons u s ih =>
    cases s with
    | nil => rfl
    | cons v l =>
      rw [along, List.map_cons, List.map_cons, along, (List.chain'_cons.mp he).1, ih (List.chain'_cons.mp he).2]
      rfl

private theorem along_corrected (r : ℕ) (u : ℕ) (s : List ℕ) :
    along (correction r) (u::s) =
      (((u::s).zipWith (fun (a b : ℕ) => |(b:ℤ)-a|^r) s).sum -
      2*((u::s).map (fun (d : ℕ) => leafWeight d r)).sum + leafWeight u r + leafWeight ((u::s).getLast!) r) := by
  induction s generalizing u with
  | nil => simp [along]; ring
  | cons v l ih =>
    simp only [along, List.zipWith_cons_cons, List.sum_cons, List.map_cons, correction,
      show (u::v::l).getLast! = (v::l).getLast! by rfl] at ih ⊢
    rw [ih v, abs_sub_comm (u:ℤ) v]
    ring

private theorem spine_arithmetic (r : ℕ) (x : List ℕ) (hx : x ≠ []) :
    (x.map (fun (d : ℕ) => (d:ℤ) * leafWeight d r)).sum + along (correction r) x = spineTerms x r := by
  have split (l : List ℕ) :
      (l.map (fun (d : ℕ) => (d:ℤ)*leafWeight d r)).sum -
        2*(l.map (fun (d : ℕ) => leafWeight d r)).sum =
        (l.map (fun (d : ℕ) => ((d:ℤ)-2)*leafWeight d r)).sum := by
    induction l with
    | nil => simp
    | cons d l ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith
  cases x with
  | nil => exact False.elim (hx rfl)
  | cons u s =>
    rw [along_corrected]
    unfold spineTerms
    have conv (l : List ℕ) : (l >>= fun d => pure (d:ℤ)) = l.map (fun d : ℕ => (d:ℤ)) :=
      bind_pure_comp (fun d : ℕ => (d:ℤ)) l
    simp only [conv, List.map_map, List.zipWith_map, Function.comp_def, List.tail_cons]
    change _ = ((u::s).map (fun (d : ℕ) => ((d:ℤ)-2)*leafWeight d r)).sum + leafWeight u r +
      leafWeight ((u::s).getLast!) r + _
    linarith [split (u::s)]

theorem sum_incidence {n : ℕ} (G : Graph n) (f : Fin n → ℤ) (u : Fin n) :
    (∑ v, if G.Adj u v then f u else 0) = (degree G u : ℤ)*f u := by
  classical
  rw [← Finset.sum_filter, ← G.neighborFinset_eq_filter]
  simp [degree]

/-- The decomposition holds for every positive exponent. -/
theorem spine_index {n : ℕ} (G : Graph n) (x : List ℕ) (hx : Admissible x)
    (hG : Realizes G x) (r : ℕ) (hr : 0 < r) : edgeIndex G r = spineTerms x r := by
  classical
  obtain ⟨ht,s,hn,hmap,hmem,hsteps⟩ := hG
  have chain : s.Chain' G.Adj := List.chain'_iff_get.mpr (fun i hi => hsteps i (by omega))
  let D := degree G
  let T := s.toFinset
  let F (u v : Fin n) : ℤ := if G.Adj u v then leafWeight (D u) r else 0
  let W (u v : Fin n) : ℤ := if G.Adj u v then correction r (D u) (D v) else 0
  have sym (u v : Fin n) : W u v = W v u := by
    by_cases ha : G.Adj u v
    · simp only [W,ha,ha.symm,if_true,correction]
      rw [abs_sub_comm]; ring
    · simp [W,ha,show ¬G.Adj v u from fun h => ha h.symm]
  have off (u v : Fin n) (ha : ¬G.Adj u v) : W u v=0 := by simp [W,ha]
  have positive_of_adj {u v : Fin n} (ha : G.Adj u v) : 0 < D u :=
    (G.degree_pos_iff_exists_adj u).mpr ⟨v,ha⟩
  have outside (u v : Fin n) (hu : u ∉ T) : W u v=0 := by
    by_cases ha : G.Adj u v
    · have hm : u ∉ s := by simpa [T] using hu
      have hlt : ¬ 2 ≤ D u := fun h => hm ((hmem u).mpr h)
      have hdu : D u=1 := by have := positive_of_adj ha; omega
      have hdv : (1:ℤ) ≤ D v := by exact_mod_cast positive_of_adj ha.symm
      simp [W,ha,correction,hdu,leafWeight,zero_pow hr.ne',abs_sub_comm (1:ℤ) (D v),
        abs_of_nonneg (sub_nonneg.mpr hdv)]
    · exact off u v ha
  have point (u v : Fin n) :
      (if G.Adj u v then |(D u:ℤ)-D v|^r else 0) = F u v + F v u + W u v := by
    by_cases ha : G.Adj u v
    · simp [F,W,ha,ha.symm,correction]
    · simp [F,W,ha,show ¬G.Adj v u from fun h => ha h.symm]
  have wsum : (∑ u, ∑ v, W u v) = 2*along (correction r) x := by
    calc
      _ = ∑ u ∈ T, ∑ v, W u v := (Finset.sum_subset T.subset_univ (fun u _ hu =>
        Finset.sum_eq_zero (fun v _ => outside u v hu))).symm
      _ = ∑ u ∈ T, ∑ v ∈ T, W u v := Finset.sum_congr rfl (fun u _ =>
        (Finset.sum_subset T.subset_univ (fun v _ hv => (sym u v).trans (outside v u hv))).symm)
      _ = 2*along W s := sum_spine ht W sym off s chain hn
      _ = _ := by
        rw [along_map W (correction r) D s (chain.imp (fun u v ha => by simp [W,ha])), hmap]
  have fsum : (∑ u, ∑ v, F u v) = (x.map (fun (d:ℕ) => (d:ℤ)*leafWeight d r)).sum := by
    simp only [F, sum_incidence G (fun u => leafWeight (D u) r)]
    change (∑ u, (D u:ℤ)*leafWeight (D u) r) = _
    calc
      _ = ∑ u ∈ T, (D u:ℤ)*leafWeight (D u) r := by
        symm
        apply Finset.sum_subset T.subset_univ
        intro u _ hu
        have hm : u ∉ s := by simpa [T] using hu
        have hlt : ¬ 2 ≤ D u := fun h => hm ((hmem u).mpr h)
        rcases (show D u=0 ∨ D u=1 by omega) with h|h <;> simp [h, leafWeight,zero_pow hr.ne']
      _ = _ := by rw [sum_list _ s hn, ← hmap]; simp [D,List.map_map, Function.comp_def]
  have he := twice_edgeIndex G r
  change 2 * edgeIndex G r = ∑ u, ∑ v, (if G.Adj u v then |(D u:ℤ)-D v|^r else 0) at he
  simp_rw [point, Finset.sum_add_distrib] at he
  rw [Finset.sum_comm (f:=fun u v => F v u), fsum, wsum] at he
  have hx' : x ≠ [] := by intro h; have := hx.1; simp [h] at this
  linarith [spine_arithmetic r x hx']

/-- The endpoint form used in (2.6) and (3.1). The middle list may be empty. -/
theorem index_endpoints {n : ℕ} (G : Graph n) (u v : ℕ) (m : List ℕ) (r : ℕ) (hr : 0 < r)
    (hx : Admissible (u::(m++[v]))) (hG : Realizes G (u::(m++[v]))) :
    edgeIndex G r = ((u:ℤ)-1)^(r+1) + ((v:ℤ)-1)^(r+1) +
      (m.map (fun (d:ℕ) => ((d:ℤ)-2)*((d:ℤ)-1)^r)).sum +
      ((u::(m++[v])).zipWith (fun (a b:ℕ) => |(b:ℤ)-a|^r) (m++[v])).sum := by
  rw [spine_index G _ hx hG r hr, spineTerms]
  have conv (l : List ℕ) : (l >>= fun d => pure (d:ℤ)) = l.map (fun d : ℕ => (d:ℤ)) :=
    bind_pure_comp (fun d : ℕ => (d:ℤ)) l
  simp only [conv, List.map_map, List.zipWith_map, Function.comp_def, List.tail_cons]
  simp only [List.map_cons, List.map_append, List.map_nil, List.sum_cons, List.sum_append, List.sum_nil,
    add_zero, List.head!_cons, List.getLast!_eq_getLast?_getD, pow_succ]
  have last : (u::(m++[v])).getLast? = some v := List.getLast?_concat (l:=u::m)
  rw [last]
  simp only [Option.getD_some]
  ring

/-- Section 1.3(1), simultaneously for the Albertson and sigma indices. -/
theorem claim1 : Claim1 := by
  intro n G x hx hG r hr
  apply spine_index G x hx hG r
  simp at hr
  omega

end Thesis.Trees
