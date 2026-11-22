import Thesis.GutmanSpine
import Mathlib.Data.List.Perm.Basic

namespace Thesis.Trees

private theorem exchange_head {α : Type*} (x : List α) (i : ℕ) (hi : i < x.length) (b : α) :
    (x[i] :: x.set i b).Perm (b::x) := by
  exact ((List.set_perm_cons_eraseIdx hi b).cons x[i]).trans
    ((List.Perm.swap b x[i] _).trans ((List.getElem_cons_eraseIdx_perm hi).cons b))

theorem swap_perm (x : List ℕ) {u v : ℕ} (hu : u < v) (hv : v < x.length) : (swapAt x u v).Perm x := by
  have hu' : u < x.length := by omega
  have e := exchange_head x u hu' x[v]
  have e' := exchange_head (x.set u x[v]) v (by simpa using hv) x[u]
  rw [List.getElem_set_ne (by omega : u ≠ v)] at e'
  have p := e'.trans e
  simpa [swapAt,getElem!_pos x u hu',getElem!_pos x v hv] using p

private def prefixWeight (x : List ℕ) (j : ℕ) := ((spineWeights x).take j).sum

private theorem sum_set (l : List ℤ) (i : ℕ) (hi : i < l.length) (z : ℤ) :
    (l.set i z).sum = l.sum + z - l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons u l ih =>
    cases i with
    | zero => simp; omega
    | succ i =>
      have h : i<l.length := by simpa using hi
      simp [ih i h]; omega

private theorem prefix_set (x : List ℕ) (i b j : ℕ) (hi : i < x.length) :
    prefixWeight (x.set i b) j = prefixWeight x j + (if i<j then (b:ℤ)-x[i] else 0) := by
  unfold prefixWeight spineWeights
  rw [List.map_set,List.take_set]
  by_cases h : i < j
  · rw [if_pos h,sum_set _ i (by simp; omega)]
    simp; omega
  · rw [if_neg h,List.set_eq_of_length_le (by simp; omega),add_zero]

private theorem swap_prefix (x : List ℕ) {u v : ℕ} (hu : u < v) (hv : v < x.length) (i : ℕ) :
    prefixWeight (swapAt x u v) (i+1) = prefixWeight x (i+1) +
      (if u ≤ i ∧ i < v then (x[v]:ℤ) - x[u] else 0) := by
  have h₁ : u<x.length := by omega
  rw [swapAt,getElem!_pos x u h₁,getElem!_pos x v hv,prefix_set _ v _ _ (by simpa using hv),
      List.getElem_set_ne (ne_of_lt hu),prefix_set _ u _ _ h₁]
  split_ifs <;> omega

private theorem map_difference {α : Type*} (s : List α) (f g : α → ℤ) :
    (s.map f).sum - (s.map g).sum = (s.map (fun i => f i - g i)).sum := by
  induction s with
  | nil => simp
  | cons a s ih => simp only [List.map_cons,List.sum_cons]; omega

private theorem interval_sum (N u v : ℕ) (hu : u ≤ v) (hv : v ≤ N) (f : ℕ → ℤ) :
    ((List.range N).map (fun i => if u ≤ i ∧ i < v then f i else 0)).sum =
    ((List.range' u (v-u)).map f).sum := by
  let g (i : ℕ) := if u ≤ i ∧ i<v then f i else 0
  have split : List.range N = List.range' 0 u ++ List.range' u (v-u) ++ List.range' v (N-v) := by
    rw [List.range_eq_range']
    have e := List.range'_append_1 (s:=0) (m:=u) (n:=v-u)
    simp only [Nat.zero_add,Nat.add_sub_of_le hu] at e
    rw [e]
    simpa [Nat.add_sub_of_le hv] using (List.range'_append_1 (s:=0) (m:=v) (n:=N-v)).symm
  have hmem {t a i : ℕ} (hi : i ∈ List.range' a t) : a ≤ i ∧ i < a+t := by
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp; omega
  have zero (l : List ℕ) (h : ∀ i ∈ l, ¬(u ≤ i ∧ i<v)) : (l.map g).sum=0 := by
    have eq : l.map g = l.map (fun _ => (0:ℤ)) := List.map_congr_left (fun i hi => if_neg (h i hi))
    simp [eq]
  have left := zero (List.range' 0 u) (fun _ h => by have := hmem h; omega)
  have right := zero (List.range' v (N-v)) (fun _ h => by have := hmem h; omega)
  have mid : (List.range' u (v-u)).map g = (List.range' u (v-u)).map f :=
    List.map_congr_left (fun i h => if_pos (by have := hmem h; omega))
  change ((List.range N).map g).sum=_
  rw [split]
  simp [List.map_append,List.sum_append,left,right,mid]

private theorem cutProducts_prefix (x : List ℕ) :
    cutProducts (spineWeights x) =
      ((List.range (x.length-1)).map (fun i => prefixWeight x (i+1) *
        ((spineWeights x).sum-prefixWeight x (i+1)))).sum := by
  unfold cutProducts
  rw [show (spineWeights x).length = x.length by simp [spineWeights]]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  have h := congrArg List.sum (List.take_append_drop (i+1) (spineWeights x))
  rw [List.sum_append] at h
  unfold prefixWeight
  rw [show ((spineWeights x).drop (i+1)).sum = (spineWeights x).sum-((spineWeights x).take (i+1)).sum by omega]

/-- Lemma 4.2.1. Exactly the cuts after the zero-based positions u,…,v−1 change. -/
theorem swap_formula {n : ℕ} (G : Graph n) (x : List ℕ) (hx : Admissible x) (hG : Realizes G x)
    (u v : ℕ) (hu : u<v) (hv : v<x.length) (H : Graph n) (hH : Realizes H (swapAt x u v)) :
    gutman H - gutman G = swapDifference x u v := by
  let y := swapAt x u v
  let w := spineWeights x
  let δ : ℤ := (x[v]:ℤ)-x[u]
  let p := fun i => prefixWeight x (i+1)
  let q := fun i => prefixWeight y (i+1)
  let f := fun i => w.sum-2*p i-δ
  have hp : y.Perm x := swap_perm x hu hv
  have hy : Admissible y := ⟨hx.1.trans_eq hp.length_eq.symm,fun _ h => hx.2 _ (hp.mem_iff.mp h)⟩
  have sumEq : (spineWeights y).sum = w.sum := (hp.map _).sum_eq
  have pts (i : ℕ) : q i*(w.sum-q i)-p i*(w.sum-p i) =
      if u ≤ i ∧ i<v then δ*f i else 0 := by
    have e : q i=p i+(if u ≤ i ∧ i<v then δ else 0) := swap_prefix x hu hv i
    rw [e]
    by_cases hh : u ≤ i ∧ i < v
    · simp only [if_pos hh,f]; ring
    · simp [hh]
  have diff : cutProducts (spineWeights y) - cutProducts w =
      δ*((List.range' u (v-u)).map f).sum := by
    rw [cutProducts_prefix y,cutProducts_prefix x,hp.length_eq,sumEq,map_difference]
    change ((List.range (x.length-1)).map (fun i => q i*(w.sum-q i)-p i*(w.sum-p i))).sum = _
    simp_rw [pts]
    rw [interval_sum _ _ _ hu.le (by omega)]
    generalize List.range' u (v-u)=l
    induction l with
    | nil => simp
    | cons i l ih => simp [mul_add,ih]
  have val := gutman_spine H y hy hH
  rw [gutman_spine G x hx hG,val,gutmanScore,gutmanScore,sumEq]
  have hu' : u<x.length := by omega
  have changeScore : swapDifference x u v=4*δ*((List.range' u (v-u)).map f).sum := by
    have conv : (x >>= fun a => pure (a:ℤ)) = x.map (fun a : ℕ => (a:ℤ)) :=
      bind_pure_comp (fun a : ℕ => (a:ℤ)) x
    unfold swapDifference
    simp only [conv,List.map_map,Function.comp_def,getElem!_pos x u hu',getElem!_pos x v hv]
    congr 2
    apply List.map_congr_left
    intro i _
    change 2+w.sum-2*(1+p i)-δ=w.sum-2*p i-δ
    ring
  rw [changeScore]
  change 4*((2+w.sum-1)^2+cutProducts (spineWeights y)) - (2+w.sum-1)*(2*(2+w.sum)-1) -
    (4*((2+w.sum-1)^2+cutProducts w) - (2+w.sum-1)*(2*(2+w.sum)-1)) = _
  linarith

theorem global_implies_local {n : ℕ} (G : Graph n) (x : List ℕ)
    (hg : IsGreatest (values gutman x) (gutman G)) : LocallyMaximal G x := by
  intro u v hu hv H hH
  exact hg.2 ⟨n,H,swapAt x u v,swap_perm x hu hv,hH,rfl⟩

end Thesis.Trees
