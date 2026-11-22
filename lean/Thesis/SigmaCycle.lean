import Thesis.SpineIndex
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.Perm.Basic

namespace Thesis.Trees

/-- Accumulate edge weights along a list with specified start and finish. -/
def route {V A : Type*} [Add A] (W : V → V → A) (a : V) : List V → V → A
  | [],b => W a b
  | v::s,b => W a v + route W v s b

theorem route_split {V A : Type*} [AddSemigroup A] (W : V → V → A) (a : V)
    (l : List V) (v : V) (r : List V) (b : V) :
    route W a (l++v::r) b = route W a l v + route W v r b := by
  induction l generalizing a with
  | nil => rfl
  | cons u l ih => simp [route,ih,add_assoc]

theorem route_reverse {V A : Type*} [AddCommSemigroup A] (W : V → V → A)
    (hs : ∀ u v, W u v=W v u) (a : V) (s : List V) (b : V) :
    route W a s.reverse b = route W b s a := by
  induction s generalizing a b with
  | nil => exact hs a b
  | cons u s ih =>
    rw [List.reverse_cons,route_split,route,route,ih,hs u b,add_comm]

theorem route_map {V X A : Type*} [Add A] (W : X → X → A) (f : V → X) (a : V) (s : List V) (b : V) :
    route W (f a) (s.map f) (f b) = route (fun u v => W (f u) (f v)) a s b := by
  induction s generalizing a with
  | nil => rfl
  | cons u s ih => simp [route,ih]

def sigmaBase (x : List ℕ) : ℤ :=
  (x.map (fun (a:ℕ) => ((a:ℤ)-2)*((a:ℤ)-1)^2)).sum

def squareDiff (a b : ℤ) := (a-b)^2

private theorem route_pairs (a : ℤ) (s : List ℤ) (b : ℤ) :
    route squareDiff a s b =
    (((a::s).zipWith squareDiff s).sum + squareDiff (a::s).getLast! b) := by
  induction s generalizing a with
  | nil => simp [route]
  | cons v s ih =>
    rw [route,ih]
    simp only [List.zipWith_cons_cons,List.sum_cons,show (a::v::s).getLast! = (v::s).getLast! by rfl]
    omega

/-- Lemma 3.1.2. Shift each spine degree by one and close the walk at zero. -/
theorem sigma_cycle {n : ℕ} (G : Graph n) (x : List ℕ) (hx : Admissible x) (hG : Realizes G x) :
    edgeIndex G 2 = sigmaBase x + route squareDiff 0 (x.map (fun (a:ℕ) => (a:ℤ)-1)) 0 := by
  have conv (l : List ℕ) : (l >>= fun d => pure (d:ℤ)) = l.map (fun d : ℕ => (d:ℤ)) := by
    exact bind_pure_comp (fun d : ℕ => (d:ℤ)) l
  rw [spine_index G x hx hG 2 (by decide),spineTerms]
  simp only [conv,List.map_map,List.zipWith_map,Function.comp_def,sigmaBase]
  cases x with
  | nil => have := hx.1; simp at this
  | cons a s =>
    simp only [List.map_cons,route,List.head!_cons,List.tail_cons]
    rw [route_pairs]
    have eq : ((a::s).zipWith (fun (u v:ℕ) => |(v:ℤ)-u|^2) s) =
        (((a::s).map (fun (u:ℕ) => (u:ℤ)-1)).zipWith squareDiff (s.map (fun (u:ℕ) => (u:ℤ)-1))) := by
      rw [List.zipWith_map]
      congr 1
      funext u v
      rw [sq_abs]; unfold squareDiff; ring
    rw [eq]
    have last : (((a::s).map (fun (u:ℕ) => (u:ℤ)-1)).getLast!) = ((a::s).getLast!:ℤ)-1 := by
      simp only [List.getLast!_eq_getLast?_getD,List.getLast?_map,
        List.getLast?_eq_getLast (l:=a::s) (by simp),Option.map_some,Option.getD_some]
      rfl
    change _ = _ + (squareDiff 0 ((a:ℤ)-1) + (_ + squareDiff (((a::s).map (fun (u:ℕ) => (u:ℤ)-1)).getLast!) 0))
    rw [last]
    simp only [List.map_cons]
    unfold squareDiff
    ring

theorem rank_order_identity (d : List ℕ) : rankOrder d (List.range' 1 d.length)=d := by
  unfold rankOrder
  apply List.ext_getElem
  · simp
  · intro i _ hi
    simp [List.getElem?_eq_getElem hi]

theorem rank_order_perm {d r : List ℕ} (hr : r.Perm (List.range' 1 d.length)) : (rankOrder d r).Perm d := by
  have h : (rankOrder d r).Perm (rankOrder d (List.range' 1 d.length)) := hr.map _
  rwa [rank_order_identity] at h

theorem label_permutation {d x : List ℕ} (hx : x.Perm d) :
    ∃ r, r.Perm (List.range' 1 d.length) ∧ rankOrder d r=x := by
  let f (i : ℕ) := d[i-1]!
  have heq : (List.range' 1 d.length).map f=d := rank_order_identity d
  have h : x.Perm ((List.range' 1 d.length).map f) := by rw [heq]; exact hx
  have hrel := congrFun (congrFun (List.eq_map_comp_perm f) x) (List.range' 1 d.length)
  obtain ⟨l,he,hp⟩ := hrel.mpr h
  exact ⟨l,hp,he.symm⟩

end Thesis.Trees
