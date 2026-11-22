import Thesis.RootedTree
import Thesis.TreeDistanceLiterature
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Thesis.Trees

open Finset SimpleGraph
open scoped Classical

private noncomputable def rootDepth {n : ℕ} (G : Graph n) (ht : G.IsTree)
    (root v : Fin n) : ℤ := (rootPath ht root v).length

private theorem rootDepth_root {n : ℕ} (G : Graph n) (ht : G.IsTree) (root : Fin n) :
    rootDepth G ht root root=0 := by
  rw [rootDepth,rootPath_eq ht root .nil Walk.IsPath.nil]
  rfl

private theorem rootDepth_parent {n : ℕ} (G : Graph n) (ht : G.IsTree) (root : Fin n)
    {v : Fin n} (hv : v≠root) : rootDepth G ht root (parent ht root v)=rootDepth G ht root v-1 := by
  have h := parent_depth ht root hv
  have h' := congrArg (fun z : ℕ => (z:ℤ)) h
  unfold rootDepth
  norm_num at h'
  omega

private theorem rootDepth_eq_dist {n : ℕ} (G : Graph n) (ht : G.IsTree) (root v : Fin n) :
    rootDepth G ht root v=G.dist root v := by
  obtain ⟨p,hp,hlen⟩ := ht.isConnected.exists_path_of_dist v root
  rw [rootDepth,rootPath_eq ht root p hp,hlen,G.dist_comm]

/-- The degree-weighted transmission from a root in a tree. -/
theorem rooted_degree_distance {n : ℕ} (G : Graph n) (ht : G.IsTree) (root : Fin n) :
    (∑ v, (degree G v:ℤ)*G.dist root v) = 2*(∑ v,(G.dist root v:ℤ))-((n:ℤ)-1) := by
  let h (v : Fin n) := rootDepth G ht root v
  let p (v : Fin n) := parent ht root v
  let q (v : Fin n) := h v+h (p v)
  have edge := rooted_edge_sum ht root (fun u v => h u+h v) (fun u v => by simp [add_comm])
  have lhs : (∑ u,∑ v, if G.Adj u v then h u+h v else 0) =
      2*(∑ u,(degree G u:ℤ)*h u) := by
    have first : (∑ u,∑ v,if G.Adj u v then h u else 0) =
        ∑ u,(degree G u:ℤ)*h u := by
      exact sum_congr rfl (fun u _ => sum_incidence G h u)
    have second : (∑ u,∑ v,if G.Adj u v then h v else 0) =
        ∑ u,(degree G u:ℤ)*h u := by
      rw [sum_comm]
      exact sum_congr rfl (fun u _ => by
        simpa only [G.adj_comm] using sum_incidence G h u)
    rw [show (∑ u,∑ v,if G.Adj u v then h u+h v else 0) =
        (∑ u,∑ v,if G.Adj u v then h u else 0) +
          (∑ u,∑ v,if G.Adj u v then h v else 0) by
      simp_rw [← sum_add_distrib]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      by_cases a : G.Adj u v <;> simp [a],first,second]
    ring
  have rhs : (∑ v ∈ univ.erase root,q v) =
      2*(∑ v : Fin n,h v)-((n:ℤ)-1) := by
    rw [show (∑ v ∈ univ.erase root,q v) =
        ∑ v ∈ univ.erase root,(2*h v-1) by
      apply sum_congr rfl
      intro v hv
      dsimp [q,h,p]
      rw [rootDepth_parent G ht root (Finset.mem_erase.mp hv).1]
      ring]
    rw [sum_sub_distrib]
    have erase : (∑ v ∈ univ.erase root,h v)=∑ v : Fin n,h v := by
      rw [← univ.sum_erase_add _ (mem_univ root),show h root=0 by
        exact rootDepth_root G ht root,add_zero]
    have sum2 : (∑ v ∈ univ.erase root,2*h v)=2*(∑ v : Fin n,h v) := by
      rw [← mul_sum,erase]
    rw [sum2]
    simp only [sum_const,card_erase_of_mem (mem_univ root),card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one]
    have hn0 : n≠0 := by
      intro e
      subst n
      exact Fin.elim0 root
    have cast_sub : ((n-1:ℕ):ℤ)=(n:ℤ)-1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0)]
      norm_num
    rw [cast_sub]
  rw [lhs,rhs] at edge
  have core : (∑ u,(degree G u:ℤ)*h u)=2*(∑ u,h u)-((n:ℤ)-1) := by linarith
  simpa only [h,rootDepth_eq_dist] using core

private theorem twice_lt_sum {n : ℕ} (f : Fin n→Fin n→ℤ) (hs : ∀ u v,f u v=f v u)
    (hd : ∀ u,f u u=0) :
    2*(∑ u,∑ v,if u<v then f u v else 0)=∑ u,∑ v,f u v := by
  let A (u v : Fin n) := if u<v then f u v else 0
  have point (u v : Fin n) : f u v=A u v+A v u := by
    rcases lt_trichotomy u v with h|h|h
    · simp [A,h,h.asymm]
    · subst v; simp [A,hd]
    · simp [A,h,h.asymm,hs]
  change 2*(∑ u,∑ v,A u v)=_
  calc
    2*(∑ u,∑ v,A u v) = (∑ u,∑ v,A u v)+(∑ u,∑ v,A v u) := by
      rw [sum_comm (f:=fun u v => A v u)]; ring
    _ = ∑ u,∑ v,f u v := by
      simp_rw [point,sum_add_distrib]

/-- The tree identity behind Lemma 4.0.1, proved internally from unique paths
and the orientation of every edge toward an arbitrary root. -/
theorem tree_gutman_wiener_proved {n : ℕ} (G : Graph n) (ht : G.IsTree) :
    gutman G = 4*wiener G-((n:ℤ)-1)*(2*n-1) := by
  by_cases hn : n=0
  · subst n
    have ne : Nonempty (Fin 0) := (SimpleGraph.isTree_iff_existsUnique_path.mp ht).1
    exact Fin.elim0 ne.some
  have root : Fin n := ⟨0,Nat.pos_of_ne_zero hn⟩
  let S : ℤ := ∑ u,∑ v,(G.dist u v:ℤ)
  let A : ℤ := ∑ u,(degree G u:ℤ)*(∑ v,(G.dist u v:ℤ))
  let D : ℤ := ∑ u,∑ v,(degree G u:ℤ)*degree G v*G.dist u v
  have trans (u : Fin n) := rooted_degree_distance G ht u
  have aeq : A=2*S-(n:ℤ)*((n:ℤ)-1) := by
    dsimp [A,S]
    calc
      (∑ u,(degree G u:ℤ)*(∑ v,(G.dist u v:ℤ))) =
          ∑ v,∑ u,(degree G u:ℤ)*G.dist v u := by
            rw [sum_comm]
            apply sum_congr rfl
            intro v _
            simp_rw [G.dist_comm]
            rw [mul_sum]
      _ = ∑ v,(2*(∑ u,(G.dist v u:ℤ))-((n:ℤ)-1)) :=
        sum_congr rfl (fun v _ => trans v)
      _ = _ := by
        rw [sum_sub_distrib,← mul_sum]
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have deq : D=2*A-((n:ℤ)-1)*(2*((n:ℤ)-1)) := by
    dsimp [D,A]
    calc
      (∑ u,∑ v,(degree G u:ℤ)*degree G v*G.dist u v) =
          ∑ u,(degree G u:ℤ)*(∑ v,(degree G v:ℤ)*G.dist u v) := by
            apply sum_congr rfl
            intro u _
            rw [mul_sum]
            apply sum_congr rfl
            intro v _
            ring
      _ = ∑ u,(degree G u:ℤ)*(2*(∑ v,(G.dist u v:ℤ))-((n:ℤ)-1)) :=
        sum_congr rfl (fun u _ => congrArg ((degree G u:ℤ)*·) (trans u))
      _ = 2*(∑ u,(degree G u:ℤ)*(∑ v,(G.dist u v:ℤ)))-
          ((n:ℤ)-1)*(∑ u,(degree G u:ℤ)) := by
            rw [show (∑ u,(degree G u:ℤ)*(2*(∑ v,(G.dist u v:ℤ))-((n:ℤ)-1))) =
                ∑ u,(2*(degree G u:ℤ)*(∑ v,(G.dist u v:ℤ))-
                  ((n:ℤ)-1)*(degree G u)) by
              apply sum_congr rfl
              intro u _
              ring,sum_sub_distrib]
            simp_rw [mul_assoc]
            rw [← mul_sum,← mul_sum]
      _ = _ := by rw [tree_degree_sum G ht root]
  have w : 2*wiener G=S := twice_lt_sum (fun (u v : Fin n) => (G.dist u v:ℤ))
    (fun u v => congrArg (fun z : ℕ => (z:ℤ))
      (show G.dist u v=G.dist v u from G.dist_comm)) (fun u => by simp)
  have g : 2*gutman G=D := twice_lt_sum
    (fun (u v : Fin n) => (degree G u:ℤ)*degree G v*G.dist u v)
    (fun (u v : Fin n) => by
      have e : (G.dist u v:ℤ)=G.dist v u := congrArg (fun z : ℕ => (z:ℤ))
        (show G.dist u v=G.dist v u from G.dist_comm)
      change (degree G u:ℤ)*degree G v*G.dist u v =
        (degree G v:ℤ)*degree G u*G.dist v u
      rw [e]
      ring) (fun u => by simp)
  rw [aeq] at deq
  nlinarith

end Thesis.Trees
