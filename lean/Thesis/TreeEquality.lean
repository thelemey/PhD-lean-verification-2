import Thesis.RootedTree
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Thesis.Trees

open SimpleGraph SimpleGraph.Walk Finset
open scoped Classical

private theorem path_upward {V : Type*} {G : SimpleGraph V} (ht : G.IsTree) (d : V → ℕ)
    {v root : V} (p : G.Walk v root) (hp : p.IsPath)
    (h : ∀ u, u ≠ root → d u ≤ d (parent ht root u)) :
    (p.support.map d).Chain' (· ≤ ·) := by
  induction p with
  | nil => simp
  | @cons u v root huv p ih =>
    have hu : u ≠ root := by
      rintro rfl
      have e := (ht.existsUnique_path u u).unique hp IsPath.nil
      cases e
    have he : parent ht root u=v := by rw [parent,rootPath_eq ht root (.cons huv p) hp,snd_cons]
    have head := h u hu
    rw [he] at head
    obtain ⟨hpath,_⟩ := (cons_isPath_iff _ _).mp hp
    have H := ih hpath h
    simp only [Walk.support_cons,List.map_cons]
    rw [p.support_eq_cons] at H ⊢
    exact List.chain'_cons.mpr ⟨head,H⟩

/-- Local degree monotonicity toward the root is equivalent to the all-simple-paths
condition in the lower equality clause of proposition 2.1.2. -/
theorem monotone_root_paths {V : Type*} {G : SimpleGraph V} (ht : G.IsTree) (d : V → ℕ) (root : V) :
    (∀ u, u ≠ root → d u ≤ d (parent ht root u)) ↔
    ∀ v (p : G.Walk root v), p.IsPath → (p.support.map d).Pairwise (· ≥ ·) := by
  have reverse_pair {u v} (p : G.Walk u v) :
      (p.reverse.support.map d).Pairwise (· ≥ ·) ↔ (p.support.map d).Pairwise (· ≤ ·) := by
    rw [Walk.support_reverse, List.map_reverse, List.pairwise_reverse]
  constructor
  · intro h v p hp
    have H := (List.chain'_iff_pairwise.mp (path_upward ht d p.reverse hp.reverse h))
    simpa using (reverse_pair p.reverse).mpr H
  · intro h u hu
    let p := rootPath ht root u
    have H := (reverse_pair p).mp (h u p.reverse (rootPath_isPath ht root u).reverse)
    have hnil : ¬p.Nil := not_nil_of_ne hu
    rw [← p.cons_support_tail hnil, List.map_cons, List.pairwise_cons] at H
    exact H.1 _ (List.mem_map.mpr ⟨_,p.tail.start_mem_support,rfl⟩)

private theorem unique_neighbor {n : ℕ} (G : Graph n) {u v w : Fin n} (hd : degree G u=1)
    (hv : G.Adj u v) (hw : G.Adj u w) : v=w := by
  classical
  have hd' : (G.neighborFinset u).card=1 := hd
  obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hd'
  have vmem := (G.mem_neighborFinset u v).mpr hv
  have wmem := (G.mem_neighborFinset u w).mpr hw
  rw [hk,Finset.mem_singleton] at vmem wmem
  exact vmem.trans wmem.symm

private theorem all_reached {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    (h : ∀ u v, P u → G.Adj u v → P v) {u v : V} (p : G.Walk u v) (hu : P u) : P v := by
  induction p with
  | nil => exact hu
  | cons ha _ ih => exact ih (h _ _ hu ha)

/-- A tree of order at least three is a star exactly when every edge has a leaf endpoint. -/
theorem leaf_edges_iff_star {n : ℕ} (hn : 3 ≤ n) (G : Graph n) (ht : G.IsTree) :
    (∀ u v, G.Adj u v → degree G u=1 ∨ degree G v=1) ↔ Star G := by
  classical
  constructor
  · intro h
    obtain ⟨c,hc⟩ : ∃ c, 2 ≤ degree G c := by
      by_contra! H
      have hle : (∑ v, (degree G v:ℤ)) ≤ ∑ _ : Fin n, (1:ℤ) := Finset.sum_le_sum (fun v _ =>
        by exact_mod_cast Nat.le_of_lt_succ (H v))
      rw [tree_degree_sum G ht ⟨0,by omega⟩] at hle
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hle
      omega
    have P (v : Fin n) : v=c ∨ G.Adj c v := by
      apply all_reached (P:=fun w => w=c ∨ G.Adj c w) (p := (ht.existsUnique_path c v).choose) _ (Or.inl rfl)
      intro u z hu huz
      rcases hu with rfl | hcu
      · exact Or.inr huz
      · have hdu : degree G u=1 := (h c u hcu).resolve_left (by omega)
        exact Or.inl (unique_neighbor G hdu huz hcu.symm)
    refine ⟨c,fun u v => ⟨fun huv => ⟨huv.ne,?_⟩,?_⟩⟩
    · rcases P u with H|H
      · exact Or.inl H
      · have hdu := (h c u H).resolve_left (by omega)
        exact Or.inr (unique_neighbor G hdu huv H.symm)
    · rintro ⟨hne,rfl|rfl⟩
      · exact (P v).resolve_left hne.symm
      · exact ((P u).resolve_left hne).symm
  · rintro ⟨c,hc⟩
    have leaf (v : Fin n) (hv : v ≠ c) : degree G v=1 := by
      have E : G.neighborFinset v={c} := by
        ext z
        simp [hc,hv]
        exact fun hz => hz ▸ hv
      change (G.neighborFinset v).card=1
      simp [E]
    intro u v huv
    by_cases hu : u=c
    · exact Or.inr (leaf v (hu ▸ huv.ne.symm))
    · exact Or.inl (leaf u hu)

end Thesis.Trees
