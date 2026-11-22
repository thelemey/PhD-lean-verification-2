import Thesis.Trees
import Mathlib.Data.List.Chain
import Mathlib.Tactic.Ring

namespace Thesis.Trees

open Finset SimpleGraph

/-- Corollary 1.2.1, for a finite connected labelled graph. -/
theorem tree_edge_count {n : ℕ} (G : Graph n) (hc : G.Connected) :
    G.IsTree ↔ Nat.card G.edgeSet + 1 = n := by
  simp [SimpleGraph.isTree_iff_connected_and_card, hc]

private theorem path_inside {V : Type*} {G : SimpleGraph V} {u z : V} {l : List V}
    (hc : (u::l).Chain' G.Adj) (hn : (u::l).Nodup) (hz : z ∈ u::l) :
    ∃ p : G.Walk u z, p.IsPath ∧ ∀ y ∈ p.support, y ∈ u::l := by
  induction l generalizing u with
  | nil =>
    obtain rfl : z=u := by simpa using hz
    exact ⟨.nil, by simp, by simp⟩
  | cons v l ih =>
    rw [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨.nil, by simp, by simp⟩
    · obtain ⟨p, hp, hs⟩ := ih (List.chain'_cons.mp hc).2 hn.tail hz
      refine ⟨.cons (List.chain'_cons.mp hc).1 p, ?_, ?_⟩
      · apply Walk.IsPath.mk'
        simpa only [Walk.support_cons, List.nodup_cons] using
          And.intro (fun hu => (List.nodup_cons.mp hn).1 (hs u hu)) hp.support_nodup
      · intro y hy
        rw [Walk.support_cons, List.mem_cons] at hy
        exact hy.elim (fun e => e ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem _ (hs _ h))

/-- A simple path in a tree has no edge from its first vertex past its second vertex. -/
theorem spine_no_chord {V : Type*} {G : SimpleGraph V} (ht : G.IsTree) {u v z : V} {l : List V}
    (hc : (u::v::l).Chain' G.Adj) (hn : (u::v::l).Nodup) (hz : z ∈ l) : ¬G.Adj u z := by
  intro huz
  obtain ⟨p,hp,hs⟩ := path_inside (List.chain'_cons.mp hc).2 hn.tail (List.mem_cons_of_mem v hz)
  let q := Walk.cons (List.chain'_cons.mp hc).1 p
  have hq : q.IsPath := Walk.IsPath.mk' (List.nodup_cons.mpr
    ⟨fun hu => (List.nodup_cons.mp hn).1 (hs u hu), hp.support_nodup⟩)
  have heq := (ht.existsUnique_path u z).unique hq (Walk.IsPath.of_adj huz)
  have hl := congrArg Walk.length heq
  have hp₀ : p.length=0 := by simpa [q, Adj.toWalk] using hl
  exact (List.nodup_cons.mp hn.tail).1 (p.eq_of_length_eq_zero hp₀ ▸ hz)

/-- Sum of the weights of the consecutive pairs in the given order. -/
def along {V : Type*} (W : V → V → ℤ) : List V → ℤ
  | [] | [_] => 0
  | u::v::l => W u v + along W (v::l)

/-- The double sum over spine vertices counts precisely each consecutive pair twice. -/
theorem sum_spine {V : Type*} [DecidableEq V] {G : SimpleGraph V} (ht : G.IsTree)
    (W : V → V → ℤ) (hsymm : ∀ u v, W u v = W v u) (hoff : ∀ u v, ¬G.Adj u v → W u v = 0)
    (s : List V) (hc : s.Chain' G.Adj) (hn : s.Nodup) :
    (∑ u ∈ s.toFinset, ∑ v ∈ s.toFinset, W u v) = 2*along W s := by
  induction s with
  | nil => simp [along]
  | cons u s ih =>
    cases s with
    | nil => simp [along, hoff u u (G.loopless u)]
    | cons v l =>
      let T := (v::l).toFinset
      have un : u ∉ T := by simpa [T] using (List.nodup_cons.mp hn).1
      have row : ∑ z ∈ T, W u z = W u v := by
        apply Finset.sum_eq_single v
        · intro z hz hne
          have hm : z ∈ l := by simpa [T, hne] using hz
          exact hoff _ _ (spine_no_chord ht hc hn hm)
        · intro hv; exact False.elim (hv (by simp [T]))
      have col : ∑ z ∈ T, W z u = W u v := by
        calc
          _ = ∑ z ∈ T, W u z := Finset.sum_congr rfl (fun z _ => hsymm z u)
          _ = _ := row
      rw [List.toFinset_cons]
      change (∑ x ∈ insert u T, ∑ y ∈ insert u T, W x y) = 2*(W u v + along W (v::l))
      rw [Finset.sum_insert un]
      simp_rw [Finset.sum_insert un]
      rw [Finset.sum_add_distrib, row, col, hoff u u (G.loopless u), ih (List.chain'_cons.mp hc).2 hn.tail]
      ring

end Thesis.Trees
