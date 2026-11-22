import Thesis.SpineIndex

namespace Thesis.Trees

open Finset SimpleGraph SimpleGraph.Walk
open scoped Classical

variable {V : Type*} {G : SimpleGraph V}

/-- The unique simple path from v toward the chosen root. -/
noncomputable def rootPath (ht : G.IsTree) (root v : V) : G.Walk v root :=
  (ht.existsUnique_path v root).choose

theorem rootPath_isPath (ht : G.IsTree) (root v : V) : (rootPath ht root v).IsPath :=
  (ht.existsUnique_path v root).choose_spec.1

theorem rootPath_eq (ht : G.IsTree) (root : V) {v : V} (p : G.Walk v root) (hp : p.IsPath) :
    rootPath ht root v = p := (ht.existsUnique_path v root).unique (rootPath_isPath ht root v) hp

noncomputable def parent (ht : G.IsTree) (root v : V) : V := (rootPath ht root v).snd

theorem parent_adj (ht : G.IsTree) (root : V) {v : V} (hv : v ≠ root) : G.Adj v (parent ht root v) :=
  adj_snd (not_nil_of_ne hv)

theorem parent_depth (ht : G.IsTree) (root : V) {v : V} (hv : v ≠ root) :
    (rootPath ht root (parent ht root v)).length + 1 = (rootPath ht root v).length := by
  rw [parent, rootPath_eq ht root (rootPath ht root v).tail (rootPath_isPath ht root v).tail]
  exact length_tail_add_one (not_nil_of_ne hv)

private theorem parent_of_deeper_edge (ht : G.IsTree) (root : V) {u v : V}
    (h : G.Adj u v) (hl : (rootPath ht root u).length ≤ (rootPath ht root v).length) :
    v ≠ root ∧ parent ht root v = u := by
  have hnot : v ∉ (rootPath ht root u).support := by
    intro hmem
    let p := rootPath ht root u
    have htake := (ht.existsUnique_path u v).unique ((rootPath_isPath ht root u).takeUntil hmem) (IsPath.of_adj h)
    have hdrop := rootPath_eq ht root (p.dropUntil v hmem) ((rootPath_isPath ht root u).dropUntil hmem)
    have he := congrArg Walk.length (p.take_spec hmem)
    change p.takeUntil v hmem = h.toWalk at htake
    rw [length_append, htake, ← hdrop] at he
    change 1 + (rootPath ht root v).length = (rootPath ht root u).length at he
    omega
  have he := rootPath_eq ht root (.cons h.symm (rootPath ht root u))
    ((cons_isPath_iff _ _).2 ⟨rootPath_isPath ht root u,hnot⟩)
  refine ⟨?_,?_⟩
  · rintro rfl
    rw [rootPath_eq ht v .nil IsPath.nil] at he
    cases he
  · rw [parent,he,snd_cons]

theorem edge_orientation (ht : G.IsTree) (root : V) {u v : V} (h : G.Adj u v) :
    (u ≠ root ∧ parent ht root u = v) ∨ (v ≠ root ∧ parent ht root v = u) := by
  rcases le_total (rootPath ht root u).length (rootPath ht root v).length with H | H
  · exact Or.inr (parent_of_deeper_edge ht root h H)
  · exact Or.inl (parent_of_deeper_edge ht root h.symm H)

private theorem orientation_asymm (ht : G.IsTree) (root : V) {u v : V}
    (h : u ≠ root ∧ parent ht root u = v) : ¬(v ≠ root ∧ parent ht root v = u) := by
  intro e
  have h₁ := parent_depth ht root h.1
  have h₂ := parent_depth ht root e.1
  rw [h.2] at h₁
  rw [e.2] at h₂
  omega

/-- An edge sum over both orientations equals twice the sum over nonroot children.
This reindexing works for any symmetric integer weight. -/
theorem rooted_edge_sum [Fintype V] (ht : G.IsTree) (root : V)
    (f : V → V → ℤ) (hs : ∀ u v, f u v = f v u) :
    (∑ u, ∑ v, if G.Adj u v then f u v else 0) =
      2*∑ v ∈ univ.erase root, f v (parent ht root v) := by
  classical
  let A (u v : V) := if u ≠ root ∧ parent ht root u=v then f u v else 0
  have split (u v : V) : (if G.Adj u v then f u v else 0) = A u v + A v u := by
    by_cases h : G.Adj u v
    · rcases edge_orientation ht root h with H|H
      · simp [A,h,H,orientation_asymm ht root H]
      · simp [A,h,H,orientation_asymm ht root H,hs u v]
    · have no (e : u ≠ root ∧ parent ht root u=v) : False := h (e.2 ▸ parent_adj ht root e.1)
      have no' (e : v ≠ root ∧ parent ht root v=u) : False := h (e.2 ▸ (parent_adj ht root e.1).symm)
      simp only [A, if_neg h, if_neg no, if_neg no', zero_add]
  have row (u : V) : ∑ v, A u v = if u ≠ root then f u (parent ht root u) else 0 := by
    by_cases h : u = root <;> simp [A,h]
  simp_rw [split,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun u v => A v u)]
  simp_rw [row]
  rw [← Finset.sum_filter]
  have e : (univ.filter (fun u => u ≠ root)) = univ.erase root := by ext; simp
  rw [e]
  ring

theorem tree_degree_sum {n : ℕ} (G : Graph n) (ht : G.IsTree) (root : Fin n) :
    (∑ v, (degree G v : ℤ)) = 2*((n:ℤ)-1) := by
  have h := rooted_edge_sum ht root (fun _ _ => 1) (fun _ _ => rfl)
  simp_rw [sum_incidence G (fun _ => 1), mul_one] at h
  have hpos : 0 < n := Nat.zero_lt_of_lt root.isLt
  simpa [Nat.cast_sub (by omega : 1 ≤ n)] using h


theorem tree_degree_pos {n : ℕ} (hn : 2 ≤ n) (G : Graph n) (ht : G.IsTree) (v : Fin n) :
    0 < degree G v := by
  let w : Fin n := if v.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have h : v ≠ w := by
    intro e
    have he := congrArg Fin.val e
    dsimp [w] at he
    split at he <;> simp only at he <;> omega
  exact (G.degree_pos_iff_exists_adj v).mpr ⟨_,parent_adj ht w h⟩

/-- Lemma 2.1.2. The internal degrees determine the number of leaves and the order. -/
theorem leaf_count {n : ℕ} (hn : 2 ≤ n) (G : Graph n) (ht : G.IsTree) :
    let I := univ.filter (fun v => 2 ≤ degree G v)
    let L := univ.filter (fun v => degree G v=1)
    L.card + I.card = n ∧ (L.card:ℤ) = (∑ v ∈ I,(degree G v:ℤ)) - 2*I.card + 2 := by
  classical
  intro I L
  have e : L=Iᶜ := by
    ext v
    simp only [L,I,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl]
    have := tree_degree_pos hn G ht v
    omega
  have hc : L.card + I.card = n := by
    rw [e,Finset.card_compl,Fintype.card_fin,Nat.sub_add_cancel (by simpa using I.card_le_univ)]
  have hsum : (∑ v ∈ I,(degree G v:ℤ)) + (L.card:ℤ) = ∑ v,(degree G v:ℤ) := by
    rw [← Finset.sum_add_sum_compl I, ← e]
    congr 1
    calc
      (L.card:ℤ) = ∑ _ ∈ L,(1:ℤ) := by simp
      _ = _ := Finset.sum_congr rfl (fun v hv => by
        have := (Finset.mem_filter.mp hv).2
        exact_mod_cast this.symm)
  have htotal := tree_degree_sum G ht ⟨0,by omega⟩
  have hc' : (L.card:ℤ) + I.card = n := by exact_mod_cast hc
  exact ⟨hc,by linarith⟩

end Thesis.Trees
