import Thesis.SpinePath
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange

namespace Thesis.Trees

open SimpleGraph Finset
open scoped Classical

/-- Positions on the path are adjacent exactly when their integer labels differ by one. -/
def spineGraph (k : ℕ) : SimpleGraph (Fin k) where
  Adj i j := i.val+1=j.val ∨ j.val+1=i.val
  symm _ _ h := h.symm
  loopless _ h := by omega

theorem spine_degree_le_two {k : ℕ} (i : Fin k) : (spineGraph k).degree i ≤ 2 := by
  classical
  let T := ((spineGraph k).neighborFinset i).image Fin.val
  have sub : T ⊆ {i.val-1,i.val+1} := by
    intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    have h := ((spineGraph k).mem_neighborFinset i j).mp hj
    change i.val+1=j.val ∨ j.val+1=i.val at h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hc := Finset.card_le_card sub
  dsimp [T] at hc
  rw [Finset.card_image_of_injective _ Fin.val_injective, card_neighborFinset_eq_degree] at hc
  exact hc.trans ((Finset.card_insert_le _ _).trans (by simp))

abbrev ModelVertex {k : ℕ} (p : Fin k → ℕ) := Fin k ⊕ (Σ i, Fin (p i))

def caterpillarGraph {k : ℕ} (p : Fin k → ℕ) : SimpleGraph (ModelVertex p) where
  Adj
    | .inl i,.inl j => (spineGraph k).Adj i j
    | .inl i,.inr l => i=l.1
    | .inr l,.inl i => l.1=i
    | .inr _,.inr _ => False
  symm := by intro u v h; cases u <;> cases v <;> first | exact (spineGraph k).symm h | exact h.symm | exact h
  loopless := by intro u; cases u with
                 | inl i => exact (spineGraph k).loopless i
                 | inr _ => exact id

theorem model_spine_degree {k : ℕ} (p : Fin k → ℕ) (i : Fin k) :
    (caterpillarGraph p).degree (.inl i) = (spineGraph k).degree i + p i := by
  classical
  let leaves := (univ : Finset (Fin (p i))).image (fun z => (⟨i,z⟩ : Σ j, Fin (p j)))
  have neigh : (caterpillarGraph p).neighborFinset (.inl i) =
      ((spineGraph k).neighborFinset i).disjSum leaves := by
    ext v
    cases v with
    | inl j => simp [caterpillarGraph]
    | inr l =>
      obtain ⟨j,z⟩ := l
      simp only [mem_neighborFinset,inr_mem_disjSum,leaves,Finset.mem_image,Finset.mem_univ,true_and]
      change i=j ↔ ∃ w : Fin (p i), (⟨i,w⟩ : Σ j, Fin (p j))=⟨j,z⟩
      constructor
      · rintro rfl; exact ⟨z,rfl⟩
      · rintro ⟨_,h⟩; exact congrArg Sigma.fst h
  change ((caterpillarGraph p).neighborFinset (.inl i)).card = _
  rw [neigh,Finset.card_disjSum,card_neighborFinset_eq_degree]
  have inj : Function.Injective (fun z : Fin (p i) => (⟨i,z⟩ : Σ j, Fin (p j))) := fun _ _ h => by simpa using h
  simp [leaves,Finset.card_image_of_injective _ inj]

theorem model_leaf_degree {k : ℕ} (p : Fin k → ℕ) (l : Σ i, Fin (p i)) :
    (caterpillarGraph p).degree (.inr l) = 1 := by
  classical
  have neigh : (caterpillarGraph p).neighborFinset (.inr l) = {Sum.inl l.1} := by
    ext v
    cases v <;> simp [caterpillarGraph, eq_comm]
  change ((caterpillarGraph p).neighborFinset (.inr l)).card=1
  simp [neigh]

private theorem tree_of_parent_cover {V : Type*} [Fintype V] (G : SimpleGraph V) (root : V) (p : V → V)
    (hc : G.Connected) (cover : ∀ u v, G.Adj u v →
      (u≠root ∧ p u=v) ∨ (v≠root ∧ p v=u)) : G.IsTree := by
  classical
  let E := (univ.erase root).image (fun v => s(v,p v))
  have sub : G.edgeFinset ⊆ E := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have ha := (G.mem_edgeSet).mp (SimpleGraph.mem_edgeFinset.mp he)
      rcases cover u v ha with ⟨h,he⟩ | ⟨h,he⟩
      · exact Finset.mem_image.mpr ⟨u,by simp [h],by rw [he]⟩
      · exact Finset.mem_image.mpr ⟨v,by simp [h],by rw [he,Sym2.eq_swap]⟩
  have hle := (Finset.card_le_card sub).trans (Finset.card_image_le (f:=fun v => s(v,p v)))
  have hcount := hc.card_vert_le_card_edgeSet_add_one
  apply SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hc,?_⟩
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card, ← G.edgeFinset_card] at hcount ⊢
  rw [Finset.card_erase_of_mem (Finset.mem_univ root), Finset.card_univ] at hle
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  omega

theorem model_tree {k : ℕ} (hk : 0 < k) (p : Fin k → ℕ) : (caterpillarGraph p).IsTree := by
  let c : Fin k := ⟨0,hk⟩
  let root : ModelVertex p := .inl c
  let par : ModelVertex p → ModelVertex p
    | .inl i => .inl ⟨i.val-1,by omega⟩
    | .inr l => .inl l.1
  have toSpine (j : ℕ) (hj : j < k) : (caterpillarGraph p).Reachable root (.inl ⟨j,hj⟩) := by
    induction j with
    | zero => exact Reachable.refl _
    | succ j ih =>
      have e : (caterpillarGraph p).Adj (.inl ⟨j,by omega⟩) (.inl ⟨j+1,hj⟩) := Or.inl rfl
      exact (ih (by omega)).trans e.reachable
  have reaches (v : ModelVertex p) : (caterpillarGraph p).Reachable root v := by
    cases v with
    | inl i => exact toSpine i.val i.isLt
    | inr l =>
      have e : (caterpillarGraph p).Adj (.inl l.1) (.inr l) := rfl
      exact (toSpine _ l.1.isLt).trans e.reachable
  haveI : Nonempty (ModelVertex p) := ⟨root⟩
  apply tree_of_parent_cover _ root par ⟨fun u v => (reaches u).symm.trans (reaches v)⟩
  intro u v h
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      change i.val+1=j.val ∨ j.val+1=i.val at h
      rcases h with h|h
      · right
        constructor
        · intro H; have := Sum.inl.inj H; change j=c at this; have := congrArg Fin.val this; dsimp [c] at this; omega
        · exact congrArg Sum.inl (Fin.ext (by change j.val-1=i.val; omega))
      · left
        constructor
        · intro H; have := Sum.inl.inj H; change i=c at this; have := congrArg Fin.val this; dsimp [c] at this; omega
        · exact congrArg Sum.inl (Fin.ext (by change i.val-1=j.val; omega))
    | inr l => exact Or.inr ⟨by simp [root], congrArg Sum.inl (Eq.symm h)⟩
  | inr l =>
    cases v with
    | inl i => exact Or.inl ⟨by simp [root], congrArg Sum.inl h⟩
    | inr _ => exact False.elim h


private theorem degree_as_card {V : Type*} (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = Nat.card (G.neighborSet v) := by
  rw [Nat.card_eq_fintype_card,G.card_neighborSet_eq_degree]

private theorem transport_degree {V : Type*} {n : ℕ} (T : SimpleGraph V) (G : Graph n)
    (iso : T ≃g G) (z : V) [Fintype (T.neighborSet z)] : degree G (iso z) = T.degree z := by
  classical
  unfold degree
  rw [degree_as_card,degree_as_card]
  exact (Nat.card_congr (iso.mapNeighborSet z)).symm

/-- Section 1.2. Every ordered list of admissible full spine degrees is realized
by a finite labelled caterpillar, including the two-vertex spine. -/
theorem exists_realization (x : List ℕ) (hx : Admissible x) :
    ∃ (n : ℕ) (G : Graph n), Realizes G x := by
  classical
  let k := x.length
  let p (i : Fin k) := x.get i - (spineGraph k).degree i
  let T := caterpillarGraph p
  let N := Fintype.card (ModelVertex p)
  let e := Fintype.equivFin (ModelVertex p)
  let G := T.map e.toEmbedding
  let iso : T ≃g G := SimpleGraph.Iso.map e T
  let vertex (i : Fin k) : Fin N := e (.inl i)
  have hT := model_tree (by have := hx.1; dsimp [k]; omega : 0<k) p
  have hG : G.IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨iso.connected_iff.mp hT.isConnected,?_⟩
    rw [← Nat.card_congr iso.mapEdgeSet, ← Nat.card_congr iso.toEquiv]
    exact (SimpleGraph.isTree_iff_connected_and_card.mp hT).2
  have deg (z : ModelVertex p) : degree G (e z) = T.degree z :=
    transport_degree T G iso z
  have dcore (i : Fin k) : degree G (vertex i) = x.get i := by
    rw [show vertex i = e (.inl i) from rfl,deg,model_spine_degree]
    have h := hx.2 _ (List.get_mem x i)
    exact Nat.add_sub_of_le ((spine_degree_le_two i).trans h)
  refine ⟨N,G,hG,List.ofFn vertex,List.nodup_ofFn_ofInjective (e.injective.comp Sum.inl_injective),?_,?_,?_⟩
  · rw [List.map_ofFn, ← List.ofFn_get x]
    exact congrArg List.ofFn (funext dcore)
  · intro v
    obtain ⟨z,rfl⟩ := e.surjective v
    rcases z with i|l
    · constructor
      · intro _; change 2 ≤ degree G (vertex i); rw [dcore]; exact hx.2 _ (List.get_mem x i)
      · intro _; exact List.mem_ofFn.mpr ⟨i,rfl⟩
    · rw [deg,model_leaf_degree]
      simp only [List.mem_ofFn, Nat.not_ofNat_le_one, iff_false, not_exists]
      intro i H
      exact Sum.noConfusion (e.injective H)
  · intro i hi
    have H : i+1 < k := by simpa using hi
    have a : T.Adj (.inl ⟨i,by omega⟩) (.inl ⟨i+1,H⟩) := Or.inl rfl
    simpa [List.get_ofFn,vertex,iso] using iso.map_rel_iff.mpr a

/-- Every permuted admissible list has a realization; its labels may be chosen independently. -/
theorem perm_realization {x y : List ℕ} (hy : y.Perm x) (hx : Admissible x) :
    ∃ (n : ℕ) (G : Graph n), Realizes G y := by
  apply exists_realization
  exact ⟨hx.1.trans_eq hy.length_eq.symm,fun _ ha => hx.2 _ (hy.mem_iff.mp ha)⟩

end Thesis.Trees
