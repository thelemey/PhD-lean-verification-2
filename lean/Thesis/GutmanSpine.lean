import Thesis.RootedTree
import Thesis.TreeDistanceLiterature

namespace Thesis.Trees

open Finset

private theorem weight_sum (x : List ℕ) :
    (spineWeights x).sum = (x.map (fun (d:ℕ) => (d:ℤ))).sum - x.length := by
  induction x with
  | nil => simp [spineWeights]
  | cons v x ih =>
    change ((v:ℤ)-1) + (spineWeights x).sum = _
    rw [ih]; simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]; ring

/-- The number of vertices is 2 + the sum of the shifted spine degrees. -/
theorem realization_order {n : ℕ} (G : Graph n) (x : List ℕ) (hx : Admissible x)
    (hG : Realizes G x) : (n:ℤ) = 2+(spineWeights x).sum := by
  classical
  obtain ⟨ht,s,hn,he,hm,_⟩ := hG
  have length : s.length=x.length := by rw [← he,List.length_map]
  have hn₂ : 2 ≤ n := hx.1.trans (length ▸ (by simpa using hn.length_le_card : s.length ≤ n))
  obtain ⟨h₁,h₂⟩ := leaf_count hn₂ G ht
  let S := s.toFinset
  have eqS : univ.filter (fun v => 2 ≤ degree G v) = S := by ext v; simp [S,hm]
  rw [eqS] at h₁ h₂
  have card : S.card=x.length := by simpa [S,List.toFinset_card_of_nodup hn] using length
  have sumList (l : List (Fin n)) (hl : l.Nodup) :
      (∑ u ∈ l.toFinset,(degree G u:ℤ)) = (l.map (fun u => (degree G u:ℤ))).sum := by
    induction l with
    | nil => simp
    | cons v l ih => simp [List.toFinset_cons,(List.nodup_cons.mp hl).1,ih hl.tail]
  have sum : (∑ v ∈ S,(degree G v:ℤ)) = (x.map (fun d : ℕ => (d:ℤ))).sum := by
    rw [sumList s hn,← he]; simp [List.map_map, Function.comp_def]
  rw [sum,card] at h₂
  rw [card] at h₁
  rw [weight_sum]
  omega

/-- The Gutman index depends on the ordered degrees through the prefix/suffix products. -/
def gutmanScore (x : List ℕ) : ℤ :=
  let w := spineWeights x
  let n := 2+w.sum
  4*((n-1)^2 + cutProducts w) - (n-1)*(2*n-1)

theorem gutman_spine {n : ℕ} (G : Graph n) (x : List ℕ) (hx : Admissible x) (hG : Realizes G x) :
    gutman G = gutmanScore x := by
  rw [Literature.tree_gutman_wiener G hG.1,Literature.caterpillar_wiener G x hx hG,
      realization_order G x hx hG]
  rfl

end Thesis.Trees
