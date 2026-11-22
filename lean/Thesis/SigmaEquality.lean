import Thesis.RankHamilton

namespace Thesis.Trees

private theorem reverse_score {d r : List ℕ} (hd : Admissible d) (hr : r.Perm (List.range' 1 d.length))
    {n : ℕ} (G : Graph n) (hG : Realizes G (rankOrder d r).reverse) :
    edgeIndex G 2=sigmaBase d+rankEnergy d r := by
  have he : (rankOrder d r).reverse=rankOrder d r.reverse := (List.map_reverse ..).symm
  rw [he] at hG
  rw [sigma_rank_score hd ((List.reverse_perm r).trans hr) G hG]
  unfold rankEnergy
  rw [route_reverse _ (fun u v => by unfold squareDiff; ring)]

/-- Relabelling tied spine degrees preserves all three optimality tests together. -/
theorem criterion_relabel {d r s : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·))
    (hr : r.Perm (List.range' 1 d.length)) (ht : s.Perm (List.range' 1 d.length))
    (he : rankOrder d r=rankOrder d s) : cutCriterion d r ↔ cutCriterion d s := by
  obtain ⟨n,G,hG⟩ := perm_realization (rank_order_perm hr) hd
  exact (optimal_iff_cuts hd hs hr G hG).symm.trans (optimal_iff_cuts hd hs ht G (he ▸ hG))

/-- With distinct degrees, an optimal realization determines the zigzag up to reversal. -/
theorem distinct_optimal {d r : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·)) (hn : d.Nodup)
    (hr : r.Perm (List.range' 1 d.length)) {n : ℕ} (G : Graph n) (hG : Realizes G (rankOrder d r)) :
    IsLeast (values (fun G => edgeIndex G 2) d) (edgeIndex G 2) ↔
      rankOrder d r=rankOrder d (zigzagRanks d.length) ∨
      rankOrder d r=(rankOrder d (zigzagRanks d.length)).reverse := by
  constructor
  · intro hm
    have near := near_of_criterion hd hs hn hr ((optimal_iff_cuts hd hs hr G hG).mp hm)
    obtain ⟨k,hk⟩ : ∃ k, d.length=k+2 := ⟨d.length-2,by have := hd.1; omega⟩
    rw [hk] at hr ⊢
    rcases near_zigzag k r hr near with he|he
    · exact Or.inl (congrArg (rankOrder d) he)
    · right; rw [he]; exact List.map_reverse ..
  · intro h
    have hm := (sigma_minimum d hd hs).2
    have hz := zigzag_perm d.length
    have eq : edgeIndex G 2=minSigmaValue d := by
      rcases h with h|h
      · exact sigma_rank_score hd hz G (h ▸ hG)
      · exact reverse_score hd hz G (h ▸ hG)
    rwa [eq]

/-- Theorem 3.3.3. The exact bound from theorem 3.1.2, with all equality cases. -/
theorem sigma_bound_equality {d r : List ℕ} (hd : Admissible d) (hs : d.Pairwise (· ≤ ·))
    (hr : r.Perm (List.range' 1 d.length)) {n : ℕ} (G : Graph n) (hG : Realizes G (rankOrder d r)) :
    minSigmaValue d ≤ edgeIndex G 2 ∧ (edgeIndex G 2=minSigmaValue d ↔ cutCriterion d r) ∧
      (∀ s, s.Perm (List.range' 1 d.length) → rankOrder d r=rankOrder d s →
        (cutCriterion d r ↔ cutCriterion d s)) := by
  have least := (sigma_minimum d hd hs).2
  have mem : edgeIndex G 2 ∈ values (fun F => edgeIndex F 2) d :=
    ⟨n,G,_,rank_order_perm hr,hG,rfl⟩
  refine ⟨least.2 mem,?_,fun _ ht he => criterion_relabel hd hs hr ht he⟩
  rw [← optimal_iff_cuts hd hs hr G hG]
  exact ⟨fun h => h.symm ▸ least,fun other => other.unique least⟩

/-- The complete fourth defence statement, including labelled repeated degrees. -/
theorem claim4 : Claim4 := by
  intro d hd hs z S
  obtain ⟨⟨n,G,hG,eq⟩,least⟩ := sigma_minimum d hd hs
  refine ⟨⟨n,G,hG,eq.symm ▸ least⟩,?_⟩
  intro r hr m F hF
  exact ⟨optimal_iff_cuts hd hs hr F hF,fun hn => distinct_optimal hd hs hn hr F hF⟩

end Thesis.Trees
