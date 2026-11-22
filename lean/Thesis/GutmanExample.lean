import Thesis.GutmanSwap
import Thesis.CaterpillarModel

namespace Thesis.Trees

private def localOrder := [7,6,6,4,2,4,7,8]
private def betterOrder := [8,6,6,2,4,4,7,7]

/-- Example 4.2.1. All 28 transpositions at the first realization are nonimproving;
another realization of the same degree multiset exceeds it by four. -/
theorem gutman_local_example :
    ∃ (n : ℕ) (G : Graph n), Realizes G localOrder ∧ LocallyMaximal G localOrder ∧ gutman G=10381 ∧
      ∃ (m : ℕ) (H : Graph m), Realizes H betterOrder ∧ gutman H=10385 ∧ betterOrder.Perm localOrder := by
  have had : Admissible localOrder := by unfold Admissible; decide
  have hbd : Admissible betterOrder := by unfold Admissible; decide
  obtain ⟨n,G,hG⟩ := exists_realization localOrder had
  obtain ⟨m,H,hH⟩ := exists_realization betterOrder hbd
  have table : ∀ u v : Fin 8, u<v → swapDifference localOrder u v ≤ 0 := by decide
  have loc : LocallyMaximal G localOrder := by
    intro u v hu hv K hK
    have hv' : v<8 := hv
    have h := table ⟨u,by omega⟩ ⟨v,hv'⟩ hu
    have e := swap_formula G localOrder had hG u v hu hv K hK
    change swapDifference localOrder u v ≤ 0 at h
    omega
  refine ⟨n,G,hG,loc,?_,m,H,hH,?_,?_⟩
  · rw [gutman_spine G _ had hG]; decide
  · rw [gutman_spine H _ hbd hH]; decide
  · decide

/-- All swap differences, the necessary local test, and its strict counterexample. -/
theorem claim5 : Claim5 := by
  refine ⟨fun G x hx hG => ⟨swap_formula G x hx hG,global_implies_local G x⟩,?_⟩
  obtain ⟨n,G,hG,hl,hval,m,H,hH,hbetter,hp⟩ := gutman_local_example
  exact ⟨n,G,localOrder,by unfold Admissible; decide,hG,hl,10385,⟨m,H,betterOrder,hp,hH,hbetter⟩,by omega⟩

end Thesis.Trees
