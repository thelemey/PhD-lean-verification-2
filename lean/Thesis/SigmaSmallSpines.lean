import Thesis.SpineIndex
import Mathlib.Algebra.Order.Ring.Abs

namespace Thesis.Trees

/-- Lemma 3.1.1. Closed sigma formula for a caterpillar with three spine vertices. -/
theorem sigma_three_spine {n : ℕ} (G : Graph n) (d₁ d₂ d₃ : ℕ)
    (h₁ : 2≤d₁) (h₂ : 2≤d₂) (h₃ : 2≤d₃) (hG : Realizes G [d₁,d₂,d₃]) :
    edgeIndex G 2 = ((d₁:ℤ)-1)^3+((d₂:ℤ)-1)^3+((d₃:ℤ)-1)^3+
      ((d₁:ℤ)-d₂)^2+((d₂:ℤ)-d₃)^2-((d₂:ℤ)-1)^2 := by
  have ha : Admissible [d₁,d₂,d₃] := by
    refine ⟨by norm_num,?_⟩
    intro d hd
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hd
    rcases hd with rfl|rfl|rfl <;> assumption
  rw [spine_index G _ ha hG 2 (by omega)]
  unfold spineTerms
  norm_num
  ring

end Thesis.Trees
