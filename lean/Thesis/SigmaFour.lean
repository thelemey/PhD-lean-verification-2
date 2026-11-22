import Thesis.SigmaExpansion
import Mathlib.Data.List.Permutation

namespace Thesis.Trees

set_option maxHeartbeats 3000000

/-- Lemma 3.1.3. Among the 24 labelled orders of four sorted degrees,
the displayed two orders attain the minimum and maximum quadratic terms. -/
theorem four_rank_extrema (d₁ d₂ d₃ d₄ : ℕ) (h₁ : 2≤d₁) (h₁₂ : d₁≤d₂)
    (h₂₃ : d₂≤d₃) (h₃₄ : d₃≤d₄) (r : List ℕ) (hr : r.Perm [1,2,3,4]) :
    rankEnergy [d₁,d₂,d₃,d₄] [1,3,4,2] ≤ rankEnergy [d₁,d₂,d₃,d₄] r ∧
      rankEnergy [d₁,d₂,d₃,d₄] r ≤ rankEnergy [d₁,d₂,d₃,d₄] [4,1,2,3] := by
  have hm : r∈[1,2,3,4].permutations := (List.mem_permutations).2 hr
  norm_num [List.permutations] at hm
  have c₁ : ((d₁-1:ℕ):ℤ)=(d₁:ℤ)-1 := Nat.cast_sub (by omega)
  have c₂ : ((d₂-1:ℕ):ℤ)=(d₂:ℤ)-1 := Nat.cast_sub (by omega)
  have c₃ : ((d₃-1:ℕ):ℤ)=(d₃:ℤ)-1 := Nat.cast_sub (by omega)
  have c₄ : ((d₄-1:ℕ):ℤ)=(d₄:ℤ)-1 := Nat.cast_sub (by omega)
  have h₁₂' : (d₁:ℤ)≤d₂ := by exact_mod_cast h₁₂
  have h₂₃' : (d₂:ℤ)≤d₃ := by exact_mod_cast h₂₃
  have h₃₄' : (d₃:ℤ)≤d₄ := by exact_mod_cast h₃₄
  have p₁₂₂₃ : 0≤((d₂:ℤ)-d₁)*(d₃-d₂) := mul_nonneg (sub_nonneg.mpr h₁₂') (sub_nonneg.mpr h₂₃')
  have p₁₂₃₄ : 0≤((d₂:ℤ)-d₁)*(d₄-d₃) := mul_nonneg (sub_nonneg.mpr h₁₂') (sub_nonneg.mpr h₃₄')
  have p₂₃₃₄ : 0≤((d₃:ℤ)-d₂)*(d₄-d₃) := mul_nonneg (sub_nonneg.mpr h₂₃') (sub_nonneg.mpr h₃₄')
  have hx : 0≤(d₁:ℤ)-1 := sub_nonneg.mpr (by exact_mod_cast (show 1≤d₁ by omega))
  have p₁₂x : 0≤((d₂:ℤ)-d₁)*(d₁-1) := mul_nonneg (sub_nonneg.mpr h₁₂') hx
  have p₂₃x : 0≤((d₃:ℤ)-d₂)*(d₁-1) := mul_nonneg (sub_nonneg.mpr h₂₃') hx
  have p₃₄x : 0≤((d₄:ℤ)-d₃)*(d₁-1) := mul_nonneg (sub_nonneg.mpr h₃₄') hx
  have s₁₂ : 0≤((d₂:ℤ)-d₁)^2 := sq_nonneg _
  have s₂₃ : 0≤((d₃:ℤ)-d₂)^2 := sq_nonneg _
  have s₃₄ : 0≤((d₄:ℤ)-d₃)^2 := sq_nonneg _
  rcases hm with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
    constructor <;>
    simp [rankEnergy,route,rankValue,squareDiff,c₁,c₂,c₃,c₄] <;>
    ring_nf at * <;> nlinarith

end Thesis.Trees
