import Thesis.SpineIndex

namespace Thesis.Trees

private def uniformDegrees (k m : ℕ) : List ℕ :=
  (m+1)::(List.replicate (k+1) (m+2)++[m+1])

private theorem repeat_differences (q : ℕ) (a b : ℤ) :
    (((List.replicate (q+1) a++[b]).zipWith
      (fun u v : ℤ => |v-u|^2) (List.replicate q a++[b])).sum) = |b-a|^2 := by
  induction q with
  | zero => simp
  | succ q ih =>
      simp only [List.replicate_succ,List.cons_append,List.zipWith_cons_cons,List.sum_cons]
      change |(a:ℤ)-a|^2+
        ((List.replicate (q+1) a++[b]).zipWith
          (fun u v : ℤ => |v-u|^2) (List.replicate q a++[b])).sum = _
      rw [ih]
      simp

private theorem uniform_terms (k m : ℕ) :
    spineTerms (uniformDegrees k m) 2 = 2*(m:ℤ)^3+(k+1)*m*(m+1)^2+2 := by
  unfold spineTerms uniformDegrees
  have conv (l : List ℕ) : (l >>= fun d => pure (d:ℤ))=l.map (fun d : ℕ => (d:ℤ)) :=
    bind_pure_comp (fun d : ℕ => (d:ℤ)) l
  simp only [conv,List.map_map,Function.comp_def,List.map_cons,List.map_append,List.map_replicate,List.map_singleton,List.sum_cons,
    List.sum_append,List.sum_replicate,List.sum_singleton,List.head!_cons,List.tail_cons]
  have last : ((m+1)::(List.replicate (k+1) (m+2)++[m+1])).getLast?=some (m+1) :=
    by simpa using (List.getLast?_concat (l:=(m+1)::List.replicate (k+1) (m+2)) (a:=m+1))
  rw [List.getLast!_eq_getLast?_getD]
  rw [last]
  simp only [Option.getD_some]
  rw [List.replicate_succ]
  simp only [List.cons_append,List.zipWith_cons_cons,List.sum_cons]
  norm_num
  have diff : ((List.zipWith (fun a b : ℤ => |b-a|^2)
      (((m:ℤ)+2)::(List.replicate k ((m:ℤ)+2)++[(m:ℤ)+1]))
      (List.replicate k ((m:ℤ)+2)++[(m:ℤ)+1])).sum)=1 := by
    have h := repeat_differences k (2+(m:ℤ)) (1+m)
    simpa [List.replicate_succ,add_comm] using h
  rw [diff]
  have oneabs : |(1:ℤ)|^2=1 := by decide
  rw [oneabs]
  ring

/-- Proposition 3.1.2 for a spine of length at least three. -/
theorem sigma_uniform_long {N : ℕ} (G : Graph N) (k m : ℕ) (hm : 1≤m)
    (hG : Realizes G (uniformDegrees k m)) :
    edgeIndex G 2 = 2*(m:ℤ)^3+(k+1)*m*(m+1)^2+2 := by
  have ha : Admissible (uniformDegrees k m) := by
    refine ⟨by simp [uniformDegrees],?_⟩
    intro d hd
    simp only [uniformDegrees,List.mem_cons,List.mem_append,List.mem_replicate,
      List.mem_singleton,List.mem_nil_iff,or_false] at hd
    rcases hd with h|h|h
    · omega
    · rcases h with ⟨_,rfl⟩; omega
    · omega
  rw [spine_index G _ ha hG 2 (by omega)]
  exact uniform_terms k m

/-- The two-vertex case of Proposition 3.1.2. -/
theorem sigma_uniform_two {N : ℕ} (G : Graph N) (m : ℕ) (hm : 1≤m)
    (hG : Realizes G [m+1,m+1]) : edgeIndex G 2=2*(m:ℤ)^3 := by
  have ha : Admissible [m+1,m+1] := by
    refine ⟨by norm_num,?_⟩
    intro d hd
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hd
    rcases hd with rfl|rfl <;> omega
  rw [spine_index G _ ha hG 2 (by omega)]
  unfold spineTerms
  norm_num
  ring

/-- Both cases of Proposition 3.1.2, with `k+3` vertices in the second family. -/
theorem sigma_uniform_formula :
    (∀ {N : ℕ} (G : Graph N) (m : ℕ), 1≤m → Realizes G [m+1,m+1] →
      edgeIndex G 2=2*(m:ℤ)^3) ∧
    (∀ {N : ℕ} (G : Graph N) (k m : ℕ), 1≤m → Realizes G (uniformDegrees k m) →
      edgeIndex G 2=2*(m:ℤ)^3+(k+1)*m*(m+1)^2+2) := by
  exact ⟨fun G m hm hG => sigma_uniform_two G m hm hG,
    fun G k m hm hG => sigma_uniform_long G k m hm hG⟩

end Thesis.Trees
