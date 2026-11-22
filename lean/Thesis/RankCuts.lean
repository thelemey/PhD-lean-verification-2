import Thesis.SigmaCycle

namespace Thesis.Trees

def covered (u v j l : ℕ) : Prop := min u v ≤ min j l ∧ max j l < max u v
instance (u v j l : ℕ) : Decidable (covered u v j l) := inferInstanceAs (Decidable (_ ∧ _))

def cutWeight (j l u v : ℕ) : ℕ := if covered u v j l then 1 else 0

theorem cutWeight_symm (j l u v : ℕ) : cutWeight j l u v=cutWeight j l v u := by
  simp only [cutWeight,covered,min_comm u v,max_comm u v]

theorem cuts_as_route (r : List ℕ) (j l : ℕ) : crossings r j l = route (cutWeight j l) 0 r 0 := by
  let B (e : ℕ × ℕ) := decide (covered e.1 e.2 j l)
  have beq : (fun (u,v) => decide (min u v ≤ min j l) && decide (max j l < max u v)) = B := by
    funext e
    simp only [B,covered,Bool.decide_and]
  have general (a : ℕ) (s : List ℕ) (b : ℕ) :
      (((a::(s++[b])).zip (s++[b])).filter B).length = route (cutWeight j l) a s b := by
    induction s generalizing a with
    | nil =>
      by_cases h : covered a b j l <;> simp [route,cutWeight,B,h]
    | cons v s ih =>
      simp only [List.cons_append,List.zip_cons_cons,List.filter_cons,route]
      by_cases h : covered a v j l <;> simp [B,h,cutWeight,← ih v,Nat.add_comm]
  unfold crossings
  rw [beq]
  exact general 0 r 0

private theorem arc_hits (a : ℕ) (s : List ℕ) (b j l : ℕ) (ha : a ≤ j) (hb : l<b) (hj : j ≤ l)
    (avoid : ∀ v ∈ s, v ≤ j ∨ l<v) : 1 ≤ route (cutWeight j l) a s b := by
  induction s generalizing a with
  | nil =>
    have h : covered a b j l := by unfold covered; omega
    simp [route,cutWeight,h]
  | cons v s ih =>
    rw [route]
    rcases avoid v List.mem_cons_self with hv|hv
    · have h := ih v hv (fun w hw => avoid w (List.mem_cons_of_mem _ hw))
      omega
    · have h : covered a v j l := by unfold covered; omega
      simp [cutWeight,h]

private theorem arc_hits_down (a : ℕ) (s : List ℕ) (b j l : ℕ) (ha : l<a) (hb : b ≤ j) (hj : j ≤ l)
    (avoid : ∀ v ∈ s, v ≤ j ∨ l<v) : 1 ≤ route (cutWeight j l) a s b := by
  rw [← route_reverse (cutWeight j l) (cutWeight_symm j l) b s a]
  exact arc_hits b s.reverse a j l hb ha hj (by simpa using avoid)

theorem rank_mem {k : ℕ} {r : List ℕ} (hr : r.Perm (List.range' 1 k)) (i : ℕ) :
    i ∈ r ↔ 1 ≤ i ∧ i ≤ k := by
  rw [hr.mem_iff,List.mem_range'_1]; omega

theorem rank_nodup {k : ℕ} {r : List ℕ} (hr : r.Perm (List.range' 1 k)) : r.Nodup :=
  hr.nodup_iff.mpr (List.nodup_range' _)

/-- Each nontrivial rank cut is crossed on the outward and the return arc. -/
theorem diagonal_cut_lower {k : ℕ} {r : List ℕ} (hr : r.Perm (List.range' 1 k)) (j : ℕ) (hj : j<k) :
    2 ≤ crossings r j j := by
  obtain ⟨s,t,he⟩ := List.append_of_mem ((rank_mem hr k).mpr ⟨by omega,le_rfl⟩)
  rw [cuts_as_route,he,route_split]
  have left := arc_hits 0 s k j j (Nat.zero_le _) hj le_rfl (fun _ _ => by omega)
  have right := arc_hits_down k t 0 j j hj (Nat.zero_le _) le_rfl (fun _ _ => by omega)
  omega

/-- The unique intermediate rank can lie on at most one of the two arcs. -/
theorem next_cut_lower {k : ℕ} {r : List ℕ} (hr : r.Perm (List.range' 1 k)) (j : ℕ) (hj : j+1<k) :
    1 ≤ crossings r j (j+1) := by
  obtain ⟨s,t,he⟩ := List.append_of_mem ((rank_mem hr k).mpr ⟨by omega,le_rfl⟩)
  rw [cuts_as_route,he,route_split]
  have nd := rank_nodup hr
  rw [he] at nd
  have avoids (l : List ℕ) (h : j+1 ∉ l) : ∀ v ∈ l, v≤j ∨ j+1<v := by
    intro v hv
    have : v≠j+1 := fun e => h (e ▸ hv)
    omega
  by_cases h : j+1 ∈ s
  · have hnot : j+1 ∉ t := fun e => (List.nodup_append.mp nd).2.2 h (List.mem_cons_of_mem k e)
    have right := arc_hits_down k t 0 j (j+1) hj (Nat.zero_le _) (by omega) (avoids t hnot)
    omega
  · have left := arc_hits 0 s k j (j+1) (Nat.zero_le _) hj (by omega) (avoids s h)
    omega

theorem cut_lower_bounds {k : ℕ} {r : List ℕ} (hr : r.Perm (List.range' 1 k)) :
    (∀ j < k, 2 ≤ crossings r j j) ∧ ∀ j, j+1<k → 1 ≤ crossings r j (j+1) :=
  ⟨diagonal_cut_lower hr,next_cut_lower hr⟩

end Thesis.Trees
