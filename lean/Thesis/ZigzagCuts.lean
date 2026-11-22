import Thesis.RankCuts

namespace Thesis.Trees

private def odds (k : ℕ) := (List.range' 1 k).filter (fun i => i%2==1)
private def evens (k : ℕ) := ((List.range' 1 k).filter (fun i => i%2==0)).reverse

theorem zigzag_perm (k : ℕ) : (zigzagRanks k).Perm (List.range' 1 k) := by
  have e : (fun i : ℕ => !(i%2==1)) = (fun i => i%2==0) := by
    funext i
    rcases (show i%2=0 ∨ i%2=1 by omega) with h|h <;> simp [h]
  have H := List.filter_append_perm (fun i : ℕ => i%2==1) (List.range' 1 k)
  rw [e] at H
  exact ((List.reverse_perm _).append_left _).trans H

private theorem odds_succ (k : ℕ) : odds (k+1)=if (k+1)%2=1 then odds k++[k+1] else odds k := by
  rw [odds,List.range'_1_concat]
  by_cases h : (k+1)%2=1 <;> simp [odds,Nat.add_comm 1 k,h]

private theorem evens_succ (k : ℕ) : evens (k+1)=if (k+1)%2=0 then (k+1)::evens k else evens k := by
  rw [evens,List.range'_1_concat]
  by_cases h : (k+1)%2=0 <;> simp [evens,Nat.add_comm 1 k,h]

private theorem zigzag_insert (k : ℕ) : zigzagRanks (k+1)=odds k++(k+1)::evens k := by
  change odds (k+1)++evens (k+1)=_
  rw [odds_succ,evens_succ]
  by_cases h : (k+1)%2=0
  · simp [h,show (k+1)%2≠1 by omega]
  · simp [h,show (k+1)%2=1 by omega]

private theorem zigzag_ends (n : ℕ) :
    (odds (n+2)=odds n++[n+1] ∧ evens (n+2)=(n+2)::evens n) ∨
    (odds (n+2)=odds n++[n+2] ∧ evens (n+2)=(n+1)::evens n) := by
  simp only [odds_succ,evens_succ]
  by_cases h : (n+1)%2=1
  · left; simp [h,show (n+1)%2≠0 by omega,show (n+2)%2=0 by omega,show (n+2)%2≠1 by omega]
  · right; simp [h,show (n+1)%2=0 by omega,show (n+2)%2≠0 by omega,show (n+2)%2=1 by omega]

private theorem route_insert (W : ℕ → ℕ → ℤ) (a b u z v : ℕ) (s t : List ℕ) :
    route W a (s++u::z::v::t) b = route W a (s++u::v::t) b - W u v + W u z + W z v := by
  rw [route_split,route_split]
  simp only [route]; ring

theorem zigzag_route_step (W : ℕ → ℕ → ℤ) (hs : ∀ a b, W a b=W b a) (n : ℕ) :
    route W 0 (zigzagRanks (n+3)) 0 = route W 0 (zigzagRanks (n+2)) 0 -
      W (n+1) (n+2) + W (n+1) (n+3) + W (n+2) (n+3) := by
  rw [zigzag_insert (n+2)]
  change _ = route W 0 (odds (n+2)++evens (n+2)) 0 - _ + _ + _
  rcases zigzag_ends n with ⟨ho,he⟩ | ⟨ho,he⟩
  · rw [ho,he]; simp only [List.append_assoc,List.singleton_append]
    rw [route_insert,hs (n+3) (n+2)]
  · rw [ho,he]; simp only [List.append_assoc,List.singleton_append]
    rw [route_insert,hs (n+2) (n+1),hs (n+3) (n+1)]
    ring

/-- The edges in the zigzag join ranks at distance two, plus its two end edges. -/
theorem zigzag_route (W : ℕ → ℕ → ℤ) (hs : ∀ a b, W a b=W b a) (n : ℕ) :
    route W 0 (zigzagRanks (n+2)) 0 = W 0 1 + W (n+1) (n+2) +
      ((List.range (n+1)).map (fun i => W i (i+2))).sum := by
  induction n with
  | zero =>
    change W 0 1 + (W 1 2 + W 2 0) = W 0 1 + W 1 2 + (W 0 2 + 0)
    rw [hs 2 0]; ring
  | succ n ih =>
    rw [zigzag_route_step W hs n,ih,List.range_succ (n:=n+1)]
    simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    ring

theorem cast_cut_route (a b : ℕ) (r : List ℕ) (j l : ℕ) :
    ((route (cutWeight j l) a r b : ℕ) : ℤ) = route (fun u v => (cutWeight j l u v:ℤ)) a r b := by
  induction r generalizing a with
  | nil => rfl
  | cons u s ih => simp [route,ih]

/-- The comparison coefficients include cuts outside the rank interval as zero. -/
def zigzagCount (k j l : ℕ) : ℕ :=
  if max j l < k then
    if j=l then 2 else if j+1=l ∨ l+1=j then 1 else 0
  else 0

private theorem ideal_step (n j l : ℕ) (hjl : j ≤ l) :
    (zigzagCount (n+3) j l : ℤ) = (zigzagCount (n+2) j l : ℤ) -
      cutWeight j l (n+1) (n+2) + cutWeight j l (n+1) (n+3) + cutWeight j l (n+2) (n+3) := by
  simp only [zigzagCount,cutWeight,covered,min_eq_left hjl,max_eq_right hjl,
    min_eq_left (show n+1≤n+2 by omega),min_eq_left (show n+1≤n+3 by omega),
    min_eq_left (show n+2≤n+3 by omega),max_eq_right (show n+1≤n+2 by omega),
    max_eq_right (show n+1≤n+3 by omega),max_eq_right (show n+2≤n+3 by omega)]
  split_ifs <;> omega

theorem zigzag_crossings_ordered (n j l : ℕ) (hjl : j≤l) :
    crossings (zigzagRanks (n+2)) j l = zigzagCount (n+2) j l := by
  have eq (i : ℕ) : (crossings (zigzagRanks (i+2)) j l : ℤ) =
      route (fun u v => (cutWeight j l u v:ℤ)) 0 (zigzagRanks (i+2)) 0 := by
    rw [cuts_as_route,cast_cut_route]
  induction n with
  | zero =>
    change crossings [1,2] j l = zigzagCount 2 j l
    rw [cuts_as_route]
    simp only [route,cutWeight,covered,zigzagCount,min_eq_left hjl,max_eq_right hjl]
    norm_num
    split_ifs <;> omega
  | succ n ih =>
    have h := zigzag_route_step (fun u v => (cutWeight j l u v:ℤ))
      (fun u v => congrArg Nat.cast (cutWeight_symm j l u v)) n
    rw [← eq (n+1),← eq n,ih,← ideal_step n j l hjl] at h
    exact_mod_cast h

end Thesis.Trees
