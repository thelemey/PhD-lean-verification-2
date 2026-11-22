import Thesis.NearRanks

namespace Thesis.Trees

private abbrev topPair (n a b : ℕ) := (a=n+1 ∧ b=n+2) ∨ (a=n+2 ∧ b=n+1)

private def insertTop (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a::b::s => if topPair n a b then a::(n+3)::b::s else a::insertTop n (b::s)

private theorem insert_at (n : ℕ) (p : List ℕ) (a b : ℕ) (t : List ℕ)
    (hn : (p++a::b::t).Nodup) (hab : topPair n a b) :
    insertTop n (p++a::b::t)=p++a::(n+3)::b::t := by
  induction p with
  | nil => simp [insertTop,hab]
  | cons c p ih =>
    have hc := (List.nodup_cons.mp hn).1
    have ca : c≠a := by intro eq; subst c; simp at hc
    have cb : c≠b := by intro eq; subst c; simp at hc
    have h (v : ℕ) : ¬topPair n c v := by unfold topPair at *; omega
    have eq := ih (List.nodup_cons.mp hn).2
    cases p with
    | nil => simpa only [List.nil_append,List.cons_append,insertTop,if_neg (h _)] using congrArg (c::·) eq
    | cons y ys => simpa only [List.cons_append,insertTop,if_neg (h _)] using congrArg (c::·) eq

private theorem reverse_middle (p : List ℕ) (a b : ℕ) (t : List ℕ) :
    (p++a::b::t).reverse=t.reverse++b::a::p.reverse := by
  simp [List.reverse_append,List.reverse_cons,List.append_assoc]

private theorem reverse_triple (p : List ℕ) (a c b : ℕ) (t : List ℕ) :
    (p++a::c::b::t).reverse=t.reverse++b::c::a::p.reverse := by
  simp [List.reverse_append,List.reverse_cons,List.append_assoc]

private theorem insert_zigzag (n : ℕ) :
    insertTop n (zigzagRanks (n+2))=zigzagRanks (n+3) ∧
    insertTop n (zigzagRanks (n+2)).reverse=(zigzagRanks (n+3)).reverse := by
  obtain ⟨p,t,a,b,hab,lo,hi⟩ := zigzag_top_edge n
  have hn := rank_nodup (zigzag_perm (n+2))
  have hn' : (zigzagRanks (n+2)).reverse.Nodup := List.nodup_reverse.mpr hn
  rw [lo] at hn
  rw [lo,reverse_middle] at hn'
  have hba : topPair n b a := by unfold topPair; omega
  rw [lo,hi,reverse_middle,reverse_triple]
  exact ⟨insert_at n p a b t hn hab,insert_at n t.reverse b a p.reverse hn' hba⟩

private theorem perm_remove (n : ℕ) (p : List ℕ) (a b : ℕ) (t : List ℕ)
    (hr : (p++a::(n+3)::b::t).Perm (List.range' 1 (n+3))) :
    (p++a::b::t).Perm (List.range' 1 (n+2)) := by
  apply (List.perm_cons (n+3)).mp
  have lhs := @List.perm_middle ℕ (n+3) (p++[a]) (b::t)
  have rhs := @List.perm_middle ℕ (n+3) (List.range' 1 (n+2)) []
  simp only [List.append_assoc,List.singleton_append,List.append_nil] at lhs rhs
  rw [List.range'_1_concat,show 1+(n+2)=n+3 by omega] at hr
  exact lhs.symm.trans (hr.trans rhs)

private theorem pair_base {r : List ℕ} (hr : r.Perm (List.range' 1 2)) :
    r=zigzagRanks 2 ∨ r=(zigzagRanks 2).reverse := by
  change r.Perm [1,2] at hr
  change r=[1,2] ∨ r=[2,1]
  have hlen := hr.length_eq
  have h₁ := hr.mem_iff.mpr (by decide : 1 ∈ [1,2])
  have h₂ := hr.mem_iff.mpr (by decide : 2 ∈ [1,2])
  match r with
  | [] | [_] | _::_::_::_ => simp_all
  | [a,b] => simp_all only [List.mem_cons,List.mem_nil_iff,or_false]; rcases h₁ with h|h <;> rcases h₂ with g|g <;> (simp_all; try omega)

/-- A Hamiltonian rank cycle with jumps at most two has just two orientations. -/
theorem near_zigzag (n : ℕ) (r : List ℕ) (hr : r.Perm (List.range' 1 (n+2))) (hc : nearRoute 0 r 0) :
    r=zigzagRanks (n+2) ∨ r=(zigzagRanks (n+2)).reverse := by
  induction n generalizing r with
  | zero => exact pair_base hr
  | succ n ih =>
    have mem := (rank_mem hr (n+3)).mpr ⟨by omega,by omega⟩
    obtain ⟨s,t,rfl⟩ := List.append_of_mem mem
    have sides := (near_split 0 s (n+3) t 0).mp hc
    rcases List.eq_nil_or_concat s with h | ⟨p,a,h⟩
    · subst s; have hnear : nearRanks 0 (n+3) := sides.1; unfold nearRanks at hnear; omega
    subst s
    cases t with
    | nil => have hnear : nearRanks (n+3) 0 := sides.2; unfold nearRanks at hnear; omega
    | cons b t =>
      simp only [List.concat_eq_append,List.append_assoc,List.singleton_append] at hr hc ⊢
      have first := (near_split 0 p a ((n+3)::b::t) 0).mp hc
      have edges : nearRanks a (n+3) ∧ nearRanks (n+3) b ∧ nearRoute b t 0 := first.2
      have unique := rank_nodup hr
      have inner := (List.nodup_append.mp unique).2.1
      simp only [List.nodup_cons,List.mem_cons,not_or] at inner
      have ha := ((rank_mem hr a).mp (by simp)).2
      have hb := ((rank_mem hr b).mp (by simp)).2
      have hab : topPair n a b := by
        unfold topPair; unfold nearRanks at edges; omega
      have sub := perm_remove n p a b t hr
      have short : nearRoute 0 (p++a::b::t) 0 :=
        (near_split 0 p a (b::t) 0).mpr ⟨first.1,by
          exact ⟨by unfold nearRanks; unfold topPair at hab; omega,edges.2.2⟩⟩
      have eq := insert_at n p a b t (rank_nodup sub) hab
      rcases ih _ sub short with h|h
      · left; rw [← eq,h,(insert_zigzag n).1]
      · right; rw [← eq,h,(insert_zigzag n).2]

end Thesis.Trees
