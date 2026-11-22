import Thesis.AlbertsonVariation

namespace Thesis.Trees

private def offsets (m : ℕ) (s : List ℕ) : ℤ := (s.map (fun (v:ℕ) => |(v:ℤ)-m|)).sum

private theorem offsets_perm (m : ℕ) {x y : List ℕ} (h : x.Perm y) : offsets m x=offsets m y :=
  (h.map _).sum_eq

private theorem travel_bound (m a : ℕ) (s : List ℕ) :
    travel a s ≤ |(a:ℤ)-m| + 2*offsets m s + m := by
  induction s generalizing a with
  | nil =>
    simp only [travel,offsets,List.map_nil,List.sum_nil,mul_zero,add_zero]
    linarith [le_abs_self ((a:ℤ)-m)]
  | cons b s ih =>
    rw [travel]
    have e : offsets m (b::s) = |(b:ℤ)-m| + offsets m s := rfl
    rw [e]
    linarith [ih b,abs_sub_le (b:ℤ) m a,abs_sub_comm (m:ℤ) a]

private def weave : List ℕ → List ℕ → List ℕ
  | [],l => l
  | h::hs,[] => h::hs
  | h::hs,l::ls => h::l::weave hs ls

private theorem weave_perm (hs ls : List ℕ) : (weave hs ls).Perm (hs++ls) := by
  induction hs generalizing ls with
  | nil => simp [weave]
  | cons h hs ih =>
    cases ls with
    | nil => simp [weave]
    | cons l ls => exact (List.perm_cons_append_cons l (ih ls)).cons h

private theorem weave_exact (m : ℕ) (hs ls : List ℕ) (hh : ∀ h ∈ hs, m ≤ h) (hl : ∀ l ∈ ls, l ≤ m)
    (lengths : hs.length=ls.length+1) (a : ℕ) (ha : a ≤ m) :
    travel a (weave hs ls) = |(a:ℤ)-m| + 2*offsets m (weave hs ls) + m := by
  induction ls generalizing a hs with
  | nil =>
    obtain ⟨h,rfl⟩ := List.length_eq_one_iff.mp (by simpa using lengths)
    have h₁ : (m:ℤ) ≤ h := by exact_mod_cast hh h List.mem_cons_self
    have h₂ : (a:ℤ) ≤ m := by exact_mod_cast ha
    simp [weave,travel,offsets,abs_of_nonneg (sub_nonneg.mpr h₁),
      abs_of_nonneg (sub_nonneg.mpr (h₂.trans h₁)),abs_of_nonpos (sub_nonpos.mpr h₂)]
    ring
  | cons l ls ih =>
    cases hs with
    | nil => simp at lengths
    | cons h hs =>
      have h₁ : (m:ℤ) ≤ h := by exact_mod_cast hh h List.mem_cons_self
      have h₂ : (a:ℤ) ≤ m := by exact_mod_cast ha
      have h₃ : l ≤ m := hl l List.mem_cons_self
      have h₄ : (l:ℤ) ≤ m := by exact_mod_cast h₃
      have e := ih hs (fun k hk => hh k (List.mem_cons_of_mem _ hk))
        (fun k hk => hl k (List.mem_cons_of_mem _ hk)) (by simpa using lengths) l h₃
      rw [weave,travel,travel,e]
      simp only [offsets,List.map_cons,List.sum_cons]
      rw [abs_of_nonneg (sub_nonneg.mpr (h₂.trans h₁)),abs_of_nonpos (sub_nonpos.mpr (h₄.trans h₁)),
        abs_of_nonpos (sub_nonpos.mpr h₂),abs_of_nonpos (sub_nonpos.mpr h₄),abs_of_nonneg (sub_nonneg.mpr h₁)]
      ring

private theorem offsets_above (m : ℕ) (s : List ℕ) (hs : ∀ v ∈ s, m ≤ v) :
    offsets m s = (s.sum:ℤ) - (s.length:ℤ)*m := by
  induction s with
  | nil => simp [offsets]
  | cons v s ih =>
    have h : (m:ℤ) ≤ v := by exact_mod_cast hs v List.mem_cons_self
    have e := ih (fun i hi => hs i (List.mem_cons_of_mem _ hi))
    change |(v:ℤ)-m| + offsets m s = _
    rw [e,abs_of_nonneg (sub_nonneg.mpr h)]
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

private theorem offsets_below (m : ℕ) (s : List ℕ) (hs : ∀ v ∈ s, v ≤ m) :
    offsets m s = (s.length:ℤ)*m - s.sum := by
  induction s with
  | nil => simp [offsets]
  | cons v s ih =>
    have h : (v:ℤ) ≤ m := by exact_mod_cast hs v List.mem_cons_self
    have e := ih (fun i hi => hs i (List.mem_cons_of_mem _ hi))
    change |(v:ℤ)-m| + offsets m s = _
    rw [e,abs_of_nonpos (sub_nonpos.mpr h)]
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

/-- The maximizing orders displayed in theorem 2.2.1. For even length the
median is inserted before the alternating high and low ranks. -/
def maximizingOrder (d : List ℕ) : List ℕ :=
  let h := (d.length+1)/2
  let j := d.length+1-h
  (if j=h then [] else [d[h]!]) ++ weave (d.take h) (d.drop j).reverse

/-- The median splits off exactly h high entries and h-1 low entries. If the
list length is even, its single leftover entry is the median. -/
private theorem median_split (d : List ℕ) (hd : 2 ≤ d.length) (hs : d.Pairwise (· ≥ ·)) :
    let h := (d.length+1)/2
    let hi := d.take h
    let lo := d.drop (d.length+1-h)
    ∃ m : ℕ, ∃ mid : List ℕ, (mid=[] ∨ mid=[m]) ∧ d=hi++mid++lo ∧
      hi.length=lo.length+1 ∧ (∀ z ∈ hi, m ≤ z) ∧ (∀ z ∈ lo, z ≤ m) ∧
      maximizingOrder d=mid++weave hi lo.reverse := by
  intro h hi lo
  have hh : h < d.length := by dsimp [h]; omega
  let m := d[h]
  have len : hi.length=lo.length+1 := by
    simp [hi,lo,List.length_take,List.length_drop,Nat.min_eq_left hh.le]; dsimp [h]; omega
  have cut : d = hi ++ m :: d.drop (h+1) := by
    rw [← List.drop_eq_getElem_cons hh]
    exact (List.take_append_drop h d).symm
  have sorted := hs
  rw [cut,List.pairwise_append] at sorted
  have high (z : ℕ) (hz : z ∈ hi) : m ≤ z := sorted.2.2 z hz m List.mem_cons_self
  have low (z : ℕ) (hz : z ∈ d.drop (h+1)) : z ≤ m := (List.pairwise_cons.mp sorted.2.1).1 z hz
  have ix : d.length+1-h=h ∨ d.length+1-h=h+1 := by dsimp [h]; omega
  rcases ix with e|e
  · have loweq : lo=m::d.drop (h+1) := by simpa only [lo,e] using List.drop_eq_getElem_cons hh
    refine ⟨m,[],Or.inl rfl,by simpa [loweq] using cut,len,high,?_,by simp [maximizingOrder,hi,lo,h] at e ⊢; simp [e]⟩
    intro z hz
    rw [loweq,List.mem_cons] at hz
    exact hz.elim (fun e => e.le) (low z)
  · have loweq : lo=d.drop (h+1) := by simp [lo,e]
    exact ⟨m,[m],Or.inr rfl,by simpa [loweq] using cut,len,high,fun z hz => low z (loweq ▸ hz),by
      change (if d.length+1-h=h then [] else [d[h]!]) ++ _ = [m] ++ _
      rw [if_neg (by omega),getElem!_pos d h hh]⟩


theorem maximum_variation (d : List ℕ) (hd : 2 ≤ d.length) (hs : d.Pairwise (· ≥ ·)) :
    let h := (d.length+1)/2
    let bound := 2*(((d.take h).sum:ℤ) - (d.drop (d.length+1-h)).sum)
    (maximizingOrder d).Perm d ∧ travel 0 (maximizingOrder d)=bound ∧
      ∀ x : List ℕ, x.Perm d → travel 0 x ≤ bound := by
  intro h bound
  let hi := d.take h
  let lo := d.drop (d.length+1-h)
  obtain ⟨m,mid,hm,cut,hlen,high,low,order⟩ := median_split d hd hs
  change d=hi++mid++lo at cut
  change hi.length=lo.length+1 at hlen
  change maximizingOrder d=mid++weave hi lo.reverse at order
  have hl : ∀ z ∈ lo.reverse, z ≤ m := by simpa using low
  have perm : (maximizingOrder d).Perm d := by
    rw [order]
    have hp := (weave_perm hi lo.reverse).trans ((List.Perm.refl hi).append (List.reverse_perm lo))
    exact (hp.append_left mid).trans ((List.perm_append_comm_assoc mid hi lo).trans
      (by rw [← List.append_assoc,← cut]))
  have midzero : offsets m mid=0 := by rcases hm with rfl|rfl <;> simp [offsets]
  have split : offsets m d = offsets m hi + offsets m mid + offsets m lo := by
    conv_lhs => rw [cut]
    simp [offsets,List.sum_append,add_assoc]
  have mass : (m:ℤ)+offsets m d = (hi.sum:ℤ)-lo.sum := by
    rw [split,midzero,offsets_above m hi high,offsets_below m lo low,hlen]
    push_cast
    ring
  have exact_weave (a : ℕ) (ha : a ≤ m) := weave_exact m hi lo.reverse high hl (by simpa using hlen) a ha
  have exact_order : travel 0 (maximizingOrder d) = 2*((m:ℤ)+offsets m (maximizingOrder d)) := by
    rw [order]
    rcases hm with rfl|rfl
    · simp only [List.nil_append]
      rw [exact_weave 0 (Nat.zero_le _)]
      simp only [Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg (Int.natCast_nonneg _)]
      ring
    · simp only [List.singleton_append,travel]
      rw [exact_weave m le_rfl]
      change _ = 2*((m:ℤ)+(|(m:ℤ)-m| + offsets m (weave hi lo.reverse)))
      simp only [Nat.cast_zero,sub_zero,sub_self,abs_zero,zero_add,abs_of_nonneg (Int.natCast_nonneg _)]
      ring
  refine ⟨perm,?_,?_⟩
  · change _ = 2*((hi.sum:ℤ)-lo.sum)
    rw [exact_order,offsets_perm m perm,mass]
  · intro x hx
    have hbound := travel_bound m 0 x
    simp only [Nat.cast_zero,zero_sub,abs_neg,abs_of_nonneg (Int.natCast_nonneg _),offsets_perm m hx] at hbound
    change _ ≤ 2*((hi.sum:ℤ)-lo.sum)
    linarith

/-- The upper value is attained by the explicit alternating arrangement, with the
median first in even length, and bounds every labelled caterpillar in the class. -/
theorem albertson_maximum (d : List ℕ) (hd : Admissible d) (hs : d.Pairwise (· ≥ ·)) :
    let h := (d.length+1)/2
    let M := irrBase d + 2*(((d.take h).sum:ℤ) - (d.drop (d.length+1-h)).sum)
    (∃ (n : ℕ) (G : Graph n), Realizes G (maximizingOrder d) ∧ edgeIndex G 1=M) ∧
      IsGreatest (values (fun G => edgeIndex G 1) d) M := by
  intro h M
  obtain ⟨hp,he,hb⟩ := maximum_variation d hd.1 hs
  obtain ⟨n,G,hG⟩ := perm_realization hp hd
  have adm {x : List ℕ} (h : x.Perm d) : Admissible x :=
    ⟨hd.1.trans_eq h.length_eq.symm,fun _ hv => hd.2 _ (h.mem_iff.mp hv)⟩
  have e : edgeIndex G 1 = M := by rw [albertson_variation G _ (adm hp) hG,irrBase_perm hp,he]
  refine ⟨⟨n,G,hG,e⟩,⟨n,G,_,hp,hG,e⟩,?_⟩
  rintro y ⟨_,F,x,hx,hF,rfl⟩
  change edgeIndex F 1 ≤ _
  rw [albertson_variation F x (adm hx) hF,irrBase_perm hx]
  exact add_le_add_left (hb x hx) _

/-- Section 1.3(2). Both extrema are values of realized finite graphs. -/
theorem claim2 : Claim2 := by
  intro d hd hs
  exact ⟨albertson_minimum d hd hs,(albertson_maximum d hd hs).2⟩

end Thesis.Trees
