import Thesis.CaterpillarModel
import Thesis.SpineIndex

namespace Thesis.Trees

/-- Travel through the degrees in list order and return to degree zero. -/
def travel (start : ℕ) : List ℕ → ℤ
  | [] => start
  | v::s => |(v:ℤ)-start| + travel v s

def irrBase (d : List ℕ) : ℤ :=
  (d.map (fun a => ((a:ℤ)-1)*((a:ℤ)-2))).sum - 2

private theorem base_map (d : List ℕ) : irrBase d =
    (d.map (fun (a:ℕ) => ((a:ℤ)-1)*((a:ℤ)-2))).sum - 2 := by
  unfold irrBase
  have conv (l : List ℕ) : (l >>= fun d => pure (d:ℤ)) = l.map (fun d : ℕ => (d:ℤ)) :=
    bind_pure_comp (fun d : ℕ => (d:ℤ)) l
  simp only [conv, List.map_map, Function.comp_def]

theorem irrBase_perm {x y : List ℕ} (h : x.Perm y) : irrBase x=irrBase y := by
  rw [base_map,base_map]
  exact congrArg (·-2) (h.map _).sum_eq

private theorem travel_pairs (u : ℕ) (s : List ℕ) : travel u s =
    ((u::s).zipWith (fun (a b : ℕ) => |(b:ℤ)-a|) s).sum + ((u::s).getLast! : ℕ) := by
  induction s generalizing u with
  | nil => simp [travel]
  | cons v s ih =>
    rw [travel,ih v]
    simp only [List.zipWith_cons_cons,List.sum_cons,show (u::v::s).getLast! = (v::s).getLast! by rfl]
    omega

/-- Lemma 2.2.1. Only the variation of the cycle 0,x₁,…,xₖ,0 depends on the order. -/
theorem albertson_variation {n : ℕ} (G : Graph n) (x : List ℕ) (hx : Admissible x) (hG : Realizes G x) :
    edgeIndex G 1 = irrBase x + travel 0 x := by
  rw [spine_index G x hx hG 1 (by decide),spineTerms,base_map]
  have conv (l : List ℕ) : (l >>= fun d => pure (d:ℤ)) = l.map (fun d : ℕ => (d:ℤ)) :=
    bind_pure_comp (fun d : ℕ => (d:ℤ)) l
  simp only [conv, List.map_map, List.zipWith_map, Function.comp_def,pow_one]
  have muls : x.map (fun (a:ℕ) => ((a:ℤ)-2)*((a:ℤ)-1)) =
      x.map (fun (a:ℕ) => ((a:ℤ)-1)*((a:ℤ)-2)) := List.map_congr_left (fun _ _ => mul_comm ..)
  rw [muls]
  cases x with
  | nil => have := hx.1; simp at this
  | cons u s =>
    rw [travel,travel_pairs]
    simp only [List.head!_cons,List.tail_cons,Nat.cast_zero,sub_zero,abs_of_nonneg (Int.natCast_nonneg _)]
    ring

theorem travel_ge_start (a : ℕ) (s : List ℕ) : (a:ℤ) ≤ travel a s := by
  induction s generalizing a with
  | nil => rfl
  | cons b s ih =>
    rw [travel]
    linarith [ih b,neg_abs_le ((b:ℤ)-a)]

theorem travel_via (a v : ℕ) {s : List ℕ} (hv : v ∈ s) :
    |(v:ℤ)-a| + v ≤ travel a s := by
  induction s generalizing a with
  | nil => simp at hv
  | cons b s ih =>
    rw [travel]
    rcases List.mem_cons.mp hv with rfl | h
    · linarith [travel_ge_start v s]
    · linarith [ih b h, abs_sub_le (v:ℤ) b a]

theorem travel_descending (a : ℕ) (s : List ℕ) (hd : (a::s).Pairwise (· ≥ ·)) :
    travel a s = a := by
  induction s generalizing a with
  | nil => rfl
  | cons b s ih =>
    have hab := (List.pairwise_cons.mp hd).1 b List.mem_cons_self
    rw [travel, ih b (List.pairwise_cons.mp hd).2,abs_of_nonpos (sub_nonpos.mpr (show (b:ℤ)≤a by exact_mod_cast hab))]
    omega

theorem descending_value {n : ℕ} (G : Graph n) (d : List ℕ) (hd : Admissible d) (hG : Realizes G d)
    (hs : d.Pairwise (· ≥ ·)) : edgeIndex G 1 = irrBase d + 2*(d.head!:ℤ) := by
  rw [albertson_variation G d hd hG]
  cases d with
  | nil => have := hd.1; simp at this
  | cons a t =>
    rw [travel,travel_descending a t hs]
    simp only [Nat.cast_zero, sub_zero, abs_of_nonneg (Int.natCast_nonneg _), List.head!_cons]
    ring

theorem albertson_minimum (d : List ℕ) (hd : Admissible d) (hs : d.Pairwise (· ≥ ·)) :
    IsLeast (values (fun G => edgeIndex G 1) d) (irrBase d + 2*(d.head!:ℤ)) := by
  obtain ⟨n,G,hG⟩ := exists_realization d hd
  refine ⟨⟨n,G,d,.rfl,hG,descending_value G d hd hG hs⟩,?_⟩
  rintro y ⟨_,F,x,hperm,hF,rfl⟩
  have hx : Admissible x := ⟨hd.1.trans_eq hperm.length_eq.symm,fun _ h => hd.2 _ (hperm.mem_iff.mp h)⟩
  change _ ≤ edgeIndex F 1
  rw [albertson_variation F x hx hF,irrBase_perm hperm]
  have hhead : d.head! ∈ d := by cases d with
                                 | nil => have := hd.1; simp at this
                                 | cons _ _ => simp
  have bound := travel_via 0 d.head! (hperm.mem_iff.mpr hhead)
  simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Int.natCast_nonneg _)] at bound
  omega

end Thesis.Trees
