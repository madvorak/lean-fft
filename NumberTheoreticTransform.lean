import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases

namespace Matrix


--  level n = 2 ^ n
def level : ℕ → ℕ
| 0   => 1
| n+1 => level n + level n

def e : ℕ := 4
def M : ℕ := level e + 1
def vektor : Type := Fin (level e) → ZMod M


def transform (t : ℕ) (ω : ZMod M) (x : Fin (level t) → ZMod M) : (Fin (level t) → ZMod M) :=
fun (i : Fin (level t)) => dotProduct (fun (j : Fin (level t)) => ω ^ (i.val * j.val)) x

def NTS : vektor → vektor := transform e 3

def negate (x : vektor) : vektor :=
fun i => - (x i)

def NTT : vektor → vektor := negate ∘ transform e 6


lemma index_ok₁ {K : ℕ} (i : Fin K) : 2 * i.val + 1 < K + K := by
  have hi := Fin.is_lt i
  linarith

lemma index_ok₀ {K : ℕ} (i : Fin K) : 2 * i.val < K + K :=
Nat.lt_of_succ_lt (index_ok₁ i)

lemma index_ok {t : ℕ} (i : Fin (level t)) : 2 * i.val + 1 < level t.succ :=
index_ok₁ i

def for_eve {n : ℕ} (k : Fin (level n)) : Fin (level n.succ) :=
⟨2 * k.val, Nat.lt_of_succ_lt (index_ok k)⟩

def for_odd {n : ℕ} (k : Fin (level n)) : Fin (level n.succ) :=
⟨2 * k.val + 1, index_ok k⟩

def transform_fast (t : ℕ) (ω : ZMod M) (x : Fin (level t) → ZMod M) : (Fin (level t) → ZMod M) :=
match t with
| 0   => x
| n+1 =>
  let a := transform_fast n (ω * ω) (fun (i : Fin (level n)) => x (for_eve i))
  let b := transform_fast n (ω * ω) (fun (i : Fin (level n)) => x (for_odd i))
  Fin.append
    (fun j => a j + ω ^ j.val * b j)
    (fun j => a j - ω ^ j.val * b j)

def FNTS : vektor → vektor := transform_fast e 3

def FNTT : vektor → vektor := negate ∘ transform_fast e 6


#eval  NTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval FNTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval  NTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval FNTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval  NTT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval FNTT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval  NTT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
#eval FNTT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]


lemma take_succ_succ {m n : ℕ} (hm0 : m < n) (hm1 : m + 1 < n) :
  List.take m.succ.succ (List.finRange n) = List.take m (List.finRange n) ++ [⟨m, hm0⟩, ⟨m + 1, hm1⟩] :=
by
  have hLfR : n = List.length (List.finRange n)
  · rw [List.length_finRange]
  have hmL1 : m + 1 < List.length (List.finRange n)
  · rwa [hLfR] at hm1
  have hmL0 : m < List.length (List.finRange n)
  · rwa [hLfR] at hm0
  rw [List.take_succ, List.get?_eq_get hmL1, Option.to_list_some]
  rw [List.take_succ, List.get?_eq_get hmL0, Option.to_list_some]
  rw [List.append_assoc]
  simp [hLfR]

lemma perm_onik {α : Type} (a b x y z : List α) (hyp : a ++ b ~ x ++ y ++ z) : a ++ b ~ x ++ z ++ y := by
  have hhh : x ++ y ++ z ~ x ++ z ++ y
  · rw [List.append_assoc, List.append_assoc]
    rw [List.perm_append_left_iff]
    exact List.perm_append_comm
  exact List.Perm.trans hyp hhh

lemma range_perm_aux (N : ℕ) (n : ℕ) (hn : n ≤ N) : List.take (n + n) (List.finRange (N + N)) ~
    List.map (fun k => ⟨2 * k, index_ok₀ k⟩) (List.take n (List.finRange N)) ++
    List.map (fun k => ⟨2 * k + 1, index_ok₁ k⟩) (List.take n (List.finRange N)) := by
  induction' n with m ih
  · simp
  have hlen : m < List.length (List.finRange N)
  · rw [List.length_finRange]
    exact hn
  rw [List.take_succ, List.get?_eq_get hlen, Option.to_list_some]
  have mmss : Nat.succ m + Nat.succ m = (m + m).succ.succ
  · exact Nat.succ_add m (Nat.succ m)
  rw [mmss]
  have mm0 : m + m < N + N
  · linarith
  have mm1 : m + m + 1 < N + N
  · linarith
  rw [take_succ_succ mm0 mm1]
  have hm : m < N
  · exact hn
  rw [List.get_finRange]
  show
    List.take (m + m) (List.finRange (N + N)) ++ [⟨m+m, mm0⟩, ⟨m+m+1, mm1⟩] ~
      List.map (fun k => ⟨2 * k, index_ok₀ k⟩)
        (List.take m (List.finRange N) ++ [⟨m, hm⟩]) ++
      List.map (fun k => ⟨2 * k + 1, index_ok₁ k⟩)
        (List.take m (List.finRange N) ++ [⟨m, hm⟩])
  rw [List.map_append, List.map_append, List.map_singleton, List.map_singleton]
  rw [←List.append_assoc]
  convert_to
    (List.take (m + m) (List.finRange (N + N)) ++ [⟨m+m, mm0⟩]) ++ [⟨m+m+1, mm1⟩] ~
      List.map (fun k => ⟨2 * k, index_ok₀ k⟩) (List.take m (List.finRange N)) ++ [⟨m+m, mm0⟩] ++
      List.map (fun k => ⟨2 * k + 1, index_ok₁ k⟩) (List.take m (List.finRange N)) ++ [⟨m+m+1, mm1⟩]
  · rw [List.append_assoc]
    rfl
  · congr
    · rw [two_mul]
    · rw [two_mul]
  rw [List.perm_append_right_iff]
  apply perm_onik
  rw [List.perm_append_right_iff]
  apply ih
  exact le_of_lt hn

lemma my_range_perm (n : ℕ) : List.finRange (n + n) ~
    List.map (fun k => ⟨2 * k, index_ok₀ k⟩) (List.finRange n) ++
    List.map (fun k => ⟨2 * k + 1, index_ok₁ k⟩) (List.finRange n) := by
  have takenn : List.take (List.finRange (n + n)).length (List.finRange (n + n)) ~
      List.map (fun k => ⟨2 * k, index_ok₀ k⟩) (List.take (List.finRange n).length (List.finRange n)) ++
      List.map (fun k => ⟨2 * k + 1, index_ok₁ k⟩) (List.take (List.finRange n).length (List.finRange n))
  · convert range_perm_aux n n (le_of_eq rfl)
    · rw [List.length_finRange]
    · rw [List.length_finRange]
    · rw [List.length_finRange]
  rw [List.take_length, List.take_length] at takenn
  exact takenn

lemma sum_range_eq_sum_add_sum (n : ℕ) (f : Fin (level n.succ) → ZMod M) :
  List.sum (List.map f (List.finRange (level n + level n))) =
  List.sum (List.map (f ∘ for_eve) (List.finRange (level n))) +
  List.sum (List.map (f ∘ for_odd) (List.finRange (level n))) :=
by
  rw [←List.map_map, ←List.map_map, ←List.sum_append, ←List.map_append]
  have list_range_perm : List.finRange (level n + level n) ~
      List.map for_eve (List.finRange (level n)) ++ List.map for_odd (List.finRange (level n))
  · apply my_range_perm
  have list_map_perm : List.map f (List.finRange (level n + level n)) ~
      List.map f (List.map for_eve (List.finRange (level n)) ++ List.map for_odd (List.finRange (level n)))
  · exact List.Perm.map f list_range_perm
  rw [←Multiset.coe_sum, ←Multiset.coe_sum]
  exact congrArg Multiset.sum (Iff.mpr Multiset.coe_eq_coe list_map_perm)

theorem transform_fast_correct (t : ℕ) (ω : ZMod M) (hyp : 0 < t → ω ^ level (t-1) = -1) : transform_fast t ω = transform t ω := by
  revert ω
  induction' t with n ih <;> intro ω hyp <;> ext x j
  · rw [show j = (0 : Fin 1) from Fin.ext (Fin.coe_fin_one j)]
    unfold transform transform_fast dotProduct Finset.univ Fintype.elems Fin.fintype
    simp
    rfl
  unfold transform_fast
  simp at hyp
  specialize ih (ω * ω) (by {
    intro nz
    rw [mul_pow, ←pow_add]
    rw [←Nat.sub_add_cancel nz] at hyp
    exact hyp
  })
  rw [ih]
  symm
  induction' j using Fin.addCases with i i
  · have append_lef :
      @Fin.append (level (n+0)) (level (n+0)) (ZMod M)
        (fun j => transform n (ω * ω) (fun i => x (for_eve i)) j + ω ^ j.val * transform n (ω * ω)
          (fun i => x (for_odd i)) j)
        (fun j => transform n (ω * ω) (fun i => x (for_eve i)) j - ω ^ j.val * transform n (ω * ω)
          (fun i => x (for_odd i)) j)
        ((Fin.castAdd (level n) : Fin (level n) ↪o Fin (level n + level n)).toEmbedding i) =
      transform n (ω * ω) (fun i => x (for_eve i)) i + ω ^ i.val * transform n (ω * ω) (fun i => x (for_odd i)) i
    · apply Fin.append_left
    rw [append_lef] -- Do not rw `Fin.append_left` directly !!!
    clear append_lef
    show
      (fun j => ω ^ (i.val * j.val)) ⬝ᵥ x =
                    (fun j => (ω * ω) ^ (i.val * j.val)) ⬝ᵥ (fun i => x (for_eve i))
      + ω ^ i.val * (fun j => (ω * ω) ^ (i.val * j.val)) ⬝ᵥ (fun i => x (for_odd i))
    unfold dotProduct Finset.univ Fintype.elems Fin.fintype
    simp
    let a := ω ^ i.val
    convert_to
      List.sum (List.map (fun j => a ^ j.val * x j) (List.finRange (level n + level n)))
      =
        List.sum (List.map (fun j => a ^ (2 * j.val) * x (for_eve j)) (List.finRange (level n)))
      + a *
        List.sum (List.map (fun j => a ^ (2 * j.val) * x (for_odd j)) (List.finRange (level n)))
    · congr
      simp_rw [pow_mul]
    · congr
      · show
          (fun j => (ω * ω) ^ (i.val * j.val) * x (for_eve j)) =
          (fun j => a ^ (2 * j.val) * x (for_eve j))
        ext k
        rw [mul_pow, pow_mul]
        show a ^ k.val * a ^ k.val * x (for_eve k) = a ^ (2 * k.val) * x (for_eve k)
        ring
      · show
          (fun j => (ω * ω) ^ (i.val * j.val) * x (for_odd j)) =
          (fun j => a ^ (2 * j.val) * x (for_odd j))
        ext k
        rw [mul_pow, pow_mul]
        show a ^ k.val * a ^ k.val * x (for_odd k) = a ^ (2 * k.val) * x (for_odd k)
        ring
    rw [sum_range_eq_sum_add_sum, ←List.sum_map_mul_left]
    congr
    ext k
    rw [Function.comp_apply]
    show a ^ (2 * k.val + 1) * x (for_odd k) = a * (a ^ (2 * k.val) * x (for_odd k))
    ring
  · have append_rig :
      @Fin.append (level (n+0)) (level (n+0)) (ZMod M)
        (fun j => transform n (ω * ω) (fun i => x (for_eve i)) j + ω ^ j.val * transform n (ω * ω)
          (fun i => x (for_odd i)) j)
        (fun j => transform n (ω * ω) (fun i => x (for_eve i)) j - ω ^ j.val * transform n (ω * ω)
          (fun i => x (for_odd i)) j)
        ((Fin.natAdd (level n) : Fin (level n) ↪o Fin (level n + level n)).toEmbedding i) =
      transform n (ω * ω) (fun i => x (for_eve i)) i - ω ^ i.val * transform n (ω * ω) (fun i => x (for_odd i)) i
    · apply Fin.append_right
    rw [append_rig] -- Do not rw `Fin.append_right` directly !!!
    clear append_rig
    show
      transform (Nat.succ n) ω x _ =
                    (fun j => (ω * ω) ^ (i.val * j.val)) ⬝ᵥ (fun i => x (for_eve i))
      - ω ^ i.val * (fun j => (ω * ω) ^ (i.val * j.val)) ⬝ᵥ (fun i => x (for_odd i))
    unfold transform dotProduct Finset.univ Fintype.elems Fin.fintype
    simp
    let a := ω ^ i.val
    convert_to
      List.sum (List.map (fun j => (-a) ^ j.val * x j) (List.finRange (level n + level n)))
      =
        List.sum (List.map (fun j => a ^ (2 * j.val) * x (for_eve j)) (List.finRange (level n)))
      + (-a) *
        List.sum (List.map (fun j => a ^ (2 * j.val) * x (for_odd j)) (List.finRange (level n)))
    · congr
      ext k
      rw [pow_mul, pow_add, hyp, neg_one_mul]
    · rw [neg_mul, sub_eq_add_neg]
      congr <;> ext k <;> rw [mul_pow, pow_mul, ←pow_two, ←pow_mul, mul_comm 2]
    rw [sum_range_eq_sum_add_sum, ←List.sum_map_mul_left]
    congr
    · ext k
      rw [Function.comp_apply]
      show (-a) ^ (2 * k.val) * x (for_eve k) = (a ^ (2 * k.val) * x (for_eve k))
      rw [pow_mul, neg_pow_two, ←pow_mul]
    · ext k
      rw [Function.comp_apply]
      show (-a) ^ (2 * k.val + 1) * x (for_odd k) = (-a) * (a ^ (2 * k.val) * x (for_odd k))
      rw [pow_add, pow_mul, neg_pow_two, ←pow_mul]
      ring

theorem FNTS_correct : FNTS = NTS := by
  apply transform_fast_correct
  decide

theorem FNTT_correct : FNTT = NTT := by
  unfold FNTT NTT
  rw [transform_fast_correct]
  decide

#print axioms FNTS_correct
#print axioms FNTT_correct
