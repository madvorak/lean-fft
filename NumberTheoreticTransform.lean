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


lemma index_ok {t : ℕ} (i : Fin (level t)) : 2 * i.val + 1 < level t.succ := by
  unfold level
  have hi := Fin.is_lt i
  linarith

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

/-
#eval  NTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval FNTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval  NTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval FNTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval  NTT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval FNTT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval  NTT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
#eval FNTT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
-/

lemma lema (n : ℕ) (f : Fin (level n.succ) → ZMod M) :
  List.sum (List.map f (List.finRange (level n + level n))) =
  List.sum (List.map (f ∘ for_eve) (List.finRange (level n))) +
  List.sum (List.map (f ∘ for_odd) (List.finRange (level n))) :=
by sorry

theorem transform_fast_correct : transform = transform_fast := by
  apply funext
  intro t
  induction' t with n ih <;> ext ω x j
  · have jz : j = (0 : Fin 1)
    · exact Fin.ext (Fin.coe_fin_one j)
    rw [jz]
    unfold transform transform_fast dotProduct Finset.univ Fintype.elems Fin.fintype
    simp
    rfl
  unfold transform_fast
  rw [←ih]
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
    rw [append_lef] -- Do not apply `Fin.append_left` directly !!!
    clear append_lef
    show
      (fun j => ω ^ (i.val * j.val)) ⬝ᵥ x =
                    (fun j => (ω * ω) ^ (i.val * j.val)) ⬝ᵥ (fun i => x (for_eve i))
      + ω ^ i.val * (fun j => (ω * ω) ^ (i.val * j.val)) ⬝ᵥ (fun i => x (for_odd i))
    unfold dotProduct Finset.univ Fintype.elems Fin.fintype
    simp
    show
      List.sum (List.map (fun j => ω ^ (i.val * j.val) * x j) (List.finRange (level n + level n)))
      =
        List.sum (List.map (fun j => (ω * ω) ^ (i.val * j.val) * x (for_eve j)) (List.finRange (level n)))
      + ω ^ i.val *
        List.sum (List.map (fun j => (ω * ω) ^ (i.val * j.val) * x (for_odd j)) (List.finRange (level n)))
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
      · sorry
      · sorry
    rw [lema, ←List.sum_map_mul_left]
    congr
    ext k
    unfold for_odd
    sorry
  · -- Do not apply `Fin.append_right` directly !!!
    sorry
