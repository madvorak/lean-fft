import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases

namespace Matrix


def e : ℕ := 4
def M : ℕ := 2^e + 1
def vektor : Type := Fin (2^e) → ZMod M


def transform (t : ℕ) (ω : ZMod M) (x : Fin (2^t) → ZMod M) : (Fin (2^t) → ZMod M) :=
fun (i : Fin (2^t)) => dotProduct (fun (j : Fin (2^t)) => ω ^ ((i : ℕ) * (j : ℕ))) x

def NTS : vektor → vektor := transform e 3

def negate (x : vektor) : vektor :=
fun i => - (x i)

def NTT : vektor → vektor := negate ∘ transform e 6

/-
#eval NTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval NTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval NTT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval NTT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
-/


lemma index_ok {t : ℕ} (i : Fin (2 ^ t)) : 2 * (i : ℕ) + 1 < 2 ^ t.succ := by
  show 2 * (i : ℕ) + 2 ≤ 2 ^ t.succ
  convert_to 2 * ((i : ℕ) + 1) ≤ 2 * 2 ^ t
  · rw [pow_succ]
  apply LinearOrderedCommMonoid.mul_le_mul_left
  exact Fin.is_lt i

def splitter {t : ℕ} (x : Fin (2 ^ t.succ) → ZMod M) :
  (Fin (2 ^ t) → ZMod M) × (Fin (2 ^ t) → ZMod M) :=
Prod.mk
  (fun (i : Fin (2 ^ t)) => x ⟨2 * (i : ℕ), Nat.lt_of_succ_lt (index_ok i)⟩)
  (fun (i : Fin (2 ^ t)) => x ⟨2 * (i : ℕ) + 1, index_ok i⟩)

def transform_fast (t : ℕ) (ω : ZMod M) (x : Fin (2^t) → ZMod M) : (Fin (2^t) → ZMod M) :=
match t with
| 0   => x
| n+1 =>
  let p := splitter x
  let a := transform_fast n (ω * ω) p.1
  let b := transform_fast n (ω * ω) p.2
  fun (i : Fin (2 ^ (n+1))) =>
    let j : ℕ := i
    if hj : (j : ℕ) < 2 ^ n
    then
      let J : Fin (2 ^ n) := ⟨j, hj⟩
      a J + ω ^ j * b J
    else
      let j' : ℕ := j - 2 ^ n
      let J' : Fin (2 ^ n) := ⟨j', by {
        push_neg at hj
        have hh : j < 2 ^ (n + 1)
        · exact Fin.is_lt i
        rw [pow_succ, two_mul, ←tsub_lt_iff_right hj] at hh
        exact hh
      }⟩
      a J' - ω ^ j' * b J'

def FNTS : vektor → vektor := transform_fast e 3
def FNTT : vektor → vektor := negate ∘ transform_fast e 6

#eval FNTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval FNTS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval FNTT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval FNTT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]


theorem transform_fast_correct : transform = transform_fast := by
  --ext t ω x j
  apply funext
  intro t
  induction' t with n ih
  · ext ω x j
    have j_zero : j = 0
    · cases' j with v proo
      have value_zero : v = 0
      · exact Iff.mp Nat.lt_one_iff proo
      exact Fin.ext value_zero
    rw [j_zero]
    unfold transform transform_fast dotProduct
    simp
  ext ω x j
  unfold transform_fast
  rw [←ih]
  sorry
