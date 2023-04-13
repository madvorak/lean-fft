import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases

namespace Matrix


--  level n = 2 ^ n
def level : ℕ -> ℕ
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


lemma index_ok {t : ℕ} (i : Fin (level t)) : 2 * (i : ℕ) + 1 < level t.succ := by
  unfold level
  have hi := Fin.is_lt i
  linarith

def splitter {t : ℕ} (x : Fin (level (t+1)) → ZMod M) :
  (Fin (level t) → ZMod M) × (Fin (level t) → ZMod M) :=
Prod.mk
  (fun (i : Fin (level t)) => x ⟨2 * (i : ℕ), Nat.lt_of_succ_lt (index_ok i)⟩)
  (fun (i : Fin (level t)) => x ⟨2 * (i : ℕ) + 1, index_ok i⟩)

def transform_fast (t : ℕ) (ω : ZMod M) (x : Fin (level t) → ZMod M) : (Fin (level t) → ZMod M) :=
match t with
| 0   => x
| n+1 =>
  let p := splitter x
  let a := transform_fast n (ω * ω) p.1
  let b := transform_fast n (ω * ω) p.2
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

theorem transform_fast_correct : transform = transform_fast := by
  --ext t ω x j
  apply funext
  intro t
  induction' t with n ih
  · ext ω x j
    have jz : j = (0 : Fin 1)
    · exact Fin.ext (Fin.coe_fin_one j)
    rw [jz]
    unfold transform transform_fast dotProduct Finset.univ Fintype.elems Fin.fintype
    simp
    rfl
  ext ω x j
  unfold transform_fast
  rw [←ih]
  by_cases hj : j.val < level n
  · let J : Fin (level n) := ⟨j.val, hj⟩
    --let c := Fin.castAdd (level n) j
    convert_to transform (Nat.succ n) ω x j =
      let p := splitter x
      let a := transform n (ω * ω) p.fst
      let b := transform n (ω * ω) p.snd
      (fun j => a j + ω ^ j.val * b j) J
    · simp --simp_rw [←Fin.append_left]
      sorry
    show transform (Nat.succ n) ω x j =
      let p := splitter x
      transform n (ω * ω) p.fst J + ω ^ j.val * transform n (ω * ω) p.snd J
    sorry
  · sorry
