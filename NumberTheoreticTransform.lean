import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

namespace Matrix


def size : ℕ := 16
def M : ℕ := size + 1
def vektor : Type := Fin size → ZMod M


def transform (n : ℕ) (ω : ZMod M) (x : Fin n → ZMod M) : (Fin n → ZMod M) :=
fun (i : Fin n) => dotProduct (fun (j : Fin n) => ω ^ ((i : ℕ) * (j : ℕ))) x

def NNS : vektor → vektor := transform size 3

def negate (x : vektor) : vektor :=
fun i => - (x i)

def NNT : vektor → vektor := negate ∘ transform size 6
/-
#eval NNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval NNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval NNT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval NNT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
-/

lemma index_ok {n : ℕ} (k : Fin (n / 2)) : 2 * (k : ℕ) + 1 < n := by
  have hk : 2 * ((k : ℕ) + 1) ≤ 2 * ((n : ℕ) / 2)
  · apply LinearOrderedCommMonoid.mul_le_mul_left
    exact Fin.is_lt k
  show 2 * (k : ℕ) + 2 ≤ n
  rw [mul_add, mul_one] at hk
  have hn : 2 * (n / 2) ≤ n
  · exact Nat.mul_div_le n 2
  exact LE.le.trans' hn hk

def splitter (n : ℕ) (x : Fin n → ZMod M) : (Fin (n/2) → ZMod M) × (Fin (n/2) → ZMod M) :=
Prod.mk
  (fun (k : Fin (n/2)) => x ⟨2 * (k : ℕ), Nat.lt_of_succ_lt (index_ok k)⟩)
  (fun (k : Fin (n/2)) => x ⟨2 * (k : ℕ) + 1, index_ok k⟩)

partial def transform_fast (n : ℕ) (ω : ZMod M) (x : Fin n → ZMod M) : Fin n → ZMod M :=
if n ≤ 1 then x else
let p := splitter n x
let a := transform_fast (n / 2) (ω * ω) p.1
let b := transform_fast (n / 2) (ω * ω) p.2
fun (i : Fin n) => dite (i < n / 2)
                   (fun hi =>
                    let I : Fin (n / 2) := ⟨i, hi⟩
                    a I + ω ^ (i : ℕ) * b I)
                   (fun _ =>
                    let j : ℕ := (i : ℕ) - (n / 2)
                    let J : Fin (n / 2) := ⟨j, by { 
                      have hh : i < n
                      · exact Fin.is_lt i
                      -- TODO we need that `n` is even
                      sorry
                     }⟩
                    a J - ω ^ j * b J)

def FNNS : vektor → vektor := transform_fast size 3
def FNNT : vektor → vektor := negate ∘ transform_fast size 6

#eval FNNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval FNNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval FNNT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval FNNT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
