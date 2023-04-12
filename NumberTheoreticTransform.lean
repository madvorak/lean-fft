import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct

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

#eval NNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval NNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval NNT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval NNT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]


def splitter (n : ℕ) (x : Fin n → ZMod M) : (Fin (n/2) → ZMod M) × (Fin (n/2) → ZMod M) :=
Prod.mk
  (fun (k : Fin (n/2)) => x ⟨2 * (k : ℕ), (by {sorry})⟩)
  (fun (k : Fin (n/2)) => x ⟨2 * (k : ℕ) + 1, (by {sorry})⟩)

def transform_fast (n : ℕ) (ω : ZMod M) (x : Fin n → ZMod M) : Fin n → ZMod M :=
let p := splitter n x
let a := transform (n / 2) (ω * ω) p.1
let b := transform (n / 2) (ω * ω) p.2
fun (i : Fin n) => if i < n / 2
                   then a ⟨(i : ℕ), sorry⟩ + ω ^ (i : ℕ) * b ⟨(i : ℕ), sorry⟩
                   else a ⟨(i : ℕ), sorry⟩ - ω ^ ((i : ℕ) - (n / 2)) * b ⟨(i : ℕ), sorry⟩

def FNNS : vektor → vektor := transform_fast size 3
def FNNT : vektor → vektor := negate ∘ transform_fast size 6

#eval FNNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval FNNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval FNNT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval FNNT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
