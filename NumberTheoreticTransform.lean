import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace Matrix


def size : ℕ := 16
def vektor : Type := Fin size → Fin size.succ


def transform (ω : ZMod size.succ) (x : vektor) : vektor :=
fun i => dotProduct (fun j => ω ^ (i.val * j.val)) x

def NNS : vektor → vektor := transform 3

def negate (x : vektor) : vektor :=
fun i => - (x i)

def NNT : vektor → vektor := negate ∘ transform 6


#eval NNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval NNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval NNT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval NNT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
