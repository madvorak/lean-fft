import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Order

namespace Matrix

def vektor : Type := Fin 4 → ZMod 5

def NNT (x : vektor) : vektor :=
![1 * x 0 + 1 * x 1 + 1 * x 2 + 1 * x 3,
  1 * x 0 + 2 * x 1 + 4 * x 2 + 3 * x 3,
  1 * x 0 + 4 * x 1 + 1 * x 2 + 4 * x 3,
  1 * x 0 + 3 * x 1 + 4 * x 2 + 2 * x 3]

def NNS (x : vektor) : vektor :=
![1 * x 0 + 1 * x 1 + 1 * x 2 + 1 * x 3,
  1 * x 0 + 3 * x 1 + 4 * x 2 + 2 * x 3,
  1 * x 0 + 4 * x 1 + 1 * x 2 + 4 * x 3,
  1 * x 0 + 2 * x 1 + 4 * x 2 + 3 * x 3]

#eval NNT $ NNS ![1, 1, 4, 4]
#eval NNS $ NNT ![0, 3, 1, 0]

def NT (ω : ZMod 5) (x : vektor) : vektor :=
fun i => x 0 + ω ^ (i.val) * x 1 + ω ^ (2 * i.val) * x 2 + ω ^ (3 * i.val) * x 3

def NN (ω : ZMod 5) (x : vektor) : vektor :=
fun i => dotProduct x (fun j => ω ^ (j.val*i.val))

def NNT' := NN 2
def NNS' := NN 3

#eval NNT  ![0, 3, 1, 0]
#eval NNT' ![0, 3, 1, 0]
#eval NNS  ![0, 3, 1, 0]
#eval NNS' ![0, 3, 1, 0]
