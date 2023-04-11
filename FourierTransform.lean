import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Complex.Basic

namespace Matrix

def x : (Fin 3) → ℚ := ![2, 3, -1]
def y : (Fin 3) → ℚ := ![5, 3, 2]
#eval dotProduct x y

def c : ℂ := 9
