import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

namespace Matrix


def e : ℕ := 4
def M : ℕ := 2^e + 1
def vektor : Type := Fin (2^e) → ZMod M


def transform (n : ℕ) (ω : ZMod M) (x : Fin n → ZMod M) : (Fin n → ZMod M) :=
fun (i : Fin n) => dotProduct (fun (j : Fin n) => ω ^ ((i : ℕ) * (j : ℕ))) x

def NNS : vektor → vektor := transform (2^e) 3

def negate (x : vektor) : vektor :=
fun i => - (x i)

def NNT : vektor → vektor := negate ∘ transform (2^e) 6

#eval NNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval NNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval NNT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval NNT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]


lemma two_mul_two_pow_pred {n : ℕ} (npos : n > 0) : 2 * 2 ^ (n-1) = 2 ^ n := by
  let m := n - 1
  have hm : n = m + 1
  · exact Iff.mp (tsub_eq_iff_eq_add_of_le npos) rfl
  convert_to 2 * 2 ^ m = 2 ^ (m+1)
  · rw [hm]
  exact Eq.symm (pow_succ'' m 2)

lemma index_ok {t : ℕ} (tpos : t > 0) (k : Fin (2 ^ (t-1))) : 2 * (k : ℕ) + 1 < 2 ^ t := by
  show 2 * (k : ℕ) + 2 ≤ 2 ^ t
  have hk : 2 * ((k : ℕ) + 1) ≤ 2 * (2 ^ (t-1))
  · apply LinearOrderedCommMonoid.mul_le_mul_left
    exact Fin.is_lt k
  rwa [mul_add, mul_one, two_mul_two_pow_pred tpos] at hk

def splitter {t : ℕ} (tpos : t > 0) (x : Fin (2 ^ t) → ZMod M) :
  (Fin (2 ^ (t-1)) → ZMod M) × (Fin (2 ^ (t-1)) → ZMod M) :=
Prod.mk
  (fun (k : Fin (2 ^ (t-1))) => x ⟨2 * (k : ℕ), Nat.lt_of_succ_lt (index_ok tpos k)⟩)
  (fun (k : Fin (2 ^ (t-1))) => x ⟨2 * (k : ℕ) + 1, index_ok tpos k⟩)

partial def transform_fast (t : ℕ) (ω : ZMod M) (x : Fin (2^t) → ZMod M) : Fin (2^t) → ZMod M :=
dite (t = 0)
  (fun _ => x)
  (fun ht =>
    let p := splitter (Iff.mpr zero_lt_iff ht) x
    let a := transform_fast (t - 1) (ω * ω) p.1
    let b := transform_fast (t - 1) (ω * ω) p.2
    fun (i : Fin (2^t)) =>
      let j : ℕ := i
      dite ((j : ℕ) < 2 ^ (t-1))
        (fun hj =>
          let J : Fin (2 ^ (t-1)) := ⟨j, hj⟩
          a J + ω ^ j * b J)
        (fun hj =>
          let j' : ℕ := j - 2 ^ (t-1)
          let J' : Fin (2 ^ (t-1)) := ⟨j', by {
            show j - 2 ^ (t-1) < 2 ^ (t-1)
            have hh : j < 2 ^ (t-1) + 2 ^ (t-1)
            · convert_to j < 2 * 2 ^ (t-1)
              · ring
              rw [two_mul_two_pow_pred (Iff.mpr zero_lt_iff ht)]
              exact Fin.is_lt i
            push_neg at hj
            rwa [←tsub_lt_iff_right hj] at hh
          }⟩
          a J' - ω ^ j' * b J')
  )

def FNNS : vektor → vektor := transform_fast e 3
def FNNT : vektor → vektor := negate ∘ transform_fast e 6

#eval FNNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 5, 7, 7, 7, 0, 0, 9]
#eval FNNS ![4, 4, 4, 1, 1, 5, 5, 5, 5, 7, 7, 7, 7, 0, 0, 9]
#eval FNNT ![1, 6, 8, 10, 16, 15, 14, 6, 14, 0, 14, 8, 3, 3, 2, 12]
#eval FNNT ![3, 0, 9, 7, 8, 5, 10, 1, 12, 6, 13, 11, 11, 13, 6, 0]
