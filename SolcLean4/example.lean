import Mathlib.Data.Vector
open Vector
open Nat

def dfoldr {α : Type}
           : {sz : ℕ}
           → (tp : ℕ → Type)
           → (step : (idx : ℕ) → α → tp idx → tp (idx + 1))
           → (init : tp 0)
           → Vector α sz
           → tp sz
| 0, _, _, base, Vector.nil => base
| n + 1, p, step, base, v => step n (head v) (dfoldr p step base (tail v))


def joinBytes (bytes : Vector (BitVec b) sz) : BitVec (sz * b) :=
  have cast_thm {i} : b + i * b = (i + 1) * b := by rw [add_comm, mul_comm, ←mul_succ, mul_comm]
  dfoldr
    (λ i => BitVec (i * b))
    (λ i val acc => BitVec.cast cast_thm (BitVec.append val acc))
    (BitVec.cast (by simp) BitVec.nil)
    bytes
