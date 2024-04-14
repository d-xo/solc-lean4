import Aesop
import Lean
import Std.Data.HashMap
import Init.Data.Nat
import Init.Data.Nat.Lemmas
import Init.Data.BitVec
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Mathlib.Data.Nat.Bits
import Mathlib.Data.PNat.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Computability.Encoding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Std.Data.Array.Lemmas

open Lean BitVec Vector Nat


-- padRight --


/--
dfoldr is a variant of foldr that can accomodate
-/
def dfoldr {α : Type}
           : {sz : ℕ}
           → (tp : ℕ → Type)
           → (step : (idx : ℕ) → α → tp idx → tp (idx + 1))
           → (init : tp 0)
           → Vector α sz
           → tp sz
| 0, _, _, base, Vector.nil => base
| n + 1, p, step, base, v => step n (head v) (dfoldr p step base (tail v))


-- padRight --


/--
padRight extends arr so that it's size is sz by appending val's
it is a noop if arr.size ≥ sz
-/
def padRight (arr : Array t) (sz : Nat) (val : t) : Array t :=
  if sz <= arr.size
  then arr
  else
    let padding := Array.mkArray (sz - Array.size arr) val
    Array.append arr padding

-- padRight is a noop if sz <= arr.size
theorem padRight_noop_sz_lt
  (h : sz ≤ arr.size)
  : padRight arr sz val = arr := by
    unfold padRight
    simp [*]

-- padRight expands to sz if arr.size < sz
theorem padRight_size_eq_sz
  (h : sz > arr.size)
  : (padRight arr sz val).size = sz := by
    unfold padRight
    simp [not_le_of_lt h]
    unfold Array.size; simp
    rw [←Nat.add_sub_assoc, add_sub_self_left]
    apply le_of_lt h

-- padRight arr sz val is never smaller than arr
theorem padRight_never_decreases_size
  : arr.size ≤ (padRight arr sz val).size := by
    unfold padRight
    by_cases hsz : sz ≤ arr.size
    · simp [hsz]
    · simp [hsz]
      unfold mkArray
      unfold Array.size
      simp

-- the size of the array returned by padRight is always ≥ sz
theorem padRight_sz_le
  : sz ≤ (padRight arr sz val).size := by
    unfold padRight
    by_cases hsz : sz ≤ arr.size
    · simp [hsz]
    · simp [hsz]
      unfold mkArray
      unfold Array.size
      simp
      rw [←Nat.add_sub_assoc, add_sub_self_left]
      apply gt_of_not_le at hsz
      have : sz = (padRight arr sz val).size := Eq.symm (padRight_size_eq_sz hsz)
      rw [this]
      apply padRight_never_decreases_size

-- arr is a prefix of padRight arr sz val
theorem padRight_only_appends
  (h₁ : i < arr.size)
  (h₂ : i < (padRight arr s v).size := lt_of_lt_of_le h₁ padRight_never_decreases_size)
  : arr[i]'h₁ = (padRight arr s v)[i]'h₂ := by
    unfold padRight
    simp
    by_cases hsz : s ≤ arr.size
    · simp [hsz]
    · simp [hsz]
      simp [Array.get_append_left h₁]

-- all elements past arr.size in the padded arrfer are val
theorem padRight_fills_vals
  (hsz : sz > arr.size)
  (hmin : arr.size ≤ i)
  (hmax : i < sz)
  (hidx : i < (padRight arr sz val).size
    := lt_of_lt_of_eq hmax (Eq.symm $ padRight_size_eq_sz hsz))
  : (padRight arr sz val)[i]'(hidx) = val := by
    unfold padRight
    simp [not_le_of_lt hsz]
    simp [Array.get_append_right hmin]


def Subarray.toVector (arr : Subarray t) : Vector t (arr.size) := Vector.ofFn (λ i => arr[i])


-- BitVec chunk and join --


def BitVec.join (bytes : Vector (BitVec b) sz) : BitVec (b * sz) :=
  BitVec.cast (mul_comm sz b) $ dfoldr
    (λ i => BitVec (i * b))
    (λ i val acc => BitVec.cast (by ring) (BitVec.append val acc))
    (BitVec.cast (by simp) BitVec.nil)
    bytes

def BitVec.chunk (chunk : ℕ+) (num : ℕ) (bv : BitVec (chunk * num)) : Vector (BitVec chunk) num :=
  Vector.ofFn (λ i =>
    let hi : ℕ := (chunk * num) - (chunk * i)
    let lo := hi - chunk
    have : 1 ≤ (chunk : Nat) := chunk.property
    have : chunk + (chunk * i : Nat) ≤ chunk * num := by
      rw [add_comm, ←mul_succ]; apply Nat.mul_le_mul_left; omega
    BitVec.cast (by omega) $ BitVec.extractLsb (hi - 1) lo bv
  )

theorem split_join_inverse (bs : Vector (BitVec b) sz) (i : Fin sz) (h: b > 0)
  : (BitVec.chunk ⟨b,h⟩ sz (BitVec.join bs))[i] = bs[i] := by
    induction sz with
    | zero => simp [Vector.eq_nil]; rfl
    | succ n hsz =>
      induction b with
      | zero => simp [getLsb_ge]
      | succ m hb =>
        unfold BitVec.chunk
        unfold BitVec.join
        simp_all
        unfold getElem
        unfold instGetElemVectorNatLtInstLTNat
        simp [Vector.get_ofFn]
        sorry
