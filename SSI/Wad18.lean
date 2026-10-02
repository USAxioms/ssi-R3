/-!
# WAD-18 deterministic normative arithmetic (Standard III, sketch)

Integer fixed-point with scale `10^18`.  Every operation is total and returns
`Option Wad`; invalid arithmetic (overflow, underflow, division by zero)
yields `none`, which is non-permissive.
-/

namespace SSI

structure Wad where
  raw : Int
  deriving DecidableEq, Repr

namespace Wad

def scale : Int := 10 ^ 18
def maxRaw : Int := 2 ^ 255 - 1
def minRaw : Int := -(2 ^ 255)

/-- Range-checked constructor. -/
def mk? (z : Int) : Option Wad :=
  if minRaw ≤ z ∧ z ≤ maxRaw then some ⟨z⟩ else none

def add (a b : Wad) : Option Wad := mk? (a.raw + b.raw)

def sub (a b : Wad) : Option Wad := mk? (a.raw - b.raw)

def mul (a b : Wad) : Option Wad := mk? ((a.raw * b.raw) / scale)

def div (a b : Wad) : Option Wad :=
  if b.raw = 0 then none else mk? ((a.raw * scale) / b.raw)

theorem mk?_of_in_range {z : Int} (h : minRaw ≤ z ∧ z ≤ maxRaw) :
    mk? z = some ⟨z⟩ := by
  unfold mk?
  exact if_pos h

theorem mk?_of_gt_max {z : Int} (h : maxRaw < z) : mk? z = none := by
  have hn : ¬ (minRaw ≤ z ∧ z ≤ maxRaw) := fun hc => by omega
  unfold mk?
  exact if_neg hn

theorem mk?_of_lt_min {z : Int} (h : z < minRaw) : mk? z = none := by
  have hn : ¬ (minRaw ≤ z ∧ z ≤ maxRaw) := fun hc => by omega
  unfold mk?
  exact if_neg hn

theorem div_zero (a : Wad) : div a ⟨0⟩ = none := by
  simp [div]

theorem add_comm' (a b : Wad) : Wad.add a b = Wad.add b a := by
  unfold Wad.add
  rw [Int.add_comm]

end Wad

/-- Any invalid (`none`) arithmetic result yields a non-permissive verdict. -/
def verdictOf (r : Option Wad) (p : Wad → Bool) : Bool :=
  match r with
  | none => false
  | some w => p w

theorem invalid_arith_nonpermissive (p : Wad → Bool) : verdictOf none p = false := rfl

theorem div_zero_nonpermissive (a : Wad) (p : Wad → Bool) :
    verdictOf (Wad.div a ⟨0⟩) p = false := by
  simp [Wad.div_zero, verdictOf]

end SSI
