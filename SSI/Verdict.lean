/-!
# Verification verdicts (Standard I, Layer 5)

The minimum verification state space is `{PASS, FAIL, UNKNOWN}` with
`UNKNOWN ≠ PASS`.  The verifier never converts absence of evidence into
evidence of satisfaction.
-/

namespace SSI

inductive Verdict where
  | pass
  | fail
  | unknown
  deriving DecidableEq, Repr

namespace Verdict

def isPass : Verdict → Bool
  | .pass => true
  | .fail => false
  | .unknown => false

theorem unknown_ne_pass : Verdict.unknown ≠ Verdict.pass := by decide

theorem fail_ne_pass : Verdict.fail ≠ Verdict.pass := by decide

theorem isPass_iff (v : Verdict) : v.isPass = true ↔ v = Verdict.pass := by
  cases v <;> simp [isPass]

end Verdict

end SSI
