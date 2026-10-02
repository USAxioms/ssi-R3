/-!
# SSI lifecycle
`DEFINE → SPECIFY → AUTHORIZE → VERIFY → PERMIT → EXECUTE → VERIFY SUCCESSOR → COMMIT`
with failure states `REJECT, DEFER, SAFE_STOP, REVALIDATE, REVOKE`.
-/

namespace SSI

inductive Stage where
  | define
  | specify
  | authorize
  | verify
  | permit
  | execute
  | verifySuccessor
  | commit
  | reject
  | deferred
  | safeStop
  | revalidate
  | revoke
  deriving DecidableEq, Repr

def Stage.isFailure : Stage → Bool
  | .reject => true
  | .deferred => true
  | .safeStop => true
  | .revalidate => true
  | .revoke => true
  | _ => false

theorem commit_not_failure : Stage.commit.isFailure = false := rfl

theorem reject_is_failure : Stage.reject.isFailure = true := rfl

end SSI
