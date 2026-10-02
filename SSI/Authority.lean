/-!
# Authorization, authority sources, temporal validity and revocation
-/

namespace SSI

/-- Candidate sources of authority. -/
inductive AuthSource where
  | signedDirective
  | modelConfidence
  | modelOutput
  | systemCapability
  | priorExecution
  | historicalSuccess
  | selfDeclared
  deriving DecidableEq, Repr

/-- Only a validly signed human directive can ground authority. -/
def AuthSource.grantsAuthority : AuthSource → Bool
  | .signedDirective => true
  | _ => false

theorem only_signed_directive_grants_authority (s : AuthSource)
    (h : s.grantsAuthority = true) : s = AuthSource.signedDirective := by
  cases s <;> simp_all [AuthSource.grantsAuthority]

/-- A signed authorization directive (cryptographic signature abstracted away). -/
structure Directive where
  issuer : String
  scope : String
  purpose : String
  riskLimit : Nat
  issueTime : Nat
  expiryTime : Nat
  nonce : Nat
  revocationEpoch : Nat
  deriving Repr

/-- Validity at time `now` under current revocation epoch `epoch`. -/
def Directive.ValidAt (d : Directive) (now epoch : Nat) : Prop :=
  d.issueTime ≤ now ∧ now < d.expiryTime ∧ d.revocationEpoch = epoch

theorem expired_invalid {d : Directive} {now epoch : Nat}
    (h : d.expiryTime ≤ now) : ¬ d.ValidAt now epoch := by
  intro v
  unfold Directive.ValidAt at v
  omega

theorem not_yet_issued_invalid {d : Directive} {now epoch : Nat}
    (h : now < d.issueTime) : ¬ d.ValidAt now epoch := by
  intro v
  unfold Directive.ValidAt at v
  omega

/-- Revocation-epoch change dominates any earlier authorization. -/
theorem revoked_invalid {d : Directive} {now epoch : Nat}
    (h : d.revocationEpoch ≠ epoch) : ¬ d.ValidAt now epoch := by
  intro v
  unfold Directive.ValidAt at v
  omega

end SSI
