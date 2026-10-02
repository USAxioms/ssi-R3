import SSI.Verdict

/-!
# The Permit predicate and fail-closed behaviour

Every term of the canonical Permit predicate is a gate.  `PermitProof g` is
the conjunction of all fourteen gates; a single failed gate yields `¬ Permit`.
-/

namespace SSI

/-- Evaluated gate values for a state/action pair `(q, u)`. -/
structure Gates where
  typeOK : Bool
  actionWellTyped : Bool
  cslValid : Bool
  authorized : Bool
  capabilityValid : Bool
  safetyInv : Bool
  actionSafe : Bool
  verification : Verdict
  evidenceValid : Bool
  deploymentBound : Bool
  withinScope : Bool
  current : Bool
  fresh : Bool
  revoked : Bool
  deriving Repr

/-- `Permit(q,u)`: all gates hold, verification is `PASS`, and not revoked. -/
structure PermitProof (g : Gates) : Prop where
  typeOK : g.typeOK = true
  actionWellTyped : g.actionWellTyped = true
  cslValid : g.cslValid = true
  authorized : g.authorized = true
  capabilityValid : g.capabilityValid = true
  safetyInv : g.safetyInv = true
  actionSafe : g.actionSafe = true
  verification : g.verification = Verdict.pass
  evidenceValid : g.evidenceValid = true
  deploymentBound : g.deploymentBound = true
  withinScope : g.withinScope = true
  current : g.current = true
  fresh : g.fresh = true
  revoked : g.revoked = false

theorem bool_clash {b : Bool} (h1 : b = true) (h2 : b = false) : False := by
  rw [h1] at h2
  cases h2

/-! ## Fail-closed: any failed gate blocks Permit -/

theorem not_permit_of_ill_typed {g : Gates} (h : g.typeOK = false) :
    ¬ PermitProof g := fun p => bool_clash p.typeOK h

theorem not_permit_of_untyped_action {g : Gates} (h : g.actionWellTyped = false) :
    ¬ PermitProof g := fun p => bool_clash p.actionWellTyped h

theorem not_permit_of_invalid_csl {g : Gates} (h : g.cslValid = false) :
    ¬ PermitProof g := fun p => bool_clash p.cslValid h

theorem not_permit_of_unauthorized {g : Gates} (h : g.authorized = false) :
    ¬ PermitProof g := fun p => bool_clash p.authorized h

theorem not_permit_of_capability_violation {g : Gates} (h : g.capabilityValid = false) :
    ¬ PermitProof g := fun p => bool_clash p.capabilityValid h

theorem not_permit_of_safety_violation {g : Gates} (h : g.safetyInv = false) :
    ¬ PermitProof g := fun p => bool_clash p.safetyInv h

theorem not_permit_of_unsafe_action {g : Gates} (h : g.actionSafe = false) :
    ¬ PermitProof g := fun p => bool_clash p.actionSafe h

theorem not_permit_of_unknown {g : Gates} (h : g.verification = Verdict.unknown) :
    ¬ PermitProof g := by
  intro p
  have hp := p.verification
  rw [h] at hp
  exact Verdict.unknown_ne_pass hp

theorem not_permit_of_failed_verification {g : Gates} (h : g.verification = Verdict.fail) :
    ¬ PermitProof g := by
  intro p
  have hp := p.verification
  rw [h] at hp
  exact Verdict.fail_ne_pass hp

theorem not_permit_of_invalid_evidence {g : Gates} (h : g.evidenceValid = false) :
    ¬ PermitProof g := fun p => bool_clash p.evidenceValid h

theorem not_permit_of_unbound_deployment {g : Gates} (h : g.deploymentBound = false) :
    ¬ PermitProof g := fun p => bool_clash p.deploymentBound h

theorem not_permit_of_out_of_scope {g : Gates} (h : g.withinScope = false) :
    ¬ PermitProof g := fun p => bool_clash p.withinScope h

theorem not_permit_of_not_current {g : Gates} (h : g.current = false) :
    ¬ PermitProof g := fun p => bool_clash p.current h

theorem not_permit_of_stale {g : Gates} (h : g.fresh = false) :
    ¬ PermitProof g := fun p => bool_clash p.fresh h

theorem not_permit_of_revoked {g : Gates} (h : g.revoked = true) :
    ¬ PermitProof g := fun p => bool_clash h p.revoked

/-- Permit requires both authorization and action safety. -/
theorem permit_requires_authorized_and_safe {g : Gates} (p : PermitProof g) :
    g.authorized = true ∧ g.actionSafe = true := ⟨p.authorized, p.actionSafe⟩

/-! ## Authority and safety are independent -/

/-- A gate assignment in which every gate is satisfied. -/
def allGood : Gates where
  typeOK := true
  actionWellTyped := true
  cslValid := true
  authorized := true
  capabilityValid := true
  safetyInv := true
  actionSafe := true
  verification := Verdict.pass
  evidenceValid := true
  deploymentBound := true
  withinScope := true
  current := true
  fresh := true
  revoked := false

theorem allGood_permit : PermitProof allGood where
  typeOK := rfl
  actionWellTyped := rfl
  cslValid := rfl
  authorized := rfl
  capabilityValid := rfl
  safetyInv := rfl
  actionSafe := rfl
  verification := rfl
  evidenceValid := rfl
  deploymentBound := rfl
  withinScope := rfl
  current := rfl
  fresh := rfl
  revoked := rfl

/-- `Authorized ⇏ Permit` (and hence `Authorized ⇏ Safe`). -/
theorem authorized_not_sufficient :
    ∃ g : Gates, g.authorized = true ∧ ¬ PermitProof g :=
  ⟨{ allGood with actionSafe := false }, rfl, not_permit_of_unsafe_action rfl⟩

/-- `Safe ⇏ Permit` (and hence `Safe ⇏ Authorized`). -/
theorem safe_not_sufficient :
    ∃ g : Gates, g.actionSafe = true ∧ ¬ PermitProof g :=
  ⟨{ allGood with authorized := false }, rfl, not_permit_of_unauthorized rfl⟩

/-- `Verification = PASS ⇏ Permit`: verification is not authority. -/
theorem verification_not_authority :
    ∃ g : Gates, g.verification = Verdict.pass ∧ ¬ PermitProof g :=
  ⟨{ allGood with authorized := false }, rfl, not_permit_of_unauthorized rfl⟩

end SSI
