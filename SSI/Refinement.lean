/-!
# Russell Recursive Refinement (R³): adoption and fixed points
-/

namespace SSI

/-- `Adopt(q,q')`: all six adoption conditions. -/
structure Adopt
    (KernelEqual SafetyProofValid AuthorizationValid
     DeploymentValid NonRegression CapabilityDisclosureValid : Prop) : Prop where
  kernelEqual : KernelEqual
  safetyProofValid : SafetyProofValid
  authorizationValid : AuthorizationValid
  deploymentValid : DeploymentValid
  nonRegression : NonRegression
  capabilityDisclosureValid : CapabilityDisclosureValid

section
variable {K S A D N C : Prop}

/-- R³ may not silently redefine safety: a changed kernel blocks adoption. -/
theorem no_adopt_if_kernel_changed (h : ¬ K) : ¬ Adopt K S A D N C :=
  fun a => h a.kernelEqual

theorem no_adopt_without_safety_proof (h : ¬ S) : ¬ Adopt K S A D N C :=
  fun a => h a.safetyProofValid

theorem no_adopt_without_authorization (h : ¬ A) : ¬ Adopt K S A D N C :=
  fun a => h a.authorizationValid

theorem no_adopt_on_regression (h : ¬ N) : ¬ Adopt K S A D N C :=
  fun a => h a.nonRegression

theorem no_adopt_without_disclosure (h : ¬ C) : ¬ Adopt K S A D N C :=
  fun a => h a.capabilityDisclosureValid

end

/-- Appearing superior is not sufficient for adoption. -/
theorem superior_not_sufficient :
    ¬ (∀ (Superior K S A D N C : Prop), Superior → Adopt K S A D N C) := by
  intro h
  exact (h True False True True True True True trivial).kernelEqual

/-- A fixed point of R³ need not be safe. -/
theorem fixed_point_not_safe :
    ∃ (Q : Type) (R : Q → Q) (safe : Q → Prop) (q : Q), R q = q ∧ ¬ safe q :=
  ⟨Bool, id, fun b => b = true, false, rfl, by simp⟩

/-- Safety does not imply the existence of an R³ fixed point. -/
theorem safe_not_fixed_point :
    ∃ (Q : Type) (R : Q → Q) (safe : Q → Prop),
      (∃ q, safe q) ∧ ∀ q, R q ≠ q :=
  ⟨Bool, fun b => !b, fun _ => True, ⟨true, trivial⟩, by decide⟩

end SSI
