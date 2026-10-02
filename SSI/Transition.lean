import SSI.Gates

/-!
# Inductive safety, complete mediation, and the Central SSI Theorem

Two distinct transitions preserve the safety contract `C`: the execution
transition `δ` (guarded by Permit) and the refinement transition `R³`
(guarded by Adopt).  Their obligations are separate.
-/

namespace SSI

structure GovernedSystem (Q U : Type) where
  /-- `q ⊨ C` -/
  safe : Q → Prop
  initial : Q → Prop
  gates : Q → U → Gates
  /-- execution transition δ -/
  step : Q → U → Q
  adopt : Q → Q → Prop
  /-- refinement transition R³ -/
  refineStep : Q → Q
  /-- external effect -/
  effect : Q → U → Prop
  initial_safe : ∀ q, initial q → safe q
  step_preserves : ∀ q u, safe q → PermitProof (gates q u) → safe (step q u)
  refine_preserves : ∀ q q', safe q → adopt q q' → refineStep q = q' → safe q'
  /-- complete mediation: every effect requires Permit -/
  mediated : ∀ q u, effect q u → PermitProof (gates q u)

inductive Reach {Q U : Type} (S : GovernedSystem Q U) : Q → Prop where
  | start {q : Q} (h : S.initial q) : Reach S q
  | execute {q : Q} (u : U) (hr : Reach S q) (hp : PermitProof (S.gates q u)) :
      Reach S (S.step q u)
  | refined {q q' : Q} (hr : Reach S q) (ha : S.adopt q q')
      (he : S.refineStep q = q') : Reach S q'

/-- `∀ q ∈ Reach(Q₀), q ⊨ C`. -/
theorem reach_safe {Q U : Type} (S : GovernedSystem Q U) {q : Q}
    (h : Reach S q) : S.safe q := by
  induction h with
  | start hi => exact S.initial_safe _ hi
  | execute u hr hp ih => exact S.step_preserves _ u ih hp
  | refined hr ha he ih => exact S.refine_preserves _ _ ih ha he

/-- `Effect(u) ⇒ Permit(u)`. -/
theorem effect_requires_permit {Q U : Type} (S : GovernedSystem Q U) (q : Q) (u : U)
    (h : S.effect q u) : PermitProof (S.gates q u) :=
  S.mediated q u h

/-- Fail-closed at system level: `¬ Permit ⇒ ¬ Effect`. -/
theorem no_permit_no_effect {Q U : Type} (S : GovernedSystem Q U) (q : Q) (u : U)
    (h : ¬ PermitProof (S.gates q u)) : ¬ S.effect q u :=
  fun he => h (S.mediated q u he)

/-- `UNKNOWN` verification never yields an external effect. -/
theorem unknown_verification_no_effect {Q U : Type} (S : GovernedSystem Q U)
    (q : Q) (u : U) (h : (S.gates q u).verification = Verdict.unknown) :
    ¬ S.effect q u :=
  no_permit_no_effect S q u (not_permit_of_unknown h)

/-- Revoked authority never yields an external effect. -/
theorem revoked_no_effect {Q U : Type} (S : GovernedSystem Q U)
    (q : Q) (u : U) (h : (S.gates q u).revoked = true) :
    ¬ S.effect q u :=
  no_permit_no_effect S q u (not_permit_of_revoked h)

/-- **Central SSI Theorem** (under the declared structural assumptions):
every reachable state satisfies the contract, and every external effect at a
reachable state is permitted. -/
theorem central_theorem {Q U : Type} (S : GovernedSystem Q U) {q : Q}
    (h : Reach S q) :
    S.safe q ∧ ∀ u, S.effect q u → PermitProof (S.gates q u) :=
  ⟨reach_safe S h, fun u he => S.mediated q u he⟩

end SSI
