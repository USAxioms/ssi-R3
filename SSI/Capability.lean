/-!
# Capability non-escalation (Standard I)

`Cap(q_{t+1}) ⊆ Cap_authorized(q_t)`: self-acquired capability is never
self-granted authority.
-/

namespace SSI

/-- Subset relation on capability predicates. -/
def Subcap {C : Type} (a b : C → Prop) : Prop := ∀ c, a c → b c

theorem Subcap.refl {C : Type} (a : C → Prop) : Subcap a a := fun _ h => h

theorem Subcap.trans {C : Type} {a b c : C → Prop}
    (h1 : Subcap a b) (h2 : Subcap b c) : Subcap a c :=
  fun x hx => h2 x (h1 x hx)

structure CapTransition (Q C : Type) where
  cap : Q → C → Prop
  authorizedCap : Q → C → Prop
  next : Q → Q
  nonEscalation : ∀ q, Subcap (cap (next q)) (authorizedCap q)

theorem no_self_granted {Q C : Type} (T : CapTransition Q C) (q : Q) (c : C)
    (h : T.cap (T.next q) c) : T.authorizedCap q c :=
  T.nonEscalation q c h

end SSI
