# SSI-Lean4

A Lean 4 formalization of the structural core of **Safe Super Intelligence: Definition, Architecture, and Verification Standard v1.0** (M. A. Russell).

It uses only Lean core (no Mathlib), so builds are fast.

## Build

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build
```

## Module map

| Standard section | Lean module | What is proved |
|---|---|---|
| Layer 5 (verification states) | `SSI/Verdict.lean` | `UNKNOWN ≠ PASS`, `isPass ↔ = PASS` |
| Permit predicate, fail-closed, authority ≠ safety | `SSI/Gates.lean` | each failed gate ⇒ `¬Permit`; `Authorized ⇏ Permit`, `Safe ⇏ Permit`, `Verified ⇏ Permit` |
| SSI as conjunction | `SSI/Conditions.lean` | every component is necessary |
| Authorization, freshness, revocation | `SSI/Authority.lean` | only signed directives ground authority; expiry / revocation epoch invalidate |
| Capability non-escalation | `SSI/Capability.lean` | `Cap(q′) ⊆ Cap_authorized(q)` ⇒ no self-granted authority |
| WAD-18 | `SSI/Wad18.lean` | range-checked fixed point; invalid arithmetic is non-permissive |
| Provenance chain | `SSI/Provenance.lean` | append-only chain composition |
| R³ | `SSI/Refinement.lean` | `Adopt` conditions; fixed point ⇏ safe; safe ⇏ fixed point |
| Inductive safety, mediation, Central Theorem | `SSI/Transition.lean` | `reach_safe`, `no_permit_no_effect`, `central_theorem` |
| Lifecycle | `SSI/Lifecycle.lean` | stage / failure-state enumeration |

## Scope and honesty

The standard is *axiomatic and conditional*. `central_theorem` holds **because** the `GovernedSystem` structure bundles the standard's assumptions (initial safety, Permit-guarded safety-preserving transitions, complete mediation) as fields. The formalization checks that these assumptions compose correctly and that the fail-closed and independence properties follow; it does not prove that any real AI system satisfies them. Cryptographic signatures and hash functions are abstracted.

Add a `LICENSE` file of your choice before publishing.
