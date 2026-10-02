/-!
# Provenance chain

`P_t = Hash(P_{t-1} ‖ enc(q_t) ‖ enc(u_t) ‖ enc(e_t))`.

The hash is abstract.  A chain gives evidence *continuity*; it does not
establish truth of the recorded propositions (`Integrity ≠ Truth`).
-/

namespace SSI

section
variable {α : Type}

def chain (H : α → α → α → α → α) (p0 : α) (steps : List (α × α × α)) : α :=
  steps.foldl (fun p s => H p s.1 s.2.1 s.2.2) p0

theorem chain_nil (H : α → α → α → α → α) (p0 : α) : chain H p0 [] = p0 := rfl

/-- Append-only: extending the record extends the chain from the old head. -/
theorem chain_append (H : α → α → α → α → α) (p0 : α)
    (l1 l2 : List (α × α × α)) :
    chain H p0 (l1 ++ l2) = chain H (chain H p0 l1) l2 := by
  simp [chain, List.foldl_append]

end

end SSI
