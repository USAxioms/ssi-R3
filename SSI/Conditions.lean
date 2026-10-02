/-!
# SSI as a conjunction of conditions (Standard I, §5)

`SSI(q,u) ⇔ SI ∧ HG ∧ AUTH ∧ SAFE ∧ VER ∧ GOV ∧ CAP ∧ PROV ∧ DEP ∧ SCOPE ∧ CUR`.
No individual component is sufficient; each is necessary.
-/

namespace SSI

structure SSIConditions
    (SI HG AUTH SAFE VER GOV CAP PROV DEP SCOPE CUR : Prop) : Prop where
  si : SI
  hg : HG
  auth : AUTH
  safe : SAFE
  ver : VER
  gov : GOV
  cap : CAP
  prov : PROV
  dep : DEP
  scope : SCOPE
  cur : CUR

section
variable {SI HG AUTH SAFE VER GOV CAP PROV DEP SCOPE CUR : Prop}

theorem fails_without_auth (h : ¬ AUTH) :
    ¬ SSIConditions SI HG AUTH SAFE VER GOV CAP PROV DEP SCOPE CUR :=
  fun s => h s.auth

theorem fails_without_safe (h : ¬ SAFE) :
    ¬ SSIConditions SI HG AUTH SAFE VER GOV CAP PROV DEP SCOPE CUR :=
  fun s => h s.safe

theorem fails_without_ver (h : ¬ VER) :
    ¬ SSIConditions SI HG AUTH SAFE VER GOV CAP PROV DEP SCOPE CUR :=
  fun s => h s.ver

theorem fails_without_cur (h : ¬ CUR) :
    ¬ SSIConditions SI HG AUTH SAFE VER GOV CAP PROV DEP SCOPE CUR :=
  fun s => h s.cur

/-- `SI ⇏ SSI`: superintelligence alone is not Safe Super Intelligence. -/
theorem si_not_sufficient (hs : SI) (h : ¬ AUTH) :
    SI ∧ ¬ SSIConditions SI HG AUTH SAFE VER GOV CAP PROV DEP SCOPE CUR :=
  ⟨hs, fails_without_auth h⟩

end

end SSI
