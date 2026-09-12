import CanonicalMin.Arena

example : A → A := by canonical_min

axiom ArenaTest.A : Prop

def ArenaTest.good : ArenaTest.A → ArenaTest.A := fun value => value

def ArenaTest.bad : ArenaTest.A → Prop := fun _ => ArenaTest.A

run_meta do
  let good ← Lean.getConstInfo ``ArenaTest.good
  let bad ← Lean.getConstInfo ``ArenaTest.bad
  unless ← CanonicalMin.Arena.checkExpr good.value! good.type do
    throwError "canonical-min arena rejected a valid identity function"
  if ← CanonicalMin.Arena.checkExpr bad.value! good.type then
    throwError "canonical-min arena accepted an ill-typed function"
