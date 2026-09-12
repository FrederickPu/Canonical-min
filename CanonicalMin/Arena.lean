import CanonicalMin

open Lean Meta

namespace CanonicalMin.Arena

private def config : Canonical.CanonicalConfig := {
  simp := false
  monomorphize := false
  destruct := false
}

/-- Run CanonicalLean's existing term and type translations in one shared context. -/
private def toCanonicalJudgment (value type : Expr) : MetaM (Canonical.Term × Canonical.Typ) := do
  let arity ← Canonical.typeArity type
  let translate : Canonical.ToCanonicalM (Canonical.Term × Canonical.Typ) := do
    let typ ← Canonical.toTyp type
    let term ← Canonical.toTerm value type arity.params.toList
    let definitions := (← get).definitions.toList.toArray.map fun (name, defn) =>
      ({ name, rules := defn.rules }, defn.type.toOption)
    Monomorphize.finalizeMonos
    let typ := removeTypeInType { typ with
      lets := definitions.map Prod.fst ++ typ.lets
      letTypes := definitions.map Prod.snd ++ typ.letTypes }
    return ({ term with lets := typ.lets }, typ)
  (((translate.run {
    arities := {}
    config
    structures := #[]
  }).run' {}).run' {
    globalFVars := {}
    constNames := .ofList [``OfNat.ofNat]
  })

private def runJudgment (term : Canonical.Term) (typ : Canonical.Typ) : Bool :=
  let ((term, typ), state) := (do
    let typ ← typ.toType
    let term ← term.toTerm
    pure (Term.mk term [], Typ.mk typ [])).run {}
  match ((check term typ).run (0, #[])).run state.assignments with
  | some (_, _, constraints) => constraints.isEmpty
  | none => false

def checkExpr (value type : Expr) : MetaM Bool := do
  let (term, typ) ← toCanonicalJudgment value type
  return runJudgment term typ

end CanonicalMin.Arena
