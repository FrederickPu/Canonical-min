import Lean
import CanonicalMin.Search
open Lean PrettyPrinter Delaborator

/-!
`term{ fun A a ↦ a }` is a `RawTerm` and `type{ (A : U) → (a : A) → A }` is
a `RawTyp`. These are terms and types with named variables, which are
converted to an `MVar` or `TypeMVar` by allocating and assigning metavariables.
-/

/-- The term `fun params ↦ head args`. -/
structure RawTerm where
  params: Array String
  head: String
  args: Array RawTerm
deriving Inhabited

/-- The type `(inputs) → output`, where the `output` has no `params`. -/
structure RawTyp where
  inputs: Array (String × RawTyp)
  output: RawTerm
deriving Inhabited

/-- `ctx` is the names in scope, and `names` are bound together with the `params`. -/
partial def RawTerm.toMVar (t : RawTerm) (ctx : List (Array String) := [])
    (names : Array String := #[]) : CanonicalM MVar := do
  let names := names ++ t.params
  let ctx := if names.isEmpty then ctx else names :: ctx
  let (debruijn, index) := (ctx.zipIdx.findSome? fun (block, debruijn) =>
    (block.idxOf? t.head).map (debruijn, ·)).get!
  let assn : Assignment := ⟨debruijn, index, ← t.args.mapM (·.toMVar ctx)⟩
  modifyGet fun state => (⟨state.assignments.size, [], names⟩, {
    assignments := state.assignments.push assn
    constraints := state.constraints.push #[]
  })

partial def RawTyp.toTypeMVar (t : RawTyp) (ctx : List (Array String) := []) :
    CanonicalM TypeMVar := do
  let names := t.inputs.map (·.1)
  let inputs ← t.inputs.mapM (·.2.toTypeMVar (if names.isEmpty then ctx else names :: ctx))
  return ⟨inputs, ← t.output.toMVar ctx names⟩

instance : Coe RawTerm (CanonicalM MVar) := ⟨(·.toMVar)⟩
instance : Coe RawTyp (CanonicalM TypeMVar) := ⟨(·.toTypeMVar)⟩

/-! ### Notation -/

declare_syntax_cat canonical_term
syntax:max ident : canonical_term
syntax:max "(" canonical_term ")" : canonical_term
syntax ident (ppSpace canonical_term:max)+ : canonical_term
syntax "fun" (ppSpace ident)+ " ↦ " canonical_term : canonical_term

declare_syntax_cat canonical_type
syntax canonical_term : canonical_type
syntax "(" ident " : " canonical_type ")" " → " canonical_type : canonical_type

syntax "term{ " canonical_term " }" : term
syntax "type{ " canonical_type " }" : term

def nameLit (x : Ident) : StrLit := Syntax.mkStrLit x.getId.toString

/-- `ctx` is the names in scope, which the variables are required to be among. -/
partial def expandTerm (ctx : Array String) (params : Array Ident) :
    TSyntax `canonical_term → MacroM Lean.Term
  | `(canonical_term| $head:ident) => spine head #[]
  | `(canonical_term| $head:ident $args*) => spine head args
  | `(canonical_term| ($t)) => expandTerm ctx params t
  | `(canonical_term| fun $xs* ↦ $t) => expandTerm ctx (params ++ xs) t
  | _ => Macro.throwUnsupported
where
  spine (head : Ident) (args : Array (TSyntax `canonical_term)) := do
    let ctx := ctx ++ params.map (·.getId.toString)
    unless ctx.contains head.getId.toString do
      Macro.throwErrorAt head s!"unknown variable `{head.getId}`"
    let args ← args.mapM (expandTerm ctx #[])
    `(RawTerm.mk #[$(params.map nameLit),*] $(nameLit head) #[$args,*])

partial def expandType (ctx : Array String) (binders : Array (Ident × TSyntax `canonical_type)) :
    TSyntax `canonical_type → MacroM Lean.Term
  | `(canonical_type| ($x : $input) → $t) => expandType ctx (binders.push (x, input)) t
  | `(canonical_type| $t:canonical_term) => do
    let ctx := ctx ++ binders.map (·.1.getId.toString)
    let inputs ← binders.mapM fun (x, input) => do
      `(($(nameLit x), $(← expandType ctx #[] input)))
    `(RawTyp.mk #[$inputs,*] $(← expandTerm ctx #[] t))
  | _ => Macro.throwUnsupported

macro_rules
  | `(term{ $t }) => expandTerm #[] #[] t
  | `(type{ $t }) => expandType #[] #[] t

/-! ### Display -/

def nameIdent? : Expr → Option Ident
  | .lit (.strVal name) => some (mkIdent (.mkSimple name))
  | _ => none

partial def termSyntax (e : Expr) : DelabM (TSyntax `canonical_term) := do
  guard (e.isAppOfArity ``RawTerm.mk 3)
  let some (_, params) := (e.getArg! 0).arrayLit? | failure
  let some params := params.toArray.mapM nameIdent? | failure
  let some head := nameIdent? (e.getArg! 1) | failure
  let some (_, args) := (e.getArg! 2).arrayLit? | failure
  let args ← args.toArray.mapM fun arg => do
    let atom := (arg.getArg! 0).arrayLit?.any (·.2.isEmpty) && (arg.getArg! 2).arrayLit?.any (·.2.isEmpty)
    if atom then termSyntax arg else `(canonical_term| ($(← termSyntax arg)))
  let spine ← if args.isEmpty then `(canonical_term| $head:ident)
    else `(canonical_term| $head:ident $args*)
  if params.isEmpty then return spine else `(canonical_term| fun $params* ↦ $spine)

partial def typeSyntax (e : Expr) : DelabM (TSyntax `canonical_type) := do
  guard (e.isAppOfArity ``RawTyp.mk 2)
  let some (_, inputs) := (e.getArg! 0).arrayLit? | failure
  let mut type ← `(canonical_type| $(← termSyntax (e.getArg! 1)):canonical_term)
  for input in inputs.reverse do
    guard (input.isAppOfArity ``Prod.mk 4)
    let some name := nameIdent? (input.getArg! 2) | failure
    type ← `(canonical_type| ($name : $(← typeSyntax (input.getArg! 3))) → $type)
  return type

@[app_delab RawTerm.mk]
def delabRawTerm : Delab := whenPPOption getPPNotation do `(term{ $(← termSyntax (← SubExpr.getExpr)) })

@[app_delab RawTyp.mk]
def delabRawTyp : Delab := whenPPOption getPPNotation do `(type{ $(← typeSyntax (← SubExpr.getExpr)) })
