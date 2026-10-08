import CanonicalMin.Checker
import CanonicalMin.Notation

/-- Whether the term has the type. -/
def checks (ty : CanonicalM TypeMVar) (tm : CanonicalM MVar) : Bool :=
  let x : CanonicalM Bool := do
    let tmvar ← ty
    let mvar ← tm
    return (← run (check (Term.mk mvar []) (Typ.mk tmvar []) ⟨0, #[]⟩)).isSome
  (x.run {}).1

#guard checks type{ (U : U) → (A : U) → (a : A) → A } term{ fun U A a ↦ a }
#guard !checks type{ (U : U) → (A : U) → (a : A) → A } term{ fun U A a ↦ A }
#guard checks type{ (U : U) → (A : U) → (B : U) → (f : (a : A) → B) → (a : A) → B }
  term{ fun U A B f a ↦ f a }
#guard !checks type{ (U : U) → (A : U) → (B : U) → (f : (a : A) → B) → (a : A) → B }
  term{ fun U A B f a ↦ a }

/-- error: unknown variable `B` -/
#guard_msgs in
#check type{ (A : A) → B }

deriving instance Repr for MVar, TypeMVar
deriving instance Repr for Assignment

/-- The value of `x`, and the assignments of its metavariables. -/
def raw [Repr α] (x : CanonicalM α) : Std.Format :=
  let (value, state) := x.run {}
  repr (value, state.assignments)

/--
info: ({ id := 1, lctx := [], preferredNames := #["f", "a"] },
 #[some { debruijn := 0, index := 1, args := #[] },
   some { debruijn := 0, index := 0, args := #[{ id := 0, lctx := [], preferredNames := #[] }] }])
-/
#guard_msgs in
#eval raw term{ fun f a ↦ f a }.toMVar

/--
info: ({ inputs := #[{ inputs := #[], output := { id := 0, lctx := [], preferredNames := #[] } },
               { inputs := #[], output := { id := 1, lctx := [], preferredNames := #[] } }],
   output := { id := 2, lctx := [], preferredNames := #["A", "a"] } },
 #[some { debruijn := 0, index := 0, args := #[] }, some { debruijn := 0, index := 0, args := #[] },
   some { debruijn := 0, index := 0, args := #[] }])
-/
#guard_msgs in
#eval raw type{ (A : A) → (a : A) → A }.toTypeMVar

/-- info: type{ (U : U) → (A : U) → (f : (a : A) → A) → (a : A) → A } : RawTyp -/
#guard_msgs in
#check type{ (U : U) → (A : U) → (f : (a : A) → A) → (a : A) → A }

/-- info: term{ fun U A f a ↦ f (f a) } : RawTerm -/
#guard_msgs in
#check term{ fun U A f a ↦ f (f a) }

/-- info: term{ fun f ↦ f (fun x ↦ x) } : RawTerm -/
#guard_msgs in
#check term{ fun f ↦ f (fun x ↦ x) }

/--
info: { params := (List.cons "f" (List.cons "a" List.nil)).toArray, head := "f",
  args := (List.cons { params := List.nil.toArray, head := "a", args := List.nil.toArray } List.nil).toArray } : RawTerm
-/
#guard_msgs in
set_option pp.notation false in
#check term{ fun f a ↦ f a }
