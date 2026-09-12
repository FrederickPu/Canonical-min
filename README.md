# Canonical-min

Canonical-min is a sound and complete solver for type inhabitation and unification in dependent type theory, written in 185 lines of Lean. Canonical-min serves as a simplified reference for the algorithm behind [Canonical](github.com/chasenorman/Canonical), and a baseline for the development of future automated reasoning tools. A special feature of this implementation is the use of the *continuation monad* to convert the type checker into a constraint solver. 

## Project Structure

- `Data.lean` — The definition of terms and types.
- `Monad.lean` — The monadic framework to convert the type checker into a solver.
- `Checker.lean` — The type checker.
- `Search.lean` — The iterative deepening depth-first search. 

## Lean Kernel Arena

`canonical-min-arena` consumes the NDJSON format produced by
[`lean4export`](https://github.com/leanprover/lean4export). It uses CanonicalLean's
existing expression translation and then checks declaration values with
`CanonicalMin.check`.

```sh
lake build canonical-min-arena
LD_LIBRARY_PATH=.lake/packages/Canonical/.lake/build/lib \
  lake env .lake/build/bin/canonical-min-arena export.ndjson
```

The executable follows the arena exit-code contract: `0` accepts, `1` rejects,
and `2` declines declarations outside canonical-min's currently supported
fragment.

An arena checker entry can use:

```yaml
build: lake build canonical-min-arena
run: LD_LIBRARY_PATH=.lake/packages/Canonical/.lake/build/lib lake env .lake/build/bin/canonical-min-arena "$IN"
```

The current interface declines inductive and quotient declarations, unsafe or
partial definitions, and terms that CanonicalLean cannot translate.
