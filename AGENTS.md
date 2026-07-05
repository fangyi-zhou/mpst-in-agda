# AGENTS.md

Guidance for coding agents working in this repository.

## Build

```bash
agda Everything.agda
```

This typechecks all modules. There is no separate test runner; successful typechecking is the proof.

You can also run:

```bash
make typecheck
```

The project uses Agda 2.7.0.1 and standard-library 2.3 (`standard-library-2.3`).

## Project Structure

This is an Agda mechanisation of multiparty session type (MPST) theory. Participants are `Fin n`, a finite set of `n` roles, and labels are `Fin ℓ`.

Core modules:

- `Common.agda` - shared definitions, including `Action n ℓ`, a send/receive between two distinct roles with a label.
- `Global.agda` - global types (`Global n ℓ`): `endG` or `msgSingle p q p≢q l g`; reduction relation `_-_→g_`.
- `Local.agda` - local types (`Local n ℓ`): `endL`, `sendSingle`, `recvSingle`; `Configuration n ℓ = Vec (Local n ℓ) n`; reductions `_-_→l_` and `_-_→c_`.
- `Projection.agda` - `project : Global n ℓ → Fin n → Local n ℓ`; `_↔_` record relating a global type to a configuration via projection.
- `Soundness.agda` - if `g ↔ c` and `g` reduces, then `c` reduces to a matching configuration.
- `Completeness.agda` - if `g ↔ c` and `c` reduces, then `g` reduces; uses a size measure on `g` for termination.
- `Participation.agda` - participation-related definitions and lemmas.
- `Example.agda` - concrete examples with `n = 4` roles and `ℓ = 2` labels.
- `Everything.agda` - imports the full development for repository-wide typechecking.

## Conventions

- Inequality evidence `p ≢ q` is carried in `Action` and `msgSingle` constructors rather than computed.
- Smart constructors `action′` and `msgSingle′` take `{False (p ≟ q)}` for convenience.
- Syntax constructors are descriptive prefix names (`action`, `msgSingle`, `sendSingle`, `recvSingle`). Mixfix names are reserved for relations/records such as `_-_→g_`, `_-_→l_`, `_-_→c_`, and `_↔_`, with explicit fixity declarations at their definition sites.
- `[]≔-commutes` and `[]≔-idempotent` from `Data.Vec.Properties` require named implicit arguments `{x = ...} {y = ...}` in standard-library 2.3, because those variables moved to module-level `private variable` declarations.

## Workflow

- Prefer small, typechecked changes.
- Run `agda Everything.agda` or `make typecheck` before reporting completion when possible.
- Treat `.agdai` files and `_build/` as generated artifacts.
