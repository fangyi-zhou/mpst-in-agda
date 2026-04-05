# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build

```bash
agda Everything.agda
```

This typechecks all modules. There is no separate test runner — successful typechecking is the proof.

The stdlib is stdlib v2.3 (`standard-library-2.3`) with Agda 2.7.0.1.

## Architecture

This is an Agda mechanisation of multiparty session type (MPST) theory. Participants are `Fin n` (a finite set of `n` roles) and labels are `Fin ℓ`.

**Core types:**
- `Common.agda` — shared definitions: `Action n ℓ` (a send/receive between two distinct roles with a label)
- `Global.agda` — global types (`Global n ℓ`): `endG` or `msgSingle p q p≢q l g`; reduction relation `_-_→g_`
- `Local.agda` — local types (`Local n ℓ`): `endL`, `sendSingle`, `recvSingle`; `Configuration n ℓ = Vec (Local n ℓ) n`; reduction `_-_→l_` and `_-_→c_`
- `Projection.agda` — the `project : Global n ℓ → Fin n → Local n ℓ` function; `_↔_` record relating a global type to a configuration via projection
- `Soundness.agda` — if `g ↔ c` and `g` reduces, then `c` reduces to a matching configuration
- `Completeness.agda` — if `g ↔ c` and `c` reduces, then `g` reduces (uses a size measure on `g` for termination)
- `Example.agda` — concrete examples with `n=4` roles and `ℓ=2` labels

**Key design choices:**
- Inequality evidence `p ≢ q` is carried in `Action` and `msgSingle` constructors rather than computed; smart constructors `action′` / `msgSingle′` take `{False (p ≟ q)}` for convenience
- `[]≔-commutes` and `[]≔-idempotent` from `Data.Vec.Properties` require named implicit args `{x = ...} {y = ...}` in stdlib v2.3, since those variables moved to module-level `private variable` declarations
