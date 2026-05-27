# End-to-end safety roadmap

## Goal

Unify the executable type-checking entrypoint used by the OCaml CLI so that
end-to-end soundness and type safety can be stated against one extracted Rocq
checker path.  The target design has no `infer_full_env` fallback: programs are
accepted only when the roots checker and its safety gates accept them.

The initial end-to-end claim is for the core `global_env` produced after the
current parser/de Bruijn frontend.  Parser and de Bruijn correctness remain
outside this roadmap unless a separate frontend-correctness proof is added.

## Current issue

The OCaml CLI currently alpha-normalizes the frontend output, then checks each
function with `infer_full_env_roots`.  If that checker returns
`ErrNotImplemented`, the CLI falls back to `infer_full_env`.

This is useful operationally, but it prevents a clean end-to-end theorem:

- `infer_full_env_roots` has roots/provenance soundness and conditional runtime
  type-safety theorems.
- `infer_full_env` has structural checker soundness, but it does not produce the
  roots/provenance evidence needed by the stronger runtime safety path.
- The OCaml accept/reject predicate is a handwritten combination of both paths,
  not one Rocq-level checker predicate with a matching theorem.

## Roadmap

### 1. Define a single Rocq checker entrypoint

Add a fallback-free checker entrypoint in `TypeChecker.v`.

- `infer_fn_env_end2end env f`
  - Computes `R0 := initial_root_env_for_params (fn_params f ++ fn_captures f)`.
  - Calls `infer_full_env_roots env f R0`.
  - Applies the required root/shadow/provenance safety gates.
  - Returns `infer_ok` only when the function is accepted by the roots path.
  - Returns `infer_err err` directly; `ErrNotImplemented` is not recovered.
- `infer_program_env_end2end env`
  - Alpha-normalizes `env`.
  - Checks global name uniqueness.
  - Checks every function with `infer_fn_env_end2end`.
  - Returns the alpha-normalized environment on success.
- `check_program_env_end2end env`
  - Boolean wrapper for proofs and tests.

Do not duplicate type-checking logic in OCaml.  OCaml should call the extracted
program-level entrypoint.

### 2. Complete roots checker coverage

Remove accepted-program dependence on `ErrNotImplemented`.

Priority gaps to close:

- General `ECallExpr`, including function values and closures.
- `EDeref`.
- Field-place variants of `EReplace`, `EAssign`, and `EBorrow`.
- Struct and match cases where roots/shadow/provenance gates still reject or
  return `ErrNotImplemented`.

For each construct:

- Update the executable roots checker first.
- Prove the corresponding roots checker soundness lemma.
- Connect the construct to the existing runtime type-safety path.
- Add valid and invalid CLI regression tests for the construct.

### 3. Prove checker soundness for the unified entrypoint

Prove that the new function-level checker implies the existing Prop-level
checked relation.

Expected theorem shape:

```coq
Theorem infer_fn_env_end2end_sound :
  forall env f env' T Γ' R' roots,
    infer_fn_env_end2end env f = infer_ok (...) ->
    checked_fn_env_roots env' f ... .
```

The exact return type should follow the implementation, but the theorem must
reuse `infer_full_env_roots_sound` and preserve the roots/provenance evidence
needed by runtime safety.

Then prove the program-level version:

```coq
Theorem check_program_env_end2end_sound :
  forall env,
    check_program_env_end2end env = true ->
    forall f,
      In f (env_fns (alpha_normalize_global_env env)) ->
      checked_fn_env_roots ... .
```

### 4. Prove end-to-end type safety for the unified checker

Connect the unified checker to the runtime theorem.

Expected theorem shape:

```coq
Theorem infer_program_env_end2end_big_step_safe_checked_initial_ready :
  forall env env' f s s' v,
    infer_program_env_end2end env = infer_ok env' ->
    check_initial_root_runtime_ready f s = true ->
    In f (env_fns env') ->
    initial_store_for_fn env' f s ->
    eval env' s (fn_body f) s' v ->
    value_has_type env' s' v (fn_ret f).
```

This theorem should be the primary end-to-end statement for the extracted
checker.  It still assumes a core environment and a checked initial runtime
store; it does not claim parser correctness.

### 5. Switch OCaml to the unified extracted checker

Update the extraction list and OCaml CLI.

- Extract `infer_program_env_end2end` and `check_program_env_end2end`.
- Regenerate `fixtures/TypeChecker.ml` and `.mli` with `cd rocq && make`.
- In `ocaml/main.ml`, remove the per-function fallback logic.
- Accept only when `infer_program_env_end2end env` returns `infer_ok env'`.
- Use `env'` for FIR emission and diagnostics.
- Preserve `infer_err` as CLI failure without reinterpretation.

`infer_full_env` may remain extracted for development or legacy tests, but it
must not be used by the CLI accept path.

### 6. Make the rule durable for future agents and changes

After the unified checker and proofs are in place, codify the policy so future
language work cannot bypass it.

- Add an `AGENTS.md` rule requiring the OCaml CLI accept/reject path to use only
  the extracted `infer_program_env_end2end` entrypoint.
- State that language features, typing rules, checker behavior, borrow/root
  rules, desugaring-to-core changes, and extraction changes must preserve or
  extend the end-to-end soundness and type-safety theorems.
- Explicitly forbid OCaml fallback paths to `infer_full_env`,
  `infer_full_env_roots`, or `check_program_env` for acceptance.
- Add CI checks that fail if OCaml CLI code calls forbidden checker entrypoints
  or if the required end-to-end theorem names disappear.
- Require valid/invalid CLI tests for new language constructs to pass through
  `infer_program_env_end2end` without `ErrNotImplemented`.

## Tests and checks

Run after each phase:

- `cd rocq && make`
- `rg -n "\bAxiom\b|Admitted\.|Abort\." rocq/theories`

Run after OCaml integration:

- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh`

Add regression coverage:

- Valid function-value and closure calls that previously required fallback.
- Invalid function-value calls with type mismatch and arity mismatch.
- Valid and invalid deref, field borrow, field assign, and field replace cases.
- Struct and match programs that exercise root/shadow/provenance checks.
- A CLI regression asserting accepted valid tests do not produce
  `ErrNotImplemented`.

## Acceptance criteria

- `ocaml/main.ml` no longer calls `infer_full_env` for fallback.
- Accepted CLI programs pass through one extracted Rocq checker entrypoint.
- `ErrNotImplemented` is treated as a rejection, not as a fallback trigger.
- Rocq has a program-level theorem connecting the extracted end-to-end checker
  success to runtime type safety for the alpha-normalized core environment.
- Generated OCaml fixtures are updated only by Rocq extraction.
- Repository guidelines and CI enforce `infer_program_env_end2end` as the only
  OCaml CLI acceptance authority for future changes.
