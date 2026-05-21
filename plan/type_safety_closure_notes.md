# Type Safety Closure Notes

This file holds closure-specific design and proof notes split out of
`plan/type_safety_roadmap.md`. It is reference material. The active next task
is still defined by `plan/type_safety_roadmap.md`.

## Stage Plan

### Stage 7a: Immutable Unrestricted Captures

- Surface syntax:

  ```text
  closure [x, y](args) -> ret { body }
  ```

- Capture list contains variable names only. No `&x` or `&mut x` capture syntax
  in this stage.
- Accepted captures are immutable unrestricted reference-free values.
- Capturing copies source values into hidden capture slots.
- Mutating or consuming captured slots is rejected.
- Closure literals lower by lambda lifting:

  ```text
  surface:
    closure [x, y](a: A) -> R { body }

  synthetic function:
    fn __closure_N captures (x: X, y: Y) params (a: A) -> R { body }

  core expression:
    EMakeClosure __closure_N [x, y]
  ```

- Synthetic functions store hidden captures in `fn_captures`; ordinary call
  parameters remain in `fn_params`.
- Runtime values use `VClosure fname captured`.
- Direct `ECall` and `EFn` remain empty-capture only.
- Proof target: show that evaluating the closure literal produces a captured
  store satisfying `captured_store_runtime_ready`, then prove preservation for
  the direct core shape `ECallExpr (EMakeClosure fname captures) args`.

### Stage 7b: Captured References and Closure Lifetimes

- Still no borrow-capture syntax.
- Capturing variables whose values are already references becomes supported.
- Add the real `closure<'env>(Args) -> Ret` discipline: each captured `&'a T`
  requires `'a : 'env`, and the closure value may not escape `'env`.
- Extend captured-store readiness with lifetime validity and root reachability
  for captured references.

### Stage 7c: Borrow-Capture Syntax

- Add `closure [&x]` and `closure [&mut x]`.
- Parser records syntax only.
- Elaboration/checking creates the borrow and performs ownership/lifetime
  checks.
- Do not put ownership-sensitive desugaring in OCaml.

### Stage 7d: Mutable Unrestricted Closure Environments

- Allow mutable unrestricted captured slots to be assigned/replaced inside the
  closure body.
- Calls that may update the captured environment require a mutable closure
  place as receiver.
- Updated captured store is written back to the closure value.
- Proof target: split immutable-call preservation from mutable receiver-call
  preservation.

### Stage 7e: Affine and Linear Captures

- Add move capture for affine/linear values after unrestricted closure calls
  are proved.
- Closure usage is usage-polymorphic like structs: outer usage is the maximum
  usage of captured values.
- Moving affine/linear values into closures must respect active references.
- Consuming calls move the closure value and may consume captured affine/linear
  slots.

## Implemented Closure Infrastructure

- `Types.v` has `TClosure env_lt params ret` separate from `TFn`.
- Lifetime substitution, lifetime mapping, bound-lifetime detection,
  type-parameter substitution, well-formedness, equality, type depth,
  validation traversals, runtime lifetime-equivalence helpers, and extracted
  OCaml printers handle `TClosure`.
- Prop-level and executable `ty_compatible` allow `TClosure` with `TClosure`,
  and captureless `TFn` where `TClosure` is expected.
- The reverse `TClosure`-as-`TFn` direction remains rejected.
- `ECallExpr` typing/checking accepts callees whose inferred type is
  `TClosure env_lt params ret`.
- `fn_def` separates `fn_captures` from `fn_params`.
- Frontend-created functions elaborate with empty captures.
- Direct `EFn` / `ECall` typing, checking, and evaluation require empty
  captures.
- `fn_body_ctx f` is:

  ```coq
  params_ctx (fn_params f ++ fn_captures f)
  ```

- Function validation checks `fn_params ++ fn_captures` as one binding
  namespace.
- `EMakeClosure fname captures` is implemented for immutable unrestricted
  reference-free captures.
- Surface Stage 7a closure syntax is parsed, converted to extracted Rocq
  `raw_expr`, and elaborated by `elaborate_raw_global_env`.
- OCaml does not duplicate closure type-checking logic.
- FIR emission handles Stage 7a closure values and synthetic closure functions.
- Regression coverage exists under `tests/valid/closure/`,
  `tests/invalid/closure/`, and `tests/fir/closure_capture_value.facet`.

## Proof Infrastructure Already Available

- `captured_store_runtime_ready`
- `captured_call_frame_ready`
- `captured_call_frame_ready_compose`
- `captured_params_store_typed`
- `captured_call_frame_params_ready`
- `check_make_closure_captures_exact_sctx_sound`
- `copy_capture_store_exact_sctx_of_store`
- `copy_capture_store_exact_params_store_typed`
- `eval_captured_call_body_ctx_cleanup_preserves_value_and_refs_erased`
- `eval_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased`
- `eval_make_closure_exact_captured_call_frame_params_ready`
- `eval_make_closure_exact_captured_call_frame_params_ready_auto`
- `eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased`
- `eval_make_closure_captured_call_expr_body_ctx_cleanup_preserves_value_and_refs_erased_auto`
- `eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components`

These helpers do not permit validator widening by themselves. Widen validators
only after the matching preservation theorem compiles.

## Current Captured-Call Sidecar

The narrow captured-call sidecar package exists for exactly:

```coq
ECallExpr (EMakeClosure fname captures) args
```

It records:

- executable exact capture success via `check_make_closure_captures_exact_sctx`;
- callee lifetime count is zero;
- hidden capture names are disjoint from `args_local_store_names args`;
- callee-body root/shadow provenance under:

  ```coq
  initial_root_env_for_params (fn_params ++ fn_captures)
  ```

- `NoDup` for the whole binding list:

  ```coq
  ctx_names (params_ctx (fn_params fdef ++ fn_captures fdef))
  ```

## Current Status

Stage 7a direct and annotated local-let captured-call sidecar routes are
implemented for immutable unrestricted reference-free captures.

Implemented proof route:

```coq
copy_capture_store_as
  -> captured_store_runtime_ready
  -> captured_call_frame_ready
  -> captured_call_frame_ready_compose
  -> eval_make_closure_captured_call_expr_* cleanup/preservation
```

- `capture_ref_free_ty` is available as the Prop mirror for
  `capture_ref_free_ty_b`.
- `capture_ref_free_ty_b_sound` proves successful executable checks produce
  that Prop evidence.
- `capture_ref_free_ty` remains structural. Do not add compatibility or
  lifetime-equivalence closure constructors to it.
- `runtime_rootless_ty` is available in `TypeSafety.v` as a structural
  proof-only predicate. Its struct case factors instantiated fields through
  `runtime_rootless_fields`, not through type arguments themselves.
- `capture_ref_free_ty_b_fuel_runtime_rootless` and
  `capture_ref_free_ty_b_runtime_rootless` prove executable
  capture-ref-free checks imply that predicate.
- `ty_compatible_runtime_rootless_actual` handles the `VHT_Compatible` route
  without broadening `capture_ref_free_ty`.
- `ty_lifetime_equiv_runtime_rootless_actual` and
  `ty_lifetime_equiv_runtime_rootless_fields_actual` handle the
  `VHT_LifetimeEquiv` route.
- `value_has_type_runtime_rootless_empty_roots` and
  `struct_fields_have_type_runtime_rootless_empty_roots` prove runtime-rootless
  typed values fit in the empty root set.
- `empty_root_env_for_store` constructs the copied-capture `Rcap`.
- `copy_capture_store_as_captured_store_runtime_ready` proves exact capture
  copy satisfies `captured_store_runtime_ready`.
- `copy_capture_store_as_captured_call_frame_ready` constructs the copied
  hidden capture frame readiness package.
- Hidden capture names are proved absent from evaluated argument stores/root
  environments, allowing `captured_call_frame_ready_compose`.
- `eval_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core`
  and
  `eval_let_make_closure_captured_call_runtime_args_ready_auto_with_preservation_core`
  build the runtime-argument readiness needed by the checked sidecar routes.
- `eval_make_closure_captured_call_expr_preserves_typing_with_callee_components`
  and
  `eval_let_make_closure_captured_call_expr_preserves_typing_with_callee_components`
  are the checked preservation bridge endpoints for direct and annotated
  local-let captured calls.

The proof bodies are split across:

- `TypeSafetyClosureRuntimeArgs.v`: copied-capture/runtime-argument readiness.
- `TypeSafetyClosureCleanup.v`: parameterized cleanup cores and captured-call
  cleanup wrappers.
- `TypeSafetyClosure.v`: export aggregator.

## Next Closure Lemmas

1. Do not add `ELetInfer` captured-call support until the semantics has an
   evaluable `ELetInfer` case or the route is expressed through an existing
   evaluable core shape. Current `ELetInfer` preservation is vacuous by
   inversion on evaluation.
2. For broader captured closures, move to Stage 7b: captured references plus
   closure lifetime evidence. Extend captured-store readiness with lifetime
   validity and root reachability before widening validators.
3. Keep direct `EFn`/`ECall` empty-capture only. Captured closure calls should
   stay on explicit captured-call sidecar routes.
