# Type Safety Roadmap

This file is the active Codex-facing implementation guide. Keep it focused on
the next implementation decision and the current proof blockers.

Reference files:

- `plan/type_safety_endpoints.md`: detailed theorem/API endpoint names.
- `plan/type_safety_roadmap_inventory.md`: completed proof inventory.
- `plan/type_safety_roadmap_history.md`: older milestone notes.
- `plan/closure.md`: closure design details.

## How Codex Should Read This File

Use this file as the active work guide:

1. Read `Purpose` and `Codex Digest` to identify the target theorem and the
   current executable endpoints.
2. Use `Next Implementation Order` to choose the next task. Do not mine
   reference files for new work unless the active roadmap points there.
3. Use `plan/type_safety_endpoints.md` only when an implementation task needs
   an existing theorem or checker entrypoint name.
4. Treat `plan/type_safety_roadmap_inventory.md` as history and proof context,
   not as the implementation queue.

When updating this file, keep the digest, current endpoint, and known gaps in
sync. Stale theorem names in the digest cause future agents to take the wrong
route.

## Purpose

The primary goal is to prove operational type safety for the user-facing,
ordinary checker pipeline.

Canonical target:

```coq
infer_full_env env f = infer_ok (T, Γ')
  -> initial_store_for_fn f s
  -> eval env s (fn_body f) s' v
  -> value_has_type env s' v (fn_ret f).
```

The root checker is not the language definition and is not a substitute for
ordinary checker safety. Root provenance remains auxiliary evidence used for
runtime reference safety, let-local escape checks, and direct-call cleanup
proofs. If a future design promotes the root checker to the canonical route,
that decision must be made explicitly and this file must be rewritten around
that theorem.

## Codex Digest

Quick interpretation for implementation work:

- **Canonical goal (Ordinary checker target):**

  ```coq
  infer_full_env env f = infer_ok (T, Γ')
    -> initial_store_for_fn f s
    -> eval env s (fn_body f) s' v
    -> value_has_type env s' v (fn_ret f).
  ```

- **User-facing accepted-program checker:**
  `check_program_env_alpha`
- **Validated sidecar checker, general provenance route:**
  `check_program_env_alpha_validated_root_shadow_provenance_summary`
- **Validated sidecar checker, direct-call-local route:**
  `check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary`
- **Strongest executable theorem, general provenance route:**
  `check_program_env_alpha_validated_root_shadow_provenance_summary_big_step_safe_checked_initial_ready`
- **Strongest executable theorem, direct-call-local route:**
  `check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary_big_step_safe_checked_initial_ready`
- **Current sidecar rule:** executable validators discharge proof evidence;
  they do not redefine the language accepted by the ordinary checker.

Current gap summary:

- Ordinary checker acceptance still exceeds validator acceptance.
- Initial-runtime readiness is a checked execution-state premise, not a program
  acceptance condition.
- Direct `ECall` has a localized sidecar route. Do not add it to ordinary
  expression readiness.
- `ECallExpr (EFn fname) args` is closed as syntactic direct-call sugar in the
  direct-call-local sidecar route.
- General `ECallExpr callee args` remains a staged design gap. The staged
  order is: first-class functions without captures, then MVP closures with
  immutable unrestricted captures, then captured references/lifetimes, then
  mutable and affine/linear captures.
- Core-only closure construction for immutable unrestricted reference-free
  captures is implemented as `EMakeClosure`; parser syntax, frontend lambda
  lifting, and captured `ECallExpr` preservation are still future work.

Next-task rule:

1. Prefer reducing concrete validator false negatives already listed in the
   ready-gap matrix.
2. Before widening any validator, check the ordinary checker review gates.
3. If the next step requires a new invariant, checker contract change, or
   theorem shape decision beyond the staged `ECallExpr` plan below, stop and
   document the design choice instead of implementing.

## Canonical Route

1. Prove preservation and runtime safety from the Prop-level ordinary typing
   rules used by checker soundness.
2. Connect ordinary checker soundness to the preservation theorem.
3. Use root provenance only when the operational proof needs reference-target
   or cleanup evidence that ordinary typing does not currently expose.
4. Keep root-checker success as a sidecar theorem unless the project explicitly
   changes the user-facing checker contract.

Do not make the root checker stricter than the ordinary checker to patch a
proof gap. The ordinary safety route should prove structural preservation from
the existing structural rules and checker soundness. In particular, do not
strengthen `TES_If` or ordinary checker acceptance merely to manufacture
shadow/root sidecar evidence.

## Fixed Design Decisions

- Big-step preservation comes before progress.
- Progress is deferred until a future small-step semantics exists.
- Checker soundness and operational type safety stay separate until the final
  checker-to-runtime theorem connects them.
- The ordinary checker is the primary accepted-program interface.
- Root provenance is a sidecar API:
  - `infer_core_env_roots`
  - `infer_env_roots`
  - `infer_full_env_roots`
- Updating the sidecar API requires updating its soundness theorem.
- Lifetime inference and root provenance inference are separate: lifetime
  inference determines lifetime substitution; root provenance determines which
  runtime roots flow through references.
- Runtime calls freshen callee function definitions against caller/captured
  store names before `bind_params`.
- The user-facing checker route should type-check alpha-normalized core.
  The verified operational target is the alpha-normalized core, not the
  pre-normalization frontend core.
- Root provenance should run on alpha-renamed, shadow-free core terms when root
  evidence is needed.
- `let x = &x` is not inherently unsafe. After alpha-renaming-before-checking,
  the internal shape is `let x_fresh = &x`, so initializer roots do not collide
  with the binder being introduced.
- Do not reject initializer roots merely because they mention the source binder
  name of a shadowing `let`.
- Reference `drop` does not release a borrow. Cases like `drop r; drop x` are
  deferred to future non-lexical lifetime / last-use analysis.
- Local annotation lifetime elision remains rejected until fresh local lifetime
  regions are designed.
- Same-argument-name parameters in one function are rejected.
- Duplicate-parameter and shadowing errors should stay distinguishable.
- Captureless `fn(...) -> ...` and captured `closure<'env>(...) -> ...` are
  separate callable value types. `fn_value_ty` remains the empty-capture
  function item wrapper; captured closures use `closure_value_ty`.
- Closure literals use explicit capture lists. The parser records capture
  syntax; elaboration/checking performs copy/move/borrow decisions.
- Closure literals are lowered by lambda lifting. The generated synthetic
  function takes hidden capture parameters first, followed by ordinary call
  parameters, and runtime values reuse the existing `VClosure fname captured`
  representation.
- Rust-style `Fn` / `FnMut` / `FnOnce` are not new Facet kinds. Their behavior
  is represented by receiver mutability, closure value usage, and whether the
  captured environment is read, updated, or consumed.

## Codex Quick Path

Start here. The reference files listed at the top are history/context, not the
implementation order.

### Current Goal

Make the ordinary-checker safety route understandable and implementable without
turning the root checker into the language definition.

Near-term working goal:

1. Keep `check_program_env_alpha` as the ordinary accepted-program checker.
2. Use executable safety validators only to discharge proof evidence that the
   current operational proof still needs.
3. Reduce the validator's false negatives until the safety-validator route has
   the same accepted program range as the ordinary checker, or until a specific
   gap is proven to require a checker contract decision.
4. Keep initial runtime readiness as a separate execution-state obligation; it
   is not part of program acceptance.

Do not claim ordinary-checker-only safety until the final theorem no longer
needs root-shadow summary evidence, preservation readiness sidecar evidence, or
initial runtime readiness beyond the agreed initial-store contract.
For Codex updates, treat this as: reduce explicit validator false negatives first,
then decide whether each remaining gap is intrinsic to the checker contract.

### Current Route

The active route is ordinary checker safety over alpha-normalized core:

1. The frontend/checker path checks `alpha_normalize_global_env env`.
2. Ordinary checker success gives structural typing.
3. Structural preservation proves `value_has_type`.
4. Root/shadow evidence is used only as sidecar evidence for direct-call
   cleanup/provenance.

Do not try to prove `typed_env_structural -> typed_env_roots_shadow_safe` as the
canonical route.

### Next Implementation Order

Follow this order before inventing new theorem shapes:

1. **List acceptance gaps with fixtures and Rocq examples.**
   Add small examples that pass the ordinary checker but fail the current
   safety-validator route. Include both `.facet` fixtures and small core-AST
   examples when parser/desugarer behavior would obscure the proof issue.
   Include the still-relevant `plan/review.md` safety cases in this matrix so
   validator widening does not re-open old ordinary-checker bugs.
   Current implementation note: `TypeChecker.v` now contains a core-AST gap
   matrix for ordinary-checker accepted shapes rejected by the current
   preservation-ready validator: annotated `ELet`, existing `ELetInfer`,
   `EDeref (EBorrow RShared ...)`, direct `ECall`, and
   `ECallExpr (EFn ...)`. Matching ordinary-checker accepted source fixtures
   live under `tests/valid/type_safety_ready_gap/`; source-level function-value
   calls use a local function-typed binding because the frontend lowers an
   unbound call name to direct `ECall`.
2. **Reduce `preservation_ready_expr_b` false negatives.**
   The current executable validator rejects broad syntax classes such as
   `ELet`, `ELetInfer`, direct `ECall`, `ECallExpr`, and `EDeref`. First make
   the structural preservation route cover ordinary accepted `let` and direct
   call cases where the proof already has the required facts. For `ELet` and
   `ELetInfer`, do not merely remove the validator rejection: first make the
   ordinary route account for let-local reference escape, either by proving the
   current checker already rejects it or by adding an executable ordinary
   checker-side escape check.
   Current implementation note: `provenance_ready_expr_b` now accepts `ELet`
   and `ELetInfer`, and the checker has an executable elaboration route that
   turns inferred lets into annotated `ELet`. Do not wire this into the
   existing root-shadow validator by simple substitution. The existing
   preservation-ready root-shadow validator remains unchanged. The additive
   provenance-only route is now represented by
   `callee_body_root_shadow_provenance_ready_at`,
   `callee_body_root_shadow_provenance_summary`, and
   `check_env_root_shadow_provenance_summary`; the program-level entrypoint
   is `check_program_env_alpha_validated_root_shadow_provenance_summary`.
   The Rocq examples currently show this provenance-only entrypoint accepts
   the annotated and inferred ready-gap `let` cases that the split
   preservation-ready validator rejects.
3. **Move the non-direct-call structural route toward no validator.**
   Prefer deriving or eliminating `preservation_ready_expr` obligations from
   ordinary typing/checker success over adding more executable checks.
4. **Localize direct-call cleanup and root evidence.**
   Root/shadow evidence should be required only for the direct-call cleanup and
   reference-provenance subproofs that actually need it. Avoid whole-program
   root-shadow validation when a narrower direct-call evidence package is
   enough.
   For direct `ECall`, do not widen ordinary or provenance expression
   readiness by simply adding an `ECall` constructor. Direct calls need
   callee-body root-shadow/provenance evidence, so the route must stay local:
   the caller body should use `preservation_direct_call_ready_expr`, while only
   the called callee body is required to have the existing root-shadow
   provenance summary evidence. Avoid a whole-environment validator shape that
   makes the direct-call caller depend on the same old summary predicate it is
   trying to relax.
   While doing this, keep `replace p e_new` target-conflict discipline visible:
   the ordinary checker must not allow `e_new` to consume or invalidate the
   place being replaced, and any proof route should use that fact directly
   rather than relying on a broad sidecar rejection.
5. **Closed: `ECallExpr (EFn fname) args` as direct-call sugar.**
   The direct-call-local sidecar route treats only the syntactic function-name
   form as equivalent to direct `ECall fname args`. The validator root-checks
   a synthetic `ECall fname args`, uses the same callee lookup, argument
   readiness, callee root-shadow provenance summary, and cleanup proof as
   direct `ECall`, and leaves general `ECallExpr` out of
   `provenance_ready_expr_b` and `preservation_ready_expr_b`.
   Current implementation note: `direct_call_target_expr` recognizes direct
   `ECall` and syntactic `ECallExpr (EFn fname) args`; general function-value
   calls remain rejected by the direct-call-local summary route.
6. **Prove first-class functions without captures.**
   After syntactic function-call sugar is closed, add a function-value
   provenance route for calls where evaluating `callee` yields a non-capturing
   top-level function value. The proof must retain evidence connecting the
   runtime function value to the `fname` whose callee summary is used. Do not
   use only the function type; type information alone loses the function-name
   summary needed by cleanup/provenance.
   Current implementation blocker: do not implement this by recognizing
   `let g = EFn fname in ECallExpr (EVar g) args` and rewriting the whole
   expression to `ECall fname args`. That rewrite is not semantics-preserving:
   the real `ECallExpr` evaluates the callee first, then evaluates arguments
   and freshens the callee body with `store_names (captured ++ s_args)`, while
   the direct `ECall` route freshens with `store_names s_args`. Even for
   empty captures, a local function-value binding can leave extra caller-frame
   names in scope before argument evaluation. The next implementation must
   prove a dedicated non-capturing `ECallExpr` preservation lemma that keeps
   the evaluated callee store in the proof, instead of converting the source
   expression to direct `ECall`.
   Stage 6a target: support only statically traced, empty-capture function
   values whose callee evaluation is proven store-preserving and whose
   `VClosure fname []` target is linked to the callee summary. Keep
   function-typed parameters and unknown function values rejected by the
   validator until this theorem shape is stable.
   Current implementation note: an executable validator now exists
   as
   `check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary`.
   It accepts only the local alias shapes
   `let g: unrestricted fn(...) = EFn fname in ECallExpr (EVar g) args` and
   `let g = EFn fname in ECallExpr (EVar g) args` by root-checking a
   structure-preserving synthetic body where only the call site is changed to
   `ECall fname args`. Annotated aliases with affine or linear outer
   function-value usage are deliberately rejected by this stage-6a sidecar:
   the proof relies on
   evaluating `EVar g` by copy, without consuming or changing the caller store.
   Supporting affine/linear function-value aliases belongs to a later theorem
   that explicitly accounts for callee evaluation effects.
   Current proof progress: the Prop mirror and boolean soundness bridge now
   exist as
   `callee_body_root_shadow_non_capturing_call_provenance_summary`,
   `env_fns_root_shadow_non_capturing_call_provenance_summary_check_ready`,
   `check_fn_root_shadow_non_capturing_call_provenance_summary_sound`, and
   `check_env_root_shadow_non_capturing_call_provenance_summary_ready`.
   There is also a local operational bridge
   `eval_local_unrestricted_fn_value_call_as_synthetic_call` showing that the
   unrestricted alias form evaluates like the structure-preserving synthetic
   `let` with an inner `ECall`.
   Current implementation progress: `eval_direct_call_body_cleanup_preserves_value_and_refs`
   now exposes both the equality
   `store_remove_params ... s_body = s_args` and the callee-body result-root
   fact `value_roots_within roots_body ret`. The bridge
   `direct_call_callee_body_root_shadow_provenance_summary_bridge_of_summary_with_result_subset`
   also records that instantiated callee result roots are bounded by
   `root_sets_union arg_roots`. Consequently
   `eval_preserves_typing_direct_call_roots_provenance_ready_with_callee_summary`
   now returns the stronger package needed by enclosing cleanup:
   `store_typed`, `value_has_type`, `store_ref_targets_preserved`,
   `store_roots_within R' s'`, `value_roots_within roots v`,
   `store_no_shadow s'`, and `root_env_no_shadow R'`.
   The checked-initial endpoint
   `check_program_env_alpha_validated_root_shadow_non_capturing_call_provenance_summary_big_step_safe_checked_initial_ready`
   is now proved. Its local-alias branch inverts the validated synthetic-let
   shape, converts evaluation with
   `eval_local_unrestricted_fn_value_call_as_synthetic_call`, applies the
   strengthened direct-call theorem to the inner `ECall`, and uses the returned
   result roots plus `TERS_Let` exclusions to type the final `store_remove g`.
7. **Introduce and prove closures in proof-friendly phases.**
   Do not implement every closure feature from `plan/closure.md` at once. Each
   phase must add a narrow language surface, the corresponding core
   elaboration, executable checks, Prop rules, and a preservation bridge before
   moving to the next phase.

   **Stage 7a: MVP immutable unrestricted captures.**
   - Surface syntax:
     `closure [x, y](args) -> ret { body }`.
   - Capture list contains variable names only. No `&x` / `&mut x` capture
     syntax in this stage.
   - Accepted captures are immutable unrestricted non-reference values only.
     Capturing copies the value into the closure environment. Mutating or
     consuming captured slots is rejected.
   - Lower closure literals by lambda lifting:

     ```text
     surface:
       closure [x, y](a: A) -> R { body }

     synthetic function:
       fn __closure_N captures (x: X, y: Y) params (a: A) -> R { body }

     core expression:
       EMakeClosure __closure_N [x, y]
     ```

     Captures are not stored in ordinary `fn_params`. Synthetic functions use
     a separate `fn_captures : list param`; ordinary `fn_params` remains the
     public call-argument list. `Eval_CallExpr` composes captured slots with
     ordinary arguments internally and now removes both internal frames before
     exposing the caller result store:
     first ordinary parameters, then hidden captures.
   - Direct `ECall` and `EFn` remain empty-capture only. Captured synthetic
     functions are constructed by `EMakeClosure` and called through
     `ECallExpr`.
   - Type the value as `unrestricted closure<'env>(Args) -> Ret` with an
     internally generated trivial `'env`. Reference-valued captures are
     deliberately deferred to Stage 7b.
   - Proof target: show that evaluating the closure literal produces a
     captured store satisfying `captured_store_typed` and
     `captured_call_frame_ready`, then prove `ECallExpr` preservation for this
     immutable-copy case.
   - The final-store mismatch must be handled by theorem shape, not by
     rewriting closure calls to direct calls. Treat the final `captured ++
     s_args` frame as internal to the closure call and expose only the caller
     output context/value promised by the ordinary typing rule.

   **Stage 7b: Captured reference values and closure lifetimes.**
   - Still no `closure [&x]` or `closure [&mut x]` syntax. This stage supports
     capturing variables whose values are already references.
   - Add the real `closure<'env>(Args) -> Ret` lifetime discipline:
     every captured `&'a T` requires `'a : 'env`, and the closure value may not
     escape `'env`.
   - Extend checker/elaboration evidence so lifetime inference introduces the
     internal closure environment lifetime outside the parser.
   - Extend captured-store readiness with lifetime validity/root reachability
     for captured references. Reuse root provenance only as sidecar evidence
     where reference safety needs it.

   **Stage 7c: Borrow-capture syntax.**
   - Add surface capture forms `closure [&x]` and `closure [&mut x]`.
   - The parser must only record the capture syntax. The elaborator/checker
     converts borrow captures into reference-valued captures and performs the
     borrow/lifetime checks.
   - Do not let parser desugaring insert ownership-sensitive operations. Any
     borrow creation, drop behavior, or root evidence belongs to the named
     elaboration/checker phase.

   **Stage 7d: Mutable unrestricted closure environments.**
   - Allow mutable unrestricted captured slots to be assigned/replaced inside
     the closure body.
   - A call that may update the captured environment requires a mutable
     closure place as receiver. The updated captured store is written back to
     the closure value after the call.
   - Copy-captured unrestricted variables remain independent from the outer
     variables. Updating the captured slot does not update the source variable;
     updating the outer variable requires a captured mutable reference.
   - Proof target: split immutable call preservation from mutable receiver call
     preservation. The mutable route must account for env writeback and prove
     that writeback preserves store typing, roots, no-shadow, and lifetime
     obligations.

   **Stage 7e: Affine and linear captures.**
   - Add move capture for affine/linear values only after immutable and mutable
     unrestricted closures are proved.
   - Captured closure values are usage-polymorphic like structs: compute the
     closure value's outer usage as the maximum usage of captured values.
     `closure_capture_usage` and `closure_value_ty` are the specification
     helpers for this shape. For polymorphic closure values, put the captured
     usage result on the outer `TForall` wrapper while keeping the inner `TFn`
     body shape unchanged.
   - Moving an affine/linear value into a closure is rejected when live
     references make the move invalid.
   - Consuming calls move the closure value and may consume captured affine or
     linear slots. The closure cannot be used after the call.
   - Proof target: add a consuming-call preservation theorem that accounts for
     callee evaluation effects instead of relying on the Stage 6a
     unrestricted-copy alias theorem.

   Existing proof assets to reuse:
   - `RuntimeTyping.v` already has `store_tys`, `sctx_of_store`,
     `captured_store_typed`, and `captured_closure_has_type`.
   - `TypeSafety.v` already has `captured_store_runtime_ready`,
     `captured_call_frame_ready`, `captured_call_frame_ready_compose`,
     `eval_call_body_cleanup_preserves_value_and_refs_frame`,
     `eval_captured_call_body_cleanup_preserves_value_and_refs`, and
     `eval_captured_call_expr_cleanup_preserves_value_and_refs`.
   - These helpers are proof infrastructure, not permission to widen the
     executable validators. Widen validators only after the matching Prop
     preservation theorem exists.

   Current implementation progress:
   - `Types.v` now has `TClosure env_lt params ret` as a separate type core
     from `TFn`. Lifetime substitution, lifetime mapping, bound-lifetime
     detection, type-parameter substitution, well-formedness, declaration
     equality, executable type equality, checker type depth, validation
     traversals, runtime lifetime-equivalence helpers, and extracted OCaml
     printers all handle `TClosure`.
   - Prop-level and executable `ty_compatible` now have the intended
     asymmetric callable relation: `TClosure` is compatible with `TClosure`,
     and captureless `TFn` is compatible where `TClosure` is expected. The
     reverse `TClosure`-as-`TFn` direction remains rejected.
   - `ECallExpr` typing/checking now accepts callees whose inferred type is
     `TClosure env_lt params ret`, with matching ordinary typing,
     env-structural typing, checker soundness, env-typing soundness, and
     alpha-renaming branches. This is only a callable-type bridge; it does not
     add closure literals, captured runtime environments, parser syntax, or
     validator/runtime theorem widening.
   - The hidden-capture design is now fixed and partially implemented:
     `fn_def` has `fn_captures` separately from ordinary `fn_params`, existing
     frontend functions elaborate with empty captures, and direct `EFn` /
     `ECall` typing, checking, and evaluation are guarded to empty-capture
     functions only.
   - Core-only `EMakeClosure fname captures` is implemented for immutable
     unrestricted reference-free captures. Rocq typing, env-structural typing,
     root/shadow typing, ordinary checker soundness, env checker soundness,
     borrow checker soundness, alpha-renaming, runtime evaluation, extraction,
     and FIR lowering all have coverage for this constructor.
   - `EMakeClosure` currently constructs `VClosure fname captured` by copying
     the listed captures. The executable capture checks require matching
     `fn_captures`, immutable bindings, unrestricted usage, no active mutable
     borrow of the captured root, and `ty_ref_free_b = true`.
   - Function-level validation now checks `fn_params ++ fn_captures` as one
     binding namespace: capture names and ordinary parameter names must be
     well-formed and duplicate-free. This prevents hidden captured frames from
     shadowing ordinary call frames.
   - Function bodies now use the capture-aware context
     `fn_body_ctx f := params_ctx (fn_params f ++ fn_captures f)`. The checker
     still keeps `fn_binding_params f := fn_params f ++ fn_captures f` for
     validation. The internal order is ordinary params first, hidden captures
     second, matching the existing runtime/proof frame shape for
     `bind_params (fn_params f) args (captured ++ caller_store)`. Direct `EFn`
     and direct `ECall` remain captureless.
   - The previous global `fn_body_ctx := params ++ captures` blocker is closed:
     direct-call preservation branches were factored into explicit helper
     lemmas, `callee_body_root_*_ready_at` now use `fn_body_ctx`, and
     captureless direct-call proofs convert back to params-only cleanup lemmas
     with the existing no-captures context conversion helpers.
   - Current bridge progress: `check_make_closure_captures_exact_ctx` and
     `check_make_closure_captures_exact_sctx` now exist as sidecar validators.
     They require each capture name to equal the corresponding hidden capture
     parameter name, each hidden capture parameter to be immutable, the captured
     binding state to be fresh, the binding to be
     immutable/unrestricted/reference-free, and the captured type to equal the
     hidden parameter type. Prop-level
     `captured_params_store_typed` and
     `captured_call_frame_params_ready` also exist, together with the basic
     lemma that types `captured ++ s_args` against
     `params_ctx fn_captures ++ Σ_args`.
   - The executable exact checker/copy-store bridge now exists at the sctx
     shape level: `check_make_closure_captures_exact_sctx_sound`,
     `copy_capture_store_exact_sctx_of_store`, and
     `copy_capture_store_exact_params_store_typed` prove that a successful exact
     sidecar check plus `copy_capture_store` turns the copied captured store
     into `captured_params_store_typed` for the hidden capture params.
   - Current cleanup progress: `eval_captured_call_body_cleanup_preserves_value_and_refs_params`
     and `eval_captured_call_expr_cleanup_preserves_value_and_refs_params`
     now expose the captured-call cleanup result against
     `sctx_of_ctx (params_ctx caps) ++ Σ_args` whenever
     `captured_call_frame_params_ready` is available.
   - Hidden-capture erasure is now reflected in both semantics and proof
     helpers. `Eval_CallExpr` returns
     `store_remove_params fn_captures (store_remove_params fn_params s_body)`,
     and `eval_captured_call_body_cleanup_preserves_value_and_refs_params_erased`
     shows that, for the exact immutable-copy capture frame, erasing hidden
     captures exposes the original caller argument store `Σ_args`. Direct
     `ECall` and syntactic `ECallExpr (EFn fname) args` proofs use the
     captureless alpha-renaming fact to simplify this new capture-removal step.
   - Function alpha-renaming now uses the stable-hidden-capture contract:
     `alpha_rename_fn_def` freshens only ordinary `fn_params`, keeps
     `fn_captures` unchanged, and includes capture names in the initial used set
     so ordinary renamed parameters cannot collide with hidden captures. The
     mixed context-alpha bridge for
     `params_ctx (fn_params f ++ fn_captures f)` is available at the
     alpha-renaming layer.
   - Captureless body-context conversion helpers now exist:
     `fn_body_ctx_eq_params_ctx_when_no_captures`,
     `typed_env_roots_fn_body_ctx_to_params_ctx_when_no_captures`, and
     `typed_env_roots_shadow_safe_fn_body_ctx_to_params_ctx_when_no_captures`.
   - Next closure proof task: add the separate captured-call preservation route
     over `fn_body_ctx fcall`, not the older params-only body context. This route
     should thread exact-capture evidence into captured callee-body readiness,
     prove the body under `params_ctx (fn_params fcall ++ fn_captures fcall)`,
     and then use the hidden-capture erasure helper to expose only the caller
     store/result promised by the ordinary `ECallExpr` typing rule.
   - Preservation/provenance readiness validators still reject
     `EMakeClosure`. Do not flip those booleans until captured `ECallExpr`
     preservation is proved. The next closure task is either parser/lambda
     lifting for Stage 7a surface syntax or the captured-call preservation
     bridge, depending on whether the project wants syntax first or theorem
     widening first.
8. **Handle the `if` root-environment gap last.**
   The known blocker is that ordinary `TES_If` does not expose
   `root_env_equiv R2 R3`, while root/shadow routes require it. Do not
   strengthen `TES_If` or ordinary checker acceptance just to manufacture this
   evidence.
9. **Treat initial readiness as a separate axis.**
   `initial_root_runtime_ready_for_fn` is about the starting store, not the
   accepted program. Reduce it only through an initial-store contract change or
   an executable initial-state validator such as `check_initial_root_runtime_ready`.

### Current Executable Endpoints

Use the endpoint names in `Codex Digest` first. Detailed public wrapper and
sidecar predicate names were moved to `plan/type_safety_endpoints.md`.

Current strongest executable runtime-safety endpoints:

```coq
check_program_env_alpha_validated_root_shadow_provenance_summary_big_step_safe_checked_initial_ready
check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary_big_step_safe_checked_initial_ready
```

Use the general provenance-summary route for ordinary non-direct-call validator
work. Use the direct-call-local route only for localized direct-call evidence.
Initial runtime readiness remains an execution-state check, currently via
`check_initial_root_runtime_ready`.

### Ordinary Checker Review Gates

`plan/review.md` is old, but its examples should stay as regression and proof
gates while the safety-validator route is widened to match the ordinary checker.

Already-fixed ordinary checker issues to preserve:

- Active-borrow access must be checked for ordinary reads/moves through `EVar`
  and `EPlace`, not only for `replace`, assignment, borrow, or dereference.
- Linear aggregate obligations must require every linear component path to be
  consumed; a single partial field move must not discharge the parent value.
- `&mut T` must be invariant in its referent type. Shared references may keep
  the intended compatible/covariant behavior, but unique references must not
  accept compatible-but-different inner types.
- Struct field mutability must be enforced for assignment and `replace`, not
  inferred only from the root binding mutability.
- Local type annotation lifetime elision must stay rejected until fresh local
  lifetime regions are designed.
- Generic trait syntax and validation must keep checking trait argument arity
  and bounds consistently.

Outstanding review-linked gates for the ordinary safety work:

- **Let-local reference escape.** The ordinary route must reject or prove safe
  examples shaped like `let r = let x = 1 in (&x); ...`. The current root-shadow
  safety route has initializer/body root exclusions, but that is sidecar
  evidence; the final ordinary checker theorem needs this handled by ordinary
  typing/checker facts or by an ordinary executable escape check.
- **Replace target self-use.** Existing path-state checks cover the direct
  self-move regression, but the final proof should make the intended rule
  explicit: while checking `replace p e_new`, `e_new` may not consume,
  overwrite, or borrow-conflict with `p` or a prefix/descendant of `p`. Add
  alias/borrow variants to the gap matrix if the current ordinary checker does
  not already reject them.
  Current implementation note: invalid fixtures now cover direct field
  self-use plus shared-borrow conflicts for replacing a root and a descendant
  field.

When reducing validator false negatives, rerun the relevant invalid fixtures
for these gates before treating a newly accepted syntax class as ordinary-safe.

### Do Not Do

- Do not strengthen `TES_If` or ordinary checker acceptance to satisfy
  root/shadow evidence.
- Do not restart full structural-to-shadow-root synthesis as the ordinary route.
- Do not make the root checker stricter than the ordinary checker to close a
  proof gap.
- Do not add an explicit `direct_call_callee_body_root_shadow_summary_bridge`
  premise to ordinary-facing statements; use `_of_unique`.

### Known Sidecar Gaps

- Ordinary checker success does not imply
  `env_fns_root_shadow_summary_evidence`.
- `check_program_env_alpha_validated` now implies `fn_env_unique_by_name` for
  the alpha-normalized environment.
- Ordinary checker success still does not imply `env_fns_preservation_ready`.
  The provenance-summary route no longer needs this for callee bodies, but the
  older split-validator route still uses it.
- The provenance-only direct-call bridge and final checked-initial wrapper now
  exist through `eval_preserves_typing_roots_ready_prefix_mutual`. The
  provenance-summary route no longer needs the caller
  `preservation_direct_call_ready_expr (fn_body f)` premise.
- The current executable safety validator is stricter than the ordinary checker.
  In particular, `preservation_ready_expr_b` currently rejects `ELet`,
  `ELetInfer`, `ECall`, `ECallExpr`, and `EDeref`.
- Direct `ECall` and syntactic `ECallExpr (EFn fname) args` should be handled
  by a localized direct-call sidecar package, not by mixing calls into ordinary
  expression readiness. The caller should use the direct-call-local readiness
  package, while only the reached callee body requires root-shadow provenance
  summary evidence.
- General `ECallExpr callee args` is staged future work. The first-class
  function-value stage proves that evaluating `callee` produces a function
  value carrying the concrete `fname` used to select the callee summary. The
  closure stages then add explicit capture-list syntax, lambda-lifted
  `EMakeClosure` core, immutable unrestricted captures, captured reference
  lifetimes, borrow-capture syntax, mutable environment writeback, and finally
  affine/linear move captures.
- `provenance_ready_expr_b` now accepts the narrow `EDeref (EBorrow rk p)`
  pattern with matching root provenance typing rules and runtime preservation
  cases. General `EDeref` remains outside the current validator route.
- The provenance-only root-shadow summary validator accepts the annotated and
  inferred ready-gap let examples that the preservation-ready root-shadow
  validator rejects, and it is now wired into the checked-initial operational
  safety theorem named in Current Endpoint.
- The abandoned synthesis route stops at `If`: `TES_If` lacks the
  `root_env_equiv R2 R3` evidence required by `TERS_If`.
- General root-checker-to-shadow-safe soundness is false for arbitrary core
  because source-level `let x = &x` initializer shadowing is valid before
  alpha-normalization.

## Archived Reference Material

Detailed completed-proof inventory was moved to
`plan/type_safety_roadmap_inventory.md`. Treat that file as reference only; do
not mine it for the next task unless the active roadmap explicitly points there.

Older milestone notes remain in `plan/type_safety_roadmap_history.md`, and
closure design details remain in `plan/closure.md`.

## Main Target Theorems

Long-term preservation target:

```coq
Theorem eval_preserves_typing :
  forall env Ω n Σ s e T Σ' s' v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e T Σ' ->
    eval env s e s' v ->
    store_typed env s' Σ' /\ value_has_type env s' v T.
```

Long-term ordinary-checker-to-runtime target:

```coq
Theorem infer_full_env_big_step_safe :
  forall env f T Γ' s s' v,
    ValidEnv env ->
    infer_full_env env f = infer_ok (T, Γ') ->
    initial_store_for_fn f s ->
    eval env s (fn_body f) s' v ->
    value_has_type env s' v (fn_ret f).
```

Runtime reference target:

```coq
Theorem eval_no_dangling_refs :
  forall env Ω n Σ s e T Σ' s' v,
    store_typed env s Σ ->
    typed_env_structural env Ω n Σ e T Σ' ->
    borrow_ok_env_structural env [] (ctx_of_sctx Σ) e [] ->
    eval env s e s' v ->
    refs_wf env s' v /\ store_refs_wf env s'.
```

Future small-step target:

```coq
Theorem step_progress :
  forall env Ω n Σ e T,
    store_typed env [] Σ ->
    typed_env_structural env Ω n Σ e T Σ ->
    terminal e \/ exists e' s', step env [] e s' e'.
```

`step_progress` must wait for `StepSemantics.v`.

## Sub-Agent Policy

Use sub-agents only after the design route is fixed and the task is
implementation-only.

Before spawning any sub-agent, state why the delegated task is
implementation-only. Example:

> This task is implementation-only because the canonical checker-safety route
> and target files are fixed; the worker is only reverting the temporary
> `roots_exclude x roots1` restriction and updating the corresponding tests.

Do not delegate:

- choosing between ordinary-checker safety and root-checker canonical safety
- deciding a new invariant
- comparing proof strategies
- investigating repository-wide design

Allowed delegation examples:

- reverting the known temporary root-checker restriction in fixed files
- updating focused regression tests after the expected behavior is fixed
- proving a named helper lemma whose statement and dependencies are already
  fixed by the main agent

## Required Checks

Before committing type-system work:

```sh
cd rocq && make
dune build
bash tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|Abort\.|DEBUG|idtac" rocq/theories
```

For roadmap-only edits, at minimum run:

```sh
git diff --check
```

The `rg` command exits with status 1 when no matches are found; that is
success.

## Commit Policy

After implementation and checks pass, commit with GPG signing disabled:

```sh
git commit --no-gpg-sign -m "<short imperative subject>"
```
