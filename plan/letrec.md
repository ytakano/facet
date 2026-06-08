# let rec Roadmap

## Status

In progress.

Done:

- Roadmap captured in this file.
- Baseline tests lock current top-level recursive function values.
- `rec` and `and` are reserved words in the OCaml frontend.
- Parser and named AST accept local `let rec` groups, including shared explicit
  capture lists.
- Raw AST includes `RawLetRec`; raw elaboration supports non-capturing
  groups and explicit-capture groups using synthetic function definitions.
- OCaml raw lowering keeps recursive function names separate from ordinary
  value scope and emits direct raw references/calls to local-rec ids.
- Rocq raw elaboration accepts non-capturing local rec groups and lowers them
  into synthetic no-capture function definitions plus direct calls.
- Local-rec raw lowering now emits reserved `__facet_local_rec_*` synthetic
  function names and rejects user top-level `__facet_*` names.
- Explicit-capture local rec groups lower rec references to closure values and
  reuse existing closure capture checking for non-recursive captured calls.
- FIR regression coverage locks synthetic local-rec function emission, direct
  calls, and captured closure construction/calls.
- The local direct-call route now has a bounded static-runtime named helper
  chain that threads `store_roots_within R s` from each argument root
  environment to the next. `preservation_ready_expr_static_runtime_named_statement`
  returns the updated `store_roots_within R' s`, and
  `typed_args_roots_preservation_ready_static_runtime_named` recurses from that
  evidence. A route-local singleton helper packages `[RStore x]` naming from
  store-name membership for later borrow/assign constructor proofs.
- The store-safe synthetic direct-call-ready summary can now be lowered back
  to the existing synthetic summary evidence and lifted through local-bounds
  environments, so later safety wrappers can keep the stronger store-safe data
  while reusing the older summary/bridge route where possible.
- Store-safe direct-call arguments are stable under alpha-renaming. The facts
  file now has both `store_safe_function_value_call_args_alpha_rename_exprs`
  for the named list helper and
  `store_safe_function_value_call_args_alpha_rename_call_go` for the local
  `fix go` shape used while normalizing synthetic `ECall` targets.
- Store-safe synthetic direct-call summary evidence can now be paired with the
  existing shadow synthetic-summary bridge to produce
  `direct_call_callee_body_root_synthetic_direct_call_ready_evidence`, via
  `direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge`.
- The route layer now has `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_named_bind_facts_core`, a store-safe variant of the synthetic direct-call cleanup bridge that derives readiness and argument named/key facts from `store_safe_function_value_call_args`.
- The env-runtime summary layer now wraps that store-safe cleanup bridge as
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_core`,
  consuming store-safe synthetic summary evidence plus the existing shadow
  summary bridge.
- The env-runtime summary layer now also has the final-roots store-safe wrapper
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_final_roots_core`,
  using store-safe argument facts for named/key preservation while reusing the
  existing result-subset bridge through summary conversion.
- The env-runtime summary layer now also has the frame/parameter scope
  store-safe cleanup wrapper
  `eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_cleanup`,
  completing the two exact-call cleanup projections needed for a store-safe
  package wrapper.
- Those store-safe exact-call projections are now packaged as
  `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement`,
  with constructor theorem
  `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_final_roots_and_cleanup`.
- `EnvRuntimeCapturedSafety.v` now has
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready`,
  proving a single no-capture direct-call component safe from the store-safe
  synthetic package and lifted summary bridge.
- The component safety theorem now has a concrete mutual-facts wrapper,
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_mutual`,
  which constructs the store-safe package and local-bounds bridge from the
  existing direct-call route proof interfaces.
- The checker sidecar layer now has an OR summary for existing captured-call
  store-safe summaries or no-capture direct-call components:
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary`,
  with Prop-level readiness and soundness lemmas.
- Captured-call store-safe safety is factored into the function-level
  `callee_body_root_shadow_captured_call_store_safe_summary_big_step_safe_checked_initial_ready`
  plus the existing env-level wrapper.
- The combined captured/store-safe-or-direct-component sidecar now has an
  env-level safety theorem,
  `env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_mutual`,
  which dispatches old captured-call summaries through the factored theorem and
  no-capture direct components through the store-safe synthetic route.
- There is also a conservative checker-level wrapper,
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_mutual`,
  which combines the OR sidecar checker with the existing whole-env no-capture
  component checker to supply store-safe synthetic evidence.
- A narrower wrapper,
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_synthetic_route`,
  now instantiates the six ordinary mutual preservation facts internally. The
  remaining open inputs for the component branch are the two recursive synthetic
  direct-call route statements:
  `eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement` and
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement`.
- `End2EndSafety.v` now derives the combined OR sidecar from the current old
  end-to-end gate via `infer_fn_env_end2end_combined_gate` and
  `infer_fns_env_end2end_combined_check_env_ready`, without changing checker
  behavior yet.
- `TypeSafetyDirectCallRoute.v` now has a non-circular exact-call helper,
  `eval_synthetic_direct_call_body_cleanup_prefix_package_from_call_statement_ready_evidence`,
  plus `direct_call_target_expr_same_is_call`. The helper reuses the
  call-statement preservation route for synthetic bodies already normalized to
  `ECall`, avoiding the full recursive synthetic route premise in that case.
- The exact-call helper is now lifted through scope cleanup by
  `eval_synthetic_direct_call_body_cleanup_prefix_from_call_statement_ready_evidence`
  and through the top-level `ECall` cleanup bridge by
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_core`.
  This reduces the remaining prefix-side cycle from the full synthetic route
  statement to the direct-call call-statement premise.
- The call-statement premise reduction now reaches the named-bind and store-safe
  bridge layers via
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_named_bind_facts_core`
  and
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_named_bind_facts_core`.
- The store-safe summary bridge now also has a call-statement-premise variant,
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_summary_bridge_core`,
  so env-level store-safe synthetic summary evidence can use the reduced prefix
  route at the non-final-roots bridge layer.
- The result-subset cleanup path and final-roots summary bridge now have
  call-statement-premise variants:
  `eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_call_statement_evidence`
  and
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_summary_bridge_final_roots_core`.
- The frame/parameter-scope exact-call cleanup path now also has
  call-statement-premise variants:
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_cleanup`
  and
  `eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_cleanup`.
- The store-safe exact-call package can now be built from the reduced
  call-statement premise via
  `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_call_statement_final_roots_and_cleanup`.
- Combined captured/no-capture component safety now has call-statement-route
  wrappers, ending at
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_call_statement_synthetic_route`.
- Store-safe exact-call packaging now has a two-sided call-statement route
  variant,
  `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_call_statement_routes_final_roots_and_cleanup`,
  reducing both prefix and frame/parameter-scope route premises.
- Combined component safety now also has a two-sided call-statement-route
  wrapper,
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_call_statement_routes`.
- End-to-end safety now has a bridge theorem for call-statement routes plus
  the current component sidecar check:
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check`.
- Component evidence localization has started with the per-function checker
  bridge
  `check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary`
  and the combined-branch extractor
  `check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_store_safe_synthetic_direct_call_ready_summary_when_not_captured`.
- The two concrete call-statement route premises can now be packaged as
  `eval_preserves_synthetic_direct_call_ready_call_routes_statement`, bridged to
  summary-bridge narrow-core helpers via
  `eval_preserves_synthetic_direct_call_ready_summary_call_package_statement_of_call_routes`,
  and lifted directly to summary-bridge preservation with
  `eval_preserves_synthetic_direct_call_ready_with_summary_bridge_narrow_core_of_call_statement_routes`.
- The direct-call route proof now factors bind-parameter inputs through
  `eval_call_bind_params_route_inputs_from_components`.
- Shadow synthetic direct-call-ready summary evidence now lifts through
  `global_env_with_local_bounds` in `TypeSafetyDirectCallEvidenceFacts.v` via
  `callee_body_root_shadow_synthetic_direct_call_ready_summary_global_env_with_local_bounds`
  and
  `env_fns_root_shadow_synthetic_direct_call_ready_summary_evidence_global_env_with_local_bounds`;
  the route layer reuses those shared facts instead of local duplicates.
- The route layer now has
  `direct_call_callee_body_root_synthetic_direct_call_ready_evidence_global_env_with_local_bounds_of_shadow_summary`,
  factoring reconstruction of body-env raw synthetic direct-call evidence from
  shadow summary evidence plus the existing summary bridge.
- The route layer also packages top-level and body-env raw synthetic
  direct-call evidence as
  `direct_call_callee_body_root_synthetic_direct_call_ready_evidence_package_of_shadow_summary`.
- Summary bridge route wrappers now consume that evidence package directly,
  keeping top-level and body-env recursive-call evidence in sync.
- Store-safe exact-call packaging can now be derived from the plain summary
  exact-call package via
  `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_plain_summary_exact_package`.
- No-capture direct-call component safety can now consume a plain summary
  exact-call package through
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package`.
- Combined captured-or-direct-component env safety can now consume the plain
  summary exact-call package via
  `env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package`.
- The checker-level combined sidecar safety wrapper can now consume the plain
  summary exact-call package via
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package`.
- End-to-end safety now has a bridge from a plain summary exact-call package
  plus the component sidecar check via
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_check`.
- End-to-end safety can now consume the plain summary call package via
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_check`.
- The summary exact-call package now has prefix/scope projection helpers:
  `eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_prefix`
  and `eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_scope`.
- The summary exact-call package now also has the explicit constructor helper
  `eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_exact_statements`.
- The checker-level summary exact-package wrapper now has a variant that takes
  `env_fns_root_shadow_store_safe_synthetic_direct_call_ready_summary_evidence`
  directly,
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_store_safe_summary_evidence`,
  isolating the replacement point for the old whole-env component check.
- Component safety can now consume store-safe synthetic summary evidence scoped to
  the component's `body_env` via
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_store_safe_summary_evidence`,
  instead of requiring top-level whole-env evidence and lifting it internally.
- The summary exact-package component wrapper now also has a body-env evidence
  variant,
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_body_store_safe_summary_evidence`.
- Env-level and checker-level summary exact-package wrappers can now take a
  direct-component-only body-env store-safe summary provider via
  `env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence`
  and
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_store_safe_summary_evidence`.
- End-to-end safety now has the matching summary exact-package bridge
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_store_safe_summary_evidence`,
  so the old whole-env component check has a single remaining replacement point:
  construction of the direct-component body-env store-safe summary provider.
- End-to-end safety also has the matching summary call-package bridge
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_body_store_safe_summary_evidence`.
- The direct-component body-env store-safe summary provider is now named as
  `component_body_store_safe_synthetic_direct_call_ready_summary_provider`,
  and the env/checker/end-to-end wrappers consume that named Prop instead of an
  inline forall.
- Existing whole-env no-capture component readiness/checks can now construct the
  named provider via
  `component_body_store_safe_synthetic_direct_call_ready_summary_provider_of_no_capture_direct_call_component_ready`
  and
  `check_env_root_shadow_no_capture_direct_call_component_store_safe_summary_component_body_store_safe_provider`.
- Existing whole-env store-safe synthetic summary evidence can also construct
  the named provider via
  `component_body_store_safe_synthetic_direct_call_ready_summary_provider_of_store_safe_summary_evidence`.
- The plain body-env synthetic summary provider is now named as
  `component_body_synthetic_direct_call_ready_summary_provider`, with conversion
  helpers from store-safe providers and whole-env plain summary evidence.
- Component safety now has plain body-summary evidence wrappers,
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_evidence`
  and
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_body_summary_evidence`,
  avoiding the store-safe exact-package conversion on that route.
- Env/checker/end-to-end safety now also has plain component-body summary
  evidence wrappers,
  `env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_summary_evidence`,
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_exact_package_with_component_body_summary_evidence`,
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_body_summary_evidence`,
  and
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_call_package_and_component_body_summary_evidence`.
- A visited-set/fuel based direct-call component closure checker now exists as
  `check_fn_root_shadow_no_capture_direct_call_component_closure_seen` and
  `check_fn_root_shadow_no_capture_direct_call_component_closure`, with head
  and callee soundness facts for the checker route.
- The checker now also has a captured-or-direct-component-closure gate,
  `check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary`
  and
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_closure_summary`,
  with soundness back to the existing combined readiness Prop.
- Direct-call evidence now has a pointwise summary-evidence form,
  `fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at`, plus an
  env-wide projection lemma. This is the replacement point for package variants
  that should consume only the current `ECall` target instead of all `env_fns`.
- The direct-call bridge now has a pointwise exact helper,
  `direct_call_callee_body_root_shadow_synthetic_direct_call_ready_summary_bridge_of_summary_with_preservation_core`,
  derived from the existing result-subset helper and a result-subset-to-ready
  conversion.
- The direct-call route now has a pointwise result-subset helper,
  `callee_body_root_shadow_synthetic_direct_call_ready_result_subset_from_summary_at`,
  mirroring the env-wide helper but consuming only the current call target's
  summary evidence.
- Current-call direct-call ready evidence is now named as
  `direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at`, with
  `direct_call_callee_body_root_synthetic_direct_call_ready_evidence_at_of_shadow_summary_at`
  deriving it from pointwise shadow summary evidence.
- The direct-call route now has current-call evidence variants for body and
  scope setup:
  `eval_synthetic_direct_call_body_from_ready_evidence_at`,
  `eval_synthetic_direct_call_body_scope_inputs_from_ready_evidence_at`, and
  `eval_synthetic_direct_call_body_scope_callback_from_ready_evidence_at`.
- The typing-roots exact-call route now has a pointwise current-target variant,
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_at_final_roots_core`,
  plus the statement wrapper
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_exact_call_statement_of_final_roots_bridge`.
- The frame/scope exact-call route and package now have pointwise current-target
  variants:
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_exact_call_statement_of_cleanup`
  and
  `eval_preserves_synthetic_direct_call_ready_summary_at_exact_call_package_statement_of_cleanup`.
- Component safety can now consume the pointwise exact-call package through
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_evidence`,
  taking only the component body's direct target summary plus an explicit
  recursive body-env evidence route.
- Component-body pointwise summary evidence is now named as
  `component_body_synthetic_direct_call_ready_summary_at_provider`, with
  compatibility helpers from env-wide summary evidence and the older env-wide
  component-body provider.
- Component-body recursive-call evidence is now named as
  `component_body_synthetic_direct_call_ready_body_env_evidence_provider`, and
  env/checker safety wrappers can consume it together with the pointwise summary
  provider via the `...summary_at_exact_package_with_component_body_summary_at_evidence`
  theorems.
- The new body-env evidence provider has compatibility constructors from
  env-wide summary evidence and the older component-body env-wide summary
  provider, keeping the pointwise route connected to existing wrappers.
- End-to-end safety can now consume the pointwise exact-call package plus the
  pointwise component-body providers via
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_exact_package_and_component_body_summary_at_evidence`.
- In-aware component provider variants now exist for closure-derived evidence:
  `component_body_synthetic_direct_call_ready_summary_at_in_provider` and
  `component_body_synthetic_direct_call_ready_body_env_evidence_in_provider`,
  with compatibility helpers from the earlier provider forms.
- Env/checker/end-to-end safety now also has In-aware pointwise provider
  wrappers via the `...component_body_summary_at_in_evidence` theorem family.
- The closure checker can now construct the In-aware current-target pointwise
  summary provider through
  `component_body_synthetic_direct_call_ready_summary_at_in_provider_of_closure_check_provider`.
  The proof handles self-cycles by using the component's `In` evidence plus
  `fn_env_unique_by_name`, and handles fresh callees via the closure checker's
  callee/head soundness facts.
- `TypeSafetyDirectCallRoute.v` now names the missing pointwise prefix-call
  interface as
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement`
  and packages it with the pointwise scope route as
  `eval_preserves_synthetic_direct_call_ready_summary_at_call_package_statement`.
  This records the route shape needed for recursive body cleanup, where only
  `store_typed_prefix` is available.
- The callee-body cleanup helper now has a pointwise call-route variant,
  `eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_summary_at_call_statement_evidence`,
  which consumes summary evidence for the body's concrete synthetic `ECall`
  target and a nested body-env evidence callback.
- The final-roots summary-at cleanup bridge now has a pointwise call-route
  variant,
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_at_call_route_final_roots_core`,
  threading body-target summary callbacks and nested body-env evidence callbacks
  into the new cleanup helper.
- The frame/scope summary-at route now has the matching pointwise call-route
  statement and wrapper,
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_call_statement`
  and
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_call_statement_of_cleanup`.
  The two pointwise call routes are packaged as
  `eval_preserves_synthetic_direct_call_ready_summary_at_pointwise_call_package_statement`.
- Recursive body-target providers are now named separately as
  `component_body_synthetic_direct_call_ready_nested_summary_at_in_provider`
  and
  `component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider`,
  matching the extra callbacks required by the pointwise call package for
  alpha-renamed callee bodies.
- Component-level direct-call safety can now consume the pointwise call-route
  final-roots core directly via
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_call_route_evidence`,
  taking the component body's target summary, one nested target-summary
  callback, and one nested body-env evidence callback.
- Env/checker safety now has pointwise call-route wrappers,
  `env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_call_route_with_component_body_nested_in_evidence`
  and
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_call_route_with_component_body_nested_in_evidence`,
  consuming the In-aware current-target provider plus the nested body providers.
- End-to-end safety now has the matching pointwise call-route bridge
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_call_route_and_component_body_nested_in_evidence`.
- Nested body-target providers now have compatibility constructors from env-wide
  summary evidence and from the older component-body summary provider:
  `component_body_synthetic_direct_call_ready_nested_summary_at_in_provider_of_summary_evidence`,
  `component_body_synthetic_direct_call_ready_nested_summary_at_in_provider_of_provider`,
  `component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider_of_summary_evidence`,
  and
  `component_body_synthetic_direct_call_ready_nested_body_env_evidence_in_provider_of_provider`.
- The new end-to-end pointwise call-route bridge can now be closed from the
  older component-body summary provider via
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_call_route_and_component_body_summary_provider`.
- Closure-scoped nested provider Props now exist for recursive body callbacks
  that are known to be on the direct-call component chain:
  `component_body_synthetic_direct_call_ready_closure_nested_summary_at_in_provider`
  and
  `component_body_synthetic_direct_call_ready_closure_nested_body_env_evidence_in_provider`,
  with compatibility helpers from the wider nested provider forms.
- The closure checker can now also produce current-target direct-call component
  evidence via
  `component_body_no_capture_direct_call_component_target_in_provider_of_closure_check_provider`,
  preserving the component-summary fact that the pointwise route needs before
  alpha-renamed body cleanup.

Next:

- Thread current-target component evidence through the pointwise call-route
  wrappers so closure-scoped nested providers can replace the wider nested
  providers.
- Once the closure-scoped providers feed the component safety wrapper, switch
  `infer_fn_env_end2end` / `infer_fns_env_end2end` from the old captured
  store-safe sidecar to the captured-or-component-closure sidecar and update the
  unconditional end-to-end safety theorem accordingly.
- Move the direct recursion invalid tests to valid tests once the extracted
  end-to-end checker accepts direct self-recursion and mutual recursion.

This roadmap adds local recursion in stages, ending with a safe v1 for
explicit-capture recursive closures. The first implementation should avoid a
new core `ELetRec` expression. Surface `let rec` should be lowered through raw
elaboration into synthetic `fn_def`s plus the existing callable forms:

- `EFn` / `ECall` for non-capturing recursive functions.
- `EMakeClosure` / `ECallExpr` for explicit-capture recursive closures.

The Rocq definitions and extracted checker remain the source of truth. The
OCaml parser and de Bruijn conversion may represent the surface syntax, but
must not duplicate type-checking logic or add fallback acceptance paths.

## Surface Syntax

Use an `fn`-like local group syntax:

```facet
let rec f(x: T) -> R {
  body
}
and g(x: T) -> R {
  body
}
in expr
```

For captured recursive closures, use one explicit capture list shared by the
whole group:

```facet
let rec [c1, c2]
  f(x: T) -> R {
    body
  }
and
  g(x: T) -> R {
    body
  }
in expr
```

V1 restrictions:

- Each recursive item is a function with explicit parameter and return types.
- Recursive non-function values are rejected.
- Local-rec generics and `where` clauses are rejected.
- Per-function capture lists are rejected; the group has one capture list.
- Captures are explicit. A rec body may not use an outer local variable unless
  it appears in the group capture list.
- Captured-rec v1 supports only the current safe closure capture discipline:
  immutable, unconsumed, unrestricted captures that are ref-free, or shared
  references whose lifetimes outlive the closure environment.
- Mutable captures, unique-reference captures, affine captures, linear
  captures, borrow-capture syntax, mutable environment write-back, and
  consuming closure calls are future work.

## Semantics

Top-level function self-recursion and mutual recursion are intended behavior.
Global raw elaboration already installs function stubs before checking bodies;
tests should lock this down before local `let rec` is added.

For a local non-capturing rec group:

- Allocate a fresh synthetic `fn_def` name for each local rec function.
- Type-check every body in an environment containing stubs for all synthetic
  functions in the group.
- Inside the group body and the `in` expression, references to rec names lower
  to `EFn synthetic`; calls lower to `ECall synthetic args`.
- The generated function values have ordinary unrestricted `fn(...) -> ...`
  types.
- Local value bindings and parameters shadow rec function names in the normal
  lexical order.
- The synthetic names are lexical implementation details and are not
  source-callable outside the `let rec` expression.

For an explicit-capture recursive closure group:

- Use `closure_elab_capture_params` to compute the shared `fn_captures` for
  each synthetic function.
- Type-check each synthetic body under `params_ctx (captures ++ params)`, as
  current closure elaboration does.
- Inside the group body and the `in` expression, references to rec names lower
  to `EMakeClosure synthetic captures`; calls lower to
  `ECallExpr (EMakeClosure synthetic captures) args`.
- Recursive calls rebuild closure values from the current captured frame rather
  than constructing cyclic runtime closure values.
- Runtime behavior reuses existing captured-call semantics:
  `copy_capture_store_as`, hidden captured frames, argument binding, callee
  alpha-renaming, and cleanup via `store_remove_params`.

## Implementation Steps

1. Baseline tests and direct-call gate.
   - Done: add valid tests for top-level recursive function values.
   - Next: add valid tests for direct top-level self-recursion and mutual
     recursion, then extend the store-safe sidecar so those no-capture direct
     calls pass the extracted end-to-end checker.
   - Keep direct top-level recursion no-capture only.

2. Parser and named AST.
   - Done: reserve `rec` and `and` in the lexer/parser token set.
   - Done: add a named AST node for local recursive groups with optional shared
     capture list, function names, params, returns, and bodies.
   - Done: update grammar printing to include both non-capturing and capturing
     forms.
   - Done: parser validation remains syntactic; semantic checks stay in
     de Bruijn validation, raw elaboration, and the extracted checker.

3. Name resolution and raw AST.
   - Done: add raw `RawLetRec captures rec_fns body` and lower parsed groups
     to it.
   - Done: de Bruijn conversion assigns stable source idents to rec function
     names and rejects duplicate names in the group.
   - Maintain a local rec-name environment separate from ordinary value scope
     so that calls can lower differently from normal variables.
   - When an ordinary local binding or parameter shadows a rec name, resolve to
     the ordinary value first.
   - Done: make OCaml raw lowering distinguish recursive function names from
     ordinary values.
   - Done: implement raw elaboration for non-capturing rec groups.
   - Done: make generated local-rec function names collision-proof against
     user top-level names and sibling/nested local rec groups.
   - Next: enable recursive bodies after the direct-call safety gate accepts
     recursion.
   - For non-capturing groups, lower rec references to direct function items.
     For captured groups, lower rec references to closure construction using
     the shared capture ids.

4. Rocq raw elaboration.
   - Done: `CheckerRawElab.v` has `RawLetRec` and allocates all synthetic
     names before checking any body.
   - Done: group stubs are appended before body elaboration so the group is
     in scope while each rec body is elaborated.
   - Done: `[]` captures create no-capture `MkFnDef` entries and use the
     existing full-env path.
   - Done: non-empty captures reuse closure capture checking and create one
     captured synthetic `fn_def` per rec function.
   - Done: the `in` expression elaborates with completed synthetic functions
     available and returns the synthetic functions as extras.

5. Checker, typing, borrow, and safety alignment.
   - Prefer reusing existing `EFn`, `ECall`, `EMakeClosure`, and `ECallExpr`
     typing/checker rules. Do not add a new core typing rule unless raw
     elaboration proves insufficient.
   - Done: non-recursive local-rec call sites reuse the existing extracted
     checker authority; no OCaml fallback checker was added.
   - Next: replace the current acyclic direct-call store-safe sidecar with a
     verified recursive-call graph summary, or another proof structure that can
     justify self/mutual direct-call cycles without depending on finite fuel
     unfolding of the same cycle. Split this proof work into three small
     commits: boolean checker summary for no-capture direct-call components,
     soundness from the boolean summary to the Prop summary, then the big-step
     safety theorem change that uses evaluation induction for direct calls.
   - Done: add the no-capture direct-call component boolean summary in
     `CheckerRootSidecars.v`; it is intentionally not connected to the
     end-to-end gate until the Prop soundness and safety theorem work lands.
   - Done: prove the boolean no-capture direct-call component summary sound
     against a matching Prop summary in `EnvRuntimeCapturedCallSummaryFacts.v`;
     it is still intentionally not wired into the gate.
   - Done: add the env-level ready lemma for that component summary, preparing
     the later gate connection without changing current accept/reject behavior.
   - Done: add local-bounds lifting for the no-capture direct-call component
     summary, matching the existing summary lifting style.
   - Done: add a helper extracting direct-call readiness for the synthetic
     direct-call body from the no-capture component summary.
   - Done: add an env-level synthetic direct-call-ready invariant derived from
     the no-capture component summary.
   - Done: add a no-env-ready direct-call route wrapper, so recursive
     direct-call components no longer need the whole environment to satisfy
     `env_fns_preservation_ready` before entering the existing direct-call route.
   - Done: factor evaluation normalization for `direct_call_target_expr`, so
     raw `ECall` and `ECallExpr (EFn ...)` bodies can share the synthetic
     `ECall` route in later recursive-component proofs.
   - Done: add direct-call-ready callee evidence definitions, root/shadow
     summary bridges, and conversion lemmas alongside the older
     preservation-ready evidence.
   - Done: add env-level direct-call-ready summary evidence and conversions from
     the older shadow summary evidence.
   - Done: add synthetic direct-call-ready callee evidence definitions for
     normalized `ECall` target bodies.
   - Done: bridge the no-capture direct-call component summary to env-level
     synthetic direct-call-ready shadow evidence; no gates are wired yet.
   - Done: add a compatibility direct-call route wrapper that accepts synthetic
     direct-call-ready evidence alongside the older body-ready evidence, without
     changing current gate behavior.
   - Done: add alpha-renaming shape evidence for `direct_call_target_expr`, so
     component summaries can be transported to alpha-renamed call bodies.
   - Done: add fn-body alpha-renaming preservation for direct-call-ready
     expressions.
   - Done: add constructors from synthetic direct-call-ready summary bridges to
     synthetic direct-call-ready evidence.
   - Done: prove the call-time bridge from env-level synthetic direct-call-ready
     shadow summaries to alpha-renamed call bodies; no gates are wired yet.
   - Done: add proof-interface statements for the recursive synthetic
     direct-call-ready route, including the roots/shadow result needed by
     parameter cleanup.
   - Done: add a route helper that uses synthetic direct-call-ready evidence
     to normalize an alpha-renamed callee body evaluation to the typed
     synthetic `ECall` target.
   - Done: add direct-call body cleanup helpers that run the synthetic
     direct-call-ready route for the normalized body and expose cleanup results
     once frame/parameter scope facts are supplied; no gates are wired yet.
   - Done: package the scope-start inputs for normalized synthetic direct-call
     bodies: typed target, body-env evaluation, call-parameter root coverage,
     argument value typing, and initial frame/parameter scope facts.
   - Done: add a direct-call-ready frame/parameter scope preservation
     statement and a callback helper that feeds normalized synthetic `ECall`
     scope results into the synthetic cleanup path; no gates are wired yet.
   - Done: add an `ECall` cleanup bridge for the recursive synthetic
     direct-call route. It destructs the outer direct call, invokes the
     synthetic typing/roots route and synthetic scope callback, and returns the
     outer store typing, value typing, ref preservation, final roots/shadow
     facts, plus the callee-body value-root witness. It is intentionally still
     a bridge: local-bounds synthetic evidence, bind-param named/key facts, and
     the final outer `value_roots_within roots` projection remain explicit
     premises at this layer.
   - Done: add a wrapper around that bridge which derives the bind-param
     named/key facts from the standard typing, roots, root-name, and root-key
     preservation packages.
   - Done: add the prefix-store synthetic direct-call-ready route interface and
     route the synthetic `ECall` cleanup bridge through prefix bind-param store
     typing, removing the exact bind-param body typing premise.
   - Done: add a summary/bridge wrapper around the synthetic `ECall` cleanup
     bridge that derives both env-level and local-bounds synthetic callee-body
     evidence from synthetic shadow summary evidence, its bridge, and the
     existing root-name/root-key preservation packages.
   - Done: add synthetic direct-call-ready result-subset evidence and a
     call-time bridge from synthetic shadow summaries to
     `root_set_stores_subset roots_body (root_sets_union arg_roots)`, mirroring
     the provenance result-subset path. Also add the route-side wrapper that
     derives this result-subset evidence from env-level synthetic summaries.
   - Done: thread result-subset evidence through the synthetic `ECall`
     cleanup bridge via a result-subset cleanup package, so the cleanup witness
     and subset proof share the same `roots_body`; add the final-roots summary
     wrapper that discharges the outer `value_roots_within roots v` projection.
   - Done: connect the final-roots synthetic `ECall` cleanup bridge to a
     full recursive direct-call route theorem over synthetic direct-call-ready
     evidence. The theorem handles both direct-call-ready constructors:
     provenance/root preservation for `PDCR_Ready`, and the synthetic summary
     bridge plus final-roots cleanup path for `PDCR_Call`.
   - Done: split the two broad proof-interface assumptions used by that route
     into concrete wrappers. Existing provenance-ready mutual packages now
     discharge the non-call branch of
     `eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_statement`
     and
     `eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement`;
     the route can use the narrower `ECall`-only prefix and frame/parameter
     scope obligations through
     `eval_preserves_typing_roots_synthetic_direct_call_ready_with_summary_bridge_narrow_core`.
   - Done: add summary/bridge-specific direct-`ECall` proof interfaces:
     `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement`
     exposes the final-roots cleanup bridge with prefix result shape via
     `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_prefix_call_statement_of_final_roots_bridge`,
     and
     `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_call_statement`
     is threaded through
     `eval_preserves_frame_param_scope_synthetic_direct_call_ready_with_summary_bridge_narrow_core`.
   - Done: prove the summary/bridge direct-`ECall` frame/parameter scope
     preservation path using the synthetic cleanup result. The summary call
     scope interface now carries the store typing and root-name/key facts
     required by the cleanup and summary-bridge evidence.
   - Done: package the summary/bridge direct-`ECall` prefix
     preservation and frame/parameter scope obligations into
     `eval_preserves_synthetic_direct_call_ready_summary_call_package_statement`,
     with projection lemmas and package-based narrow route wrappers. This gives
     future recursive proofs a single combined obligation instead of two
     separately circular obligations.
   - Done: split the summary/bridge direct-`ECall` package into prefix-friendly
     obligations for recursive/IH use and exact-store helper obligations for the
     existing cleanup bridge. The public package
     `eval_preserves_synthetic_direct_call_ready_summary_call_package_statement`
     now starts from `store_typed_prefix env s Σ`, while exact callers can use
     `eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_prefix`
     and the per-obligation exact wrappers.
   - Done: keep the concrete cleanup combiner as the exact-store helper
     `eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_final_roots_and_cleanup`;
     this documents that the currently reused root-name/key and argument
     preservation packages still require exact `store_typed` at the outer call.
   - Done: add the package-narrow exact-entry bridge
     `eval_preserves_synthetic_direct_call_ready_summary_exact_call_package_statement_of_package_narrow_core`.
     This proves the two exact-store direct-`ECall` package halves from the
     package-based narrow route theorem and a recursive package assumption,
     giving exact callers a small reusable constructor-level bridge without
     duplicating the cleanup proof.
   - Done: add the prefix-store argument named/key helper
     `eval_args_preserves_root_names_keys_ready_prefix_ctx`. It derives
     `Forall (fun roots => root_set_store_roots_named roots s_args) arg_roots`
     and `root_env_store_keys_named R_args s_args` for direct-call argument
     evaluation from `store_typed_prefix`, prefix preservation, and ctx-level
     `root_env_ctx_roots_named` / `root_env_ctx_keys_named`, without invoking
     the exact-store root-name/key mutual preservation packages.
   - Done: add a store-safe synthetic direct-call-ready summary/evidence
     variant that retains `store_safe_function_value_call_args env args` for
     the normalized direct `ECall` target, plus conversions from the existing
     no-capture component store-safe summary.
   - Done: add conversions from the store-safe synthetic summary back to the
     existing synthetic summary evidence, plus local-bounds lifting for the
     store-safe variant. This lets later wrappers carry the stronger
     `store_safe_function_value_call_args` fact without forking every older
     summary bridge immediately.
   - Done: add the bounded runtime-store-name preservation helper
     `eval_args_preserves_root_names_keys_preservation_ready_runtime_with_static_expr`.
     It transports argument root/name facts across `eval_args` using
     `preservation_ready_eval_store_names_mutual`, without requiring exact
     `store_typed`. The helper factors the remaining proof obligation into
     `preservation_ready_expr_static_runtime_named_statement`, an expression
     static-runtime named/key premise over `typed_env_roots`.
   - Done: add route-local runtime named/key building blocks and the compiled
     leaf-constructor theorem
     `preservation_ready_expr_static_runtime_named_leaf_complete`. It closes the
     expression-level static runtime named/key obligation for `EUnit`, `ELit`,
     `EVar`, `EFn`, and direct `EPlace` using only runtime root-env named/key
     facts, plus the no-shadow invariant already available in the direct-call
     route.
   - Done: add
     `direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_store_safe_shadow_summary_bridge`,
     which combines store-safe synthetic direct-call summary evidence with the
     existing shadow synthetic-summary bridge to produce the synthetic
     direct-call-ready callee evidence required by the recursive route.
   - Done: add the env-runtime wrapper
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_core`,
     so store-safe synthetic summary evidence can invoke the store-safe cleanup
     bridge without exposing ctx-based argument named/key derivations at the
     wrapper boundary.
   - Done: add the final-roots and frame/parameter scope store-safe
     cleanup wrappers
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_bridge_final_roots_core`
     and
     `eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_cleanup`.
     These close the two exact-call projections over store-safe synthetic
     summary evidence.
   - Done: package those exact-call projections as
     `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement`
     and prove
     `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_final_roots_and_cleanup`.
   - Done: add
     `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready`,
     which applies the store-safe synthetic package to one no-capture direct-call
     component under a local-bounds body environment.
   - Done: add the concrete mutual-facts wrapper
     `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_of_mutual`,
     so callers can provide the existing direct-call route interfaces instead of
     prebuilt package/bridge evidence.
   - Done: add the non-invasive OR checker sidecar
     `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary`
     and its soundness/ready lemmas. This prepares an end-to-end gate switch
     without changing the existing checker authority yet.
   - Done: add
     `env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_mutual`,
     which dispatches the combined sidecar branch-by-branch.
   - Done: add the conservative checker-level wrapper
     `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_mutual`,
     which uses the whole-env no-capture component checker as a temporary source
     of store-safe synthetic evidence.
   - Done: add
     `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_synthetic_route`,
     which closes the six ordinary mutual preservation premises internally and
     leaves only the two recursive synthetic direct-call route statements as
     explicit inputs.
   - Done: add exact-call route helpers
     `eval_synthetic_direct_call_body_cleanup_prefix_package_from_call_statement_ready_evidence`,
     `eval_synthetic_direct_call_body_cleanup_prefix_from_call_statement_ready_evidence`,
     and
     `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_core`.
     These factor the prefix-side recursive route so the cleanup bridge can use
     the direct-call call-statement premise instead of the full recursive
     synthetic route statement.
   - Done: lift the same call-statement premise reduction through named-bind
     and store-safe bridge wrappers with
     `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_named_bind_facts_core`
     and
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_named_bind_facts_core`.
   - Done: add the env-summary bridge wrapper
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_summary_bridge_core`,
     carrying the reduced call-statement premise through store-safe synthetic
     summary evidence.
   - Done: add
     `eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_call_statement_evidence`
     and
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_call_statement_summary_bridge_final_roots_core`,
     carrying the reduced call-statement premise through result-subset cleanup
     and final-roots preservation.
   - Done: add scope-side call-statement cleanup variants
     `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_cleanup`
     and
     `eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_cleanup`,
     carrying the reduced call-statement premise through frame/parameter scope
     exact-call cleanup.
   - Done: add store-safe exact-call package wrapper
     `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_call_statement_final_roots_and_cleanup`,
     combining the call-statement final-roots and scope cleanup projections.
   - Done: add call-statement-route safety wrappers through the combined
     captured/no-capture component path, ending at
     `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_call_statement_synthetic_route`.
   - Done: add scope-premise call-statement route variants
     `eval_synthetic_direct_call_body_scope_callback_from_call_statement_ready_evidence`,
     `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_routes_cleanup`,
     `eval_preserves_frame_param_scope_store_safe_synthetic_direct_call_ready_summary_exact_call_statement_of_call_statement_routes_cleanup`,
     and
     `eval_preserves_synthetic_direct_call_ready_store_safe_summary_exact_call_package_statement_of_call_statement_routes_final_roots_and_cleanup`.
   - Done: add two-sided call-statement-route safety wrappers through the
     combined captured/no-capture component path, ending at
     `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_with_call_statement_routes`.
   - Done: add the end-to-end bridge theorem
     `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check`,
     showing that call-statement route proofs plus the current component
     sidecar check are sufficient for program-level safety without changing
     the extracted checker gate.
   - Done: add per-function component-check evidence bridge
     `check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary_store_safe_synthetic_direct_call_ready_summary`,
     so later proofs can use a checked component function without first
     requiring an environment-wide component sidecar.
   - Done: add combined-branch evidence extractor
     `check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_store_safe_synthetic_direct_call_ready_summary_when_not_captured`,
     deriving the same summary when the combined OR sidecar succeeds and the
     captured sidecar is false for that function.
   - Done: add route package helper
     `eval_preserves_synthetic_direct_call_ready_summary_call_package_statement_of_call_statements`,
     packaging the prefix and frame/parameter-scope call-statement route
     premises for existing summary-bridge narrow-core helpers.
   - Done: add summary-bridge preservation corollary
     `eval_preserves_synthetic_direct_call_ready_with_summary_bridge_narrow_core_of_call_statement_routes`,
     lifting the two call-statement route premises directly through the
     summary-bridge narrow-core wrapper.
   - Done: add named call-routes package
     `eval_preserves_synthetic_direct_call_ready_call_routes_statement`
     with accessors and
     `eval_preserves_synthetic_direct_call_ready_summary_call_package_statement_of_call_routes`,
     preparing the remaining simultaneous route proof.
   - Done: factor direct-call bind-parameter route inputs into
     `eval_call_bind_params_route_inputs_from_components`, removing duplicated
     setup in the call-statement cleanup bridge.
   - Done: add non-invasive `End2EndSafety.v` bridge lemmas
     `infer_fn_env_end2end_combined_gate` and
     `infer_fns_env_end2end_combined_check_env_ready`, proving that the current
     old gate implies the combined OR sidecar.
   - Remaining gap: prove the concrete recursive synthetic direct-call route
     statements
     `eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement`
     and
     `eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement`.
     The current hard sub-obligation is supplying the body-env synthetic
     direct-call evidence under `global_env_with_local_bounds env (fn_bounds fcall)`
     while using the prefix/scope call routes simultaneously for the recursive
     body call. Then finish localizing the store-safe synthetic summary evidence
     required by the component branch, switch the extracted end-to-end checker
     gate to the combined sidecar, and move direct self/mutual recursion tests
     from invalid to valid.
   - The recursive-call proof must still route through the existing end-to-end
     program theorems:
     `infer_program_env_end2end_sound`,
     `check_program_env_end2end_sound`, and
     `infer_program_env_end2end_big_step_safe_checked_initial_ready`.
   - If any theorem must be narrowed or a proof gap is introduced, record that
     explicitly before claiming the feature complete.
   - Preserve existing closure safety invariants for captured frames, root
     provenance, alpha-renaming, and parameter cleanup.

6. FIR and diagnostics.
   - Render synthetic local-rec functions consistently with existing synthetic
     closure functions.
   - Keep diagnostic names mapped back to source rec names where practical.
   - Ensure generated synthetic names cannot collide with user-visible
     top-level names.

## Test Plan

Valid tests:

- Top-level self-recursion.
- Top-level mutual recursion.
- Basic non-capturing local rec group called from the `in` body.
- Local rec function used as a first-class `fn` value in the `in` body.
- Shadowing where a local binding hides a rec function name.
- Non-capturing local self-recursion.
- Non-capturing local mutual recursion.
- Same-group non-recursive forward direct call.
- Captured local rec closure with an immutable unrestricted capture, called
  from the `in` body.
- Captured recursive closure with an immutable unrestricted capture.
- Captured mutual recursive closures sharing one capture list.
- Captured same-group non-recursive forward direct call.
- Shadowing where a parameter hides a rec function name.

Invalid tests:

- Done: current top-level direct self/mutual recursion safety-gate failures,
  until the recursive direct-call proof lands and these move to valid tests.
- Done: duplicate function names in one rec group.
- Done: missing parameter or return annotation.
- Done: local-rec generic parameters or `where` clause.
- Done: rec body uses an outer local variable not listed in the capture list.
- Done: unknown capture name.
- Done: duplicate capture name.
- Done: mutable capture.
- Done: affine capture.
- Done: linear capture.
- Done: explicit type arguments on a local rec function value.
- Done: user-defined top-level names starting with reserved `__facet_`.
- Done: actual local recursive body calls remain rejected by the current
  end-to-end safety gate until the recursive direct-call proof lands.
- Recursive non-function binding is not representable in the v1 parser syntax.
- Unique-reference capture coverage remains under the closure test suite.

FIR tests:

- Done: non-capturing local rec emits synthetic functions and direct calls.
- Done: captured local rec emits synthetic captured functions and closure calls.

Required checks for implementation PRs:

- `cd rocq && make`
- `dune build`
- `sh tests/run.sh`
- `sh tests/fir/run.sh` when FIR output changes

## Future Work

- Local-rec generics and local `where` clauses.
- Per-function capture lists.
- Borrow-capture syntax such as `closure [&x]` or `let rec [&x]`.
- Mutable recursive closures with environment write-back, corresponding to
  `FnMut`-like behavior.
- Affine and linear captured recursive closures with consuming calls,
  corresponding to `FnOnce`-like behavior.
- More precise diagnostics for synthetic local-rec functions.
