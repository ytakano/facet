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
- Nested direct-call target component evidence is now named as
  `component_body_no_capture_direct_call_component_nested_target_in_provider`,
  with `component_body_synthetic_direct_call_ready_closure_nested_summary_at_in_provider_of_target_provider`
  deriving closure-scoped nested summary evidence from it.
- Alpha-renamed callee target evidence is now named as
  `component_body_no_capture_direct_call_component_alpha_nested_target_in_provider`,
  matching the `alpha_rename_fn_def ... = (fcall, used')` evidence available
  inside the pointwise call route.
- Alpha-renamed nested target evidence now lowers to the synthetic summary
  provider `component_body_synthetic_direct_call_ready_alpha_nested_summary_at_in_provider`,
  and the direct-call route has alpha-aware call-route variants that pass the
  route's `alpha_rename_fn_def ... = (fcall, used')` evidence to nested summary
  callbacks while preserving the old broad-provider wrapper.
- The alpha-renamed nested summary provider is now threaded through the
  component, env/checker, and end-to-end pointwise call-route wrappers via
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_summary_at_call_route_evidence`,
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_summary_at_call_route_with_component_body_nested_in_evidence`,
  and
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_summary_at_call_route_and_component_body_nested_in_evidence`.
- The remaining nested body-env evidence dependency now also has an alpha-aware
  provider shape,
  `component_body_synthetic_direct_call_ready_alpha_nested_body_env_evidence_in_provider`,
  plus route/component/env/checker/end-to-end wrappers ending at
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_nested_evidence_at_call_route_and_component_body_nested_in_evidence`.
- The alpha-aware nested body-env evidence provider can now be derived from the
  existing component summary provider via
  `component_body_synthetic_direct_call_ready_alpha_nested_body_env_evidence_in_provider_of_provider`,
  matching the previous broad nested body-env evidence construction.
- The alpha-aware end-to-end call-route bridge can now consume the existing
  component summary provider plus the closure-check provider through
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_nested_evidence_at_call_route_and_component_body_summary_provider_and_closure_check`;
  the closure provider supplies direct target evidence while the summary provider
  supplies alpha nested summary/body evidence.
- The target-scoped call-route interface is now named as
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at`,
  replacing the broad nested body-env evidence premise with evidence for the
  current callee name.
- The cleanup helper now has an evidence-at route variant,
  `eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_summary_at_call_statement_evidence_at`,
  which builds nested callee evidence from the nested `summary_at` fact instead
  of requiring broad body-env evidence.
- The final-roots alpha call-route wrapper now has an evidence-at variant,
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_call_route_final_roots_core`,
  removing the broad nested body-env evidence premise at that layer.
- The evidence-at final-roots route is now threaded through component,
  env/checker, and end-to-end wrappers, ending at
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_summary_provider_and_closure_check`.
  This removes the broad alpha nested body-env provider from the alpha route
  bridge that still uses `component_body_synthetic_direct_call_ready_summary_provider`.
- The evidence-at alpha end-to-end bridge no longer needs the broad component
  summary provider when given closure-derived direct target evidence plus
  alpha nested target evidence, via
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_closure_target_provider`.
- Alpha-renaming now has direct-call target converse facts:
  `alpha_rename_expr_efn_inv` and
  `direct_call_target_expr_alpha_rename_expr_inv`, covering the `ECall` and
  `ECallExpr (EFn ...)` cases needed to relate a route `fcall` target back to
  the pre-renamed closure-check function body.
- The expression-level converse is now lifted to function definitions as
  `direct_call_target_expr_alpha_rename_fn_def_inv`, so route-level
  `alpha_rename_fn_def ... = (fcall, used')` evidence can recover the original
  direct-call target on `fdef`.
- Closure-derived alpha nested target evidence now has a target-lookup scoped
  provider,
  `component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider`,
  with constructor
  `component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_provider_of_closure_check_provider`.
  This uses the closure checker sidecar, the alpha direct-target inverse, and
  existing local-bounds summary lifting to handle recursive self/mutual seen-set
  cases without requiring a whole body-env summary provider.
- The target-lookup scoped alpha nested provider is now threaded through the
  component/env/checker/end-to-end evidence-at call-route wrappers via
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence`,
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence`,
  and
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_component_body_closure_check`.
  The bridge now uses only the closure checker sidecar for the direct-component
  branch, instead of a separate broad component-body summary provider or broad
  alpha nested target provider.
- The route layer now has
  `direct_call_callee_body_root_synthetic_direct_call_ready_evidence_of_evidence_at_all`,
  a small bridge from per-name evidence-at callbacks to the older env-wide
  direct-call evidence shape. This gives the next route-closure step a way to
  reuse older body-env evidence interfaces when all names in that body env have
  pointwise evidence.
- The route layer now uses that bridge in
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_with_evidence_at_all`,
  a prefix-call wrapper that consumes all-name evidence-at callbacks for the
  current env while reusing the older env-wide direct-call route interface.
- The exact evidence-at prefix-call route is now factored by
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_body_env_provider`,
  reducing that route Prop to the older summary-at route plus a focused provider
  that turns the current callee's pointwise evidence into recursive body-env
  direct-call evidence.
- The prefix-call route also has a localized body-env provider wrapper,
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_local_body_env_provider`,
  so component-level wrappers can pass body-env recursive evidence for the
  current call without first constructing a global route Prop.
- The result-subset body cleanup path now has a localized body-env provider
  variant,
  `eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_summary_at_call_statement_evidence_at_local_body_env_provider`,
  which applies the older summary-at prefix route at the concrete nested body
  call while supplying recursive body-env evidence only for that nested body
  environment.
- The alpha nested final-roots summary-at call-route bridge now uses that
  localized result-subset cleanup helper, so its prefix-side recursive body
  preservation path flows through the same current-target evidence-at factoring.
- The pointwise summary-at call package now has constructor
  `eval_preserves_synthetic_direct_call_ready_summary_at_pointwise_call_package_statement_of_call_route_cleanup`,
  bundling a prefix call route with the existing frame/scope cleanup-derived
  call route.
- The lookup-evidence component wrapper cannot be reduced from the
  evidence-at prefix route back to the summary-at prefix route using only the
  closure target lookup provider: the summary-at route still requires broad
  `forall fcall_inner` nested body-env evidence, while lookup evidence is scoped
  to the concrete next target. The remaining route-closure work must therefore
  prove the evidence-at prefix route itself, rather than trying to derive that
  wrapper through the older summary-at route.
- The result-subset body cleanup path now also has a concrete nested-call
  callback helper,
  `eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_summary_at_call_statement_body_call_callback`,
  replacing the recursive route premise with a callback for the exact nested
  `ECall` body evaluation and preserving the evidence-at summary/evidence
  inputs. This is the insertion point for an evaluation-derivation induction
  hypothesis when closing the evidence-at prefix route directly.
- The evidence-at final-roots bridge now has body-callback variants:
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_body_call_callback_final_roots_core`
  connects final-roots preservation to the concrete nested body-call callback,
  and
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_body_call_callback`
  factors the full evidence-at prefix route through that callback plus a
  prefix-to-full-store premise.
- The prefix-to-full-store premise cannot be discharged directly: `store_typed_prefix`
  does not imply full `store_typed`. The route now avoids that premise in the
  body-callback factor by adding
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_body_call_callback_prefix_store_final_roots_core`
  and rewiring
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_body_call_callback`
  to call it. The prefix route now uses prefix argument typing, the
  prefix-store result-subset/scope helpers, and the prefix-only cleanup helper.
- Argument runtime naming for the generic prefix route is derived through
  `eval_args_preserves_root_names_keys_preservation_ready_runtime_with_static_expr`,
  so that generic layer needs
  `preservation_ready_expr_static_runtime_named_statement` rather than a full
  store-typed premise.
- The route layer also now has the store-safe argument variant
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_body_call_callback_prefix_store_final_roots_core`,
  which derives argument runtime naming from
  `store_safe_function_value_call_args_typed_roots_store_named`. This matches
  the direct-component checker sidecar and avoids needing the generic static
  runtime naming statement for that path.
- The direct-component wrappers
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_evidence`
  and
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence`
  now call that store-safe prefix body-callback final-roots core internally,
  using the existing evidence-at route premise only as the nested body-call
  callback.
- The route layer now names the store-safe evidence-at prefix route as
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at`,
  with constructor
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_body_call_callback`.
  This is the induction target for the direct-component path and avoids the
  generic static-runtime naming premise.
- The component summary facts now recover store-safe arguments for the
  alpha-renamed body call:
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_alpha_renamed_target_args_global_env_with_local_bounds`
  turns the component sidecar plus `alpha_rename_fn_def` and the renamed
  `direct_call_target_expr` into
  `store_safe_function_value_call_args (global_env_with_local_bounds env (fn_bounds fcall)) args_body`.
  This is the missing input for using the store-safe route inside recursive
  body-call callbacks.
- The direct-component alpha evidence-at wrappers now require the store-safe
  evidence-at prefix route for nested body calls. They derive the renamed
  body-call `store_safe_function_value_call_args` from the component sidecar
  and pass it to the store-safe route; current upper wrappers keep their public
  generic route premise by adapting it through
  `store_safe_function_value_call_args_preservation_ready`.
- The route layer now has
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_body_call_store_safe_route`,
  a bridge that builds the store-safe evidence-at route from the existing
  body-callback constructor, using only the store-safe route and a nested
  store-safe-arguments provider for recursive body calls rather than the
  generic evidence-at route.
- The captured-or-direct-component safety wrappers and their end-to-end
  component-route theorems now take the store-safe evidence-at route directly.
  The temporary generic-route adapters above the direct-component wrappers were
  removed, so the remaining route premise on this path is store-safe all the
  way up to `End2EndSafety.v`.
- Component-ready environments now expose a reusable alpha-renamed body-call
  store-safe-args provider:
  `env_fns_root_shadow_no_capture_direct_call_component_store_safe_summary_ready_alpha_renamed_target_args_global_env_with_local_bounds`.
  This packages uniqueness plus component readiness into the second provider
  required by the store-safe recursive route bridge.
- The route layer now has
  `store_safe_synthetic_direct_call_ready_body_call_route_package_statement`
  and
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_body_call_route_package`,
  grouping the summary-at and store-safe-args body-call providers used by the
  store-safe recursive route bridge.
- End-to-end safety now has closure-gate mirrors of the current checker gate:
  `infer_fn_env_end2end_closure_combined_gate` and
  `infer_fns_env_end2end_closure_combined_check_env_ready`. These do not change
  checker behavior, but prove that the existing captured-call gate implies the
  newer captured-or-direct-component-closure checker sidecar.
- The route layer now has an exact-body bridge,
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_synthetic_evidence_at_route`,
  closing store-safe nested body calls through the ordinary evidence-at route
  when the alpha-renamed function body target is literally `ECall fname args`.
  This separates the direct `ECall` case from the remaining `ECallExpr (EFn ...)`
  normalization case.
- The component summary facts now name exact direct-call bodies with
  `callee_body_root_shadow_no_capture_direct_call_component_exact_body_target`
  and preserve that exactness through alpha-renaming via
  `callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target`.
  This supplies the route-layer exact-body bridge without changing checker
  behavior.
- The checker sidecar layer now has exact direct-call component closure checks:
  `check_fn_root_shadow_no_capture_direct_call_component_exact_body_target`,
  `check_fn_root_shadow_no_capture_direct_call_component_exact_closure`, and
  the captured-or-exact-closure combined checker. Summary facts prove head
  soundness and expose
  `component_body_no_capture_direct_call_component_exact_body_target_provider`
  from the exact closure checker.
- The exact captured-or-direct-component-closure checker now has function- and
  environment-level soundness lemmas,
  `check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary_sound`
  and
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary_ready`,
  returning the existing combined readiness Prop while retaining exact-body
  information through the separate provider.
- End-to-end safety now also mirrors the current checker gate into the exact
  captured-or-direct-component-closure sidecar via
  `infer_fn_env_end2end_exact_closure_combined_gate` and
  `infer_fns_env_end2end_exact_closure_combined_check_env_ready`. This is a
  proof-only bridge; it does not widen checker acceptance yet.
- End-to-end safety now has
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route_and_component_body_closure_check`,
  which builds the store-safe evidence-at route from the ordinary evidence-at
  route plus exact body-call providers, then reuses the existing component
  closure-check safety wrapper.
- The checker sidecar layer now has a strict exact-closure combined checker,
  `check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary`
  plus its environment form. It checks exact closure whenever the direct-component
  summary checker succeeds, otherwise falls back to the captured-call summary,
  so component-branch closure evidence is not hidden by the captured branch.
  Summary facts prove readiness and component exact-closure extraction for this
  strict sidecar.
- The summary facts now also retain strict branch evidence in Prop via
  `callee_body_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary`
  and
  `env_fns_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_ready`,
  with checker soundness lemmas preserving the exact-closure component branch.
- Strict exact-closure readiness now converts back to the existing combined
  readiness through
  `callee_body_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_of_strict_exact_closure`
  and
  `env_fns_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_ready_of_strict_exact_closure`.
- Captured safety now has a checker-level strict exact-closure wrapper,
  `check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence`,
  connecting the strict sidecar to the existing evidence-at component route
  without switching the end-to-end checker gate yet.
- End-to-end safety now has the corresponding explicit strict-sidecar bridge,
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check`,
  so a future checker-gate switch has a direct safety target once the remaining
  component-body providers are available.
- Exact direct-call closure checks now imply the ordinary direct-call closure
  checker via
  `check_fn_root_shadow_no_capture_direct_call_component_closure_seen_of_exact_closure_seen`
  and `check_fn_root_shadow_no_capture_direct_call_component_closure_of_exact_closure`,
  with a provider-level adapter
  `component_body_no_capture_direct_call_component_closure_check_provider_of_exact_closure_check_provider`.
- Exact direct-call closure checks now also expose recursive callee exact-check
  evidence through
  `check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_callee`,
  matching the ordinary closure callee decomposition used by provider proofs.
- Exact direct-call closure providers now adapt directly to the existing
  component-body target, alpha-nested lookup, and summary-at providers via the
  `..._of_exact_closure_check_provider` lemmas.
- End-to-end safety now has a strict-sidecar bridge that consumes an exact
  closure provider directly:
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_and_exact_closure_provider`.
- Component summary facts now have local single-component closure-check helpers,
  `component_body_no_capture_direct_call_component_target_in_of_closure_check`
  and
  `component_body_no_capture_direct_call_component_alpha_nested_target_lookup_in_of_closure_check`,
  plus exact-closure variants, so future safety wrappers can use branch-local
  closure evidence without a whole-env provider.
- Captured safety now has branch-local strict exact-closure wrappers,
  `env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route`
  and its checker-level form, using exact closure evidence retained in the strict
  component branch instead of external component-body providers.
- End-to-end safety now has the matching branch-local strict wrapper,
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check`,
  eliminating external component-body provider premises from that bridge.
- End-to-end safety now also has an exact-body route variant of that bridge,
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route_and_branch_local_strict_exact_closure_check`,
  reusing the exact-body store-safe route adapter while keeping the strict
  checker sidecar branch-local.
- `CheckerRootSidecars.v` now has non-extracted shadow entrypoints
  `infer_fn_env_end2end_strict_exact_closure`,
  `infer_fns_env_end2end_strict_exact_closure`, and
  `infer_program_env_end2end_strict_exact_closure`, plus checker soundness and
  gate/readiness lemmas in `End2EndSafety.v`. These prepare the final gate
  switch without changing the current OCaml-facing checker behavior.
- The strict shadow program checker now has route-premised safety theorems,
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route`
  and the exact-body variant
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_synthetic_evidence_at_route`.
- The strict shadow program checker now also has an exact-body route-package
  safety bridge,
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package`,
  aligning end-to-end safety with the narrow exact-`ECall` route package.
- The strict shadow end-to-end checker entrypoints are now included in Rocq
  extraction (`infer_fn_env_end2end_strict_exact_closure`,
  `infer_program_env_end2end_strict_exact_closure`, and
  `check_program_env_end2end_strict_exact_closure`) and the regenerated OCaml
  fixtures build with dune, while the CLI still uses the existing checker.
- Rocq checker examples now lock the intended gate delta for direct self
  recursion: `check_program_env_end2end` still rejects the core direct-recursive
  example, while `check_program_env_end2end_strict_exact_closure` accepts it.
- The route layer now has component-scoped exact-body route packages via
  `store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_statement`
  and bridge theorem
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package`,
  reducing the package obligation to functions proven to be in the direct-call component.
- The strict shadow program checker now has the matching component-scoped
  exact-body route-package safety bridge,
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package`.
- Direct-call body safety now has proof-only evaluation-height relations
  (`direct_call_eval_height`, `direct_call_eval_args_height`, and
  `direct_call_eval_struct_fields_height`) plus local-bounds stability and
  existence lemmas, preparing a guarded proof of the recursive store-safe
  evidence-at route.
- Direct-call body safety now also has
  `direct_call_eval_height_ecall_inv`, extracting the argument and callee-body
  height from an `ECall` derivation and proving the body height is strictly
  smaller than the call height.
- The route layer now has a height-aware callback wrapper,
  `eval_synthetic_direct_call_body_cleanup_prefix_from_result_subset_summary_at_call_statement_body_call_callback_prefix_store_with_height`,
  which can pass a nested `ECall` evaluation-height proof to body-call
  callbacks. This confirmed that evaluation height alone does not close the
  exact-body route: when `fn_body fcall` is itself the target `ECall`, the
  nested call is the whole body, so no strict body-height decrease is available.
- Summary facts now include `lookup_fn_of_in_unique_by_name`, and the failed
  single-function exact-closure package attempt clarified the remaining route
  closure must use env-level/component-level readiness: exact closure accepts
  cycles through `seen`, so a callee head summary is not derivable from one
  function's closure check alone.
- Component readiness now has an env-level package shape,
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_with_body_summary`,
  plus `store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_body_summary_ready`,
  which turns that readiness into the scoped exact-body route package.
- Summary facts now also have
  `component_body_no_capture_direct_call_component_store_safe_summary_with_body_summary_provider`,
  with constructors from plain and store-safe component body summary providers.
- End-to-end strict shadow safety now has
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package`,
  fixing the scoped route package to the component body summary readiness shape.

- Captured safety now has route-local scoped exact-body package constructors:
  `store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_route_summary_at_provider`,
  `store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_exact_closure_component_ready`,
  and
  `store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_body_summary_provider`.
  These keep the route obligation scoped to the current direct-call component
  instead of requiring a broad body-summary provider.
- The store-safe evidence-at prefix route now has a height-indexed induction
  target,
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement`,
  plus projection theorem
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_height_statement`
  from the height-indexed target back to the ordinary route statement.
- Direct-call evaluation height now has a focused `eval_args` alignment helper,
  `direct_call_eval_args_height_eval_args_result_of_eval_result`, so once an
  expression-level height/eval result-alignment premise is available, outer
  `ECall` height inversion can be matched back to the ordinary `eval_args`
  derivation used by the route proof.
- Direct-call evaluation height now aligns with ordinary evaluation results via
  `direct_call_eval_height_eval_result`,
  `direct_call_eval_args_height_eval_args_result`, and
  `direct_call_eval_struct_fields_height_eval_struct_fields_result`, with small
  deterministic lookup helpers for store/place/path/branch overlap cases.
- Direct-call evaluation height now exposes the strictly smaller body evaluation
  for the same ordinary `Eval_Call` components through
  `direct_call_eval_height_ecall_body_lt_of_eval_call`, aligning height
  inversion back to the route proof's `eval_args`, alpha-renamed `fcall`, and
  body evaluation.
- The route layer now has the exact-body decreasing callback bridge
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_decreasing_body_call_callback_prefix_store_final_roots_core_exact_body`,
  which passes `n_body_call < n_call` from the outer direct-call height into
  the body-call callback when `fn_body fcall` is literally the target `ECall`.
- The recursive store-safe route is now closed at the height-indexed package
  level by
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_of_exact_body_call_route_package`,
  and projected back to the ordinary route by
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_height`.
- The height-projected exact-body route is now connected to the scoped
  component package by
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height`.
  The strict end-to-end exact-body scoped bridge no longer takes a
  self-recursive store-safe route premise.
- The exact-body scoped store-safe route can now be lifted to synthetic call
  routes by
  `eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement_of_exact_body_call_route_scoped_package_height`
  and
  `eval_preserves_synthetic_direct_call_ready_call_routes_statement_of_exact_body_call_route_scoped_package_height`,
  but this wrapper still has strong bridge premises for ready args and
  environment-wide synthetic summary evidence.
- The route layer now has the non-store-safe exact-body decreasing callback
  bridge
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_decreasing_body_call_callback_prefix_store_final_roots_core_exact_body`,
  removing the need for the invalid
  `preservation_ready_args -> store_safe_function_value_call_args` premise at
  the bridge level.
- The strong-premise synthetic call-route wrapper now uses the non-store-safe
  decreasing bridge through
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height`,
  so it no longer needs
  `preservation_ready_args -> store_safe_function_value_call_args`.
- The remaining summary/evidence bridge premise has been localized from
  env-wide summary evidence to callee-local
  `fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at`.
- The scoped exact-body evidence_at route is now threaded into the default
  checker plus branch-local strict-check bridge by
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check`,
  avoiding the callee-local premise for that end-to-end path.

- The component-level direct-call safety path now has a non-store-safe
  lookup-evidence wrapper,
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence_non_store_safe`,
  so the strict/direct-component branch can consume the non-store-safe
  evidence-at route once the env/checker wrappers are lifted.
- The combined captured-or-direct-component env/checker safety wrappers now also
  have non-store-safe lookup-evidence variants ending at
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe`.
- The strict exact-closure checker safety wrapper now has the corresponding
  non-store-safe lookup-evidence variant,
  `check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe`.
- Branch-local strict exact-closure safety also has non-store-safe env/checker
  wrappers ending at
  `check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe`,
  so exact-closure evidence can be derived inside the strict branch without
  separate provider premises.
- End-to-end safety now has the matching default-checker plus explicit strict
  sidecar bridge,
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_non_store_safe`.
- End-to-end branch-local strict safety now also has a non-store-safe route
  bridge,
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe`.
- The exact-body scoped package is now connected directly to that non-store-safe
  branch-local End2End bridge by
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_non_store_safe`.
- The default checker gate switch is now narrowed to the remaining concrete
  scope-route target: close
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_statement` by
  combining the existing generic ready frame/param-scope preservation with the
  direct `ECall` frame/param-scope route.
- The scope side now has a height-indexed call-route interface,
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_height_statement`,
  plus projection back to
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_statement`.
- The pointwise typed/named scope route now also has a height-indexed
  intermediate interface with the existing full `store_typed` cleanup premise,
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_call_height_statement`,
  plus projection back to the ordinary pointwise call statement.
- The pointwise typed/named scope route now also has prefix-store variants,
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement`
  and its height-indexed form. These match recursive body-call stores, where
  only `store_typed_prefix` is available for the callee parameter context.
- The prefix-store scope route also has evidence-at variants,
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at`
  and its height-indexed form. These keep current-callee evidence explicit;
  they cannot be projected to the older broad interface without root-name/root-key
  route premises.
- The scope cleanup setup now has
  `eval_synthetic_direct_call_body_scope_callback_from_result_subset_prefix_store_body_callback`,
  which replaces the circular public scope-route call with an explicit body-scope
  callback for the concrete nested `ECall`.
- The body-scope callback setup now also has the height-aware wrapper
  `eval_synthetic_direct_call_body_scope_callback_from_result_subset_prefix_store_body_callback_with_height`,
  supplying nested `direct_call_eval_height` evidence to a callback for the
  concrete body `ECall`.
- Outer direct-call argument frame/parameter scope preservation is now packaged
  as `eval_args_preserves_frame_param_scope_roots_ready`, replacing the repeated
  `Hframe_args`/`Hparam_args` extraction pattern used by scope cleanup proofs.
- Prefix-store pointwise scope routes now lift back to the existing full-store
  typed/named route interfaces via
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_call_height_statement_of_prefix_call_height_statement`
  and
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_call_statement_of_prefix_call_statement`.
- The route layer now has exact-body package projection helpers,
  `fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at_of_exact_body_call_route_package`
  and `store_safe_function_value_call_args_of_exact_body_call_route_package`,
  so exact-body route proofs can reuse package summary/store-safe facts without
  duplicating target-normalization code.
  Existing exact-body route package wrappers now use those helpers instead of
  repeating the inline target-normalization/projection proof.
- The height-indexed evidence-at prefix-store `ECall` scope route now has a
  typed-route bridge,
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_height_statement_evidence_at_from_typed_route_and_exact_body_call_route_package`.
  It closes frame/parameter cleanup from the exact-body package using the
  result-subset cleanup path, height body-scope callback, argument scope helper,
  and `direct_call_eval_height_ecall_body_lt_of_eval_call`, while taking the
  height-indexed typed/roots route as the remaining recursive premise.
- The same scope route now has the bounded body-call callback variant
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_height_statement_evidence_at_from_body_call_callback_and_exact_body_call_route_package`.
  This removes the full typed-route premise at that layer and exposes the
  concrete nested `ECall` typed/roots callback with height and `< n_call`
  evidence, matching the typed/roots height induction shape.
- The scope route now also has a current-height helper,
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_height_statement_evidence_at_current_from_less_callbacks_and_exact_body_call_route_package`,
  which takes typed/roots and scope callbacks only for heights strictly smaller
  than the current call. This is the form needed by the upcoming mutual
  height induction.
- The typed/roots route now has the matching current-height helper,
  `eval_preserves_typing_roots_synthetic_direct_call_ready_summary_at_prefix_call_height_statement_evidence_at_current_from_less_callbacks_and_exact_body_call_route_package`,
  which uses the less-than typed callback for nested cleanup and the less-than
  scope callback to produce the callee-body frame/parameter scope package.
- The current-height helpers are now packaged by the mutual height theorem
  `eval_preserves_typing_roots_and_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_height_statement_evidence_at_of_exact_body_call_route_package`,
  with projection wrappers for the typed/roots route and the evidence-at
  prefix-store scope route that no longer require the broad synthetic scope
  premise.
- The evidence-at prefix-store scope route now projects through the existing
  summary-at/full-store route layers via
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_height_statement_of_evidence_at`
  and the exact-body package wrappers ending at
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_call_statement_of_exact_body_call_route_package`.
- The exact-body package now projects directly to the pointwise summary-at call
  package via
  `eval_preserves_synthetic_direct_call_ready_summary_at_pointwise_call_package_statement_of_exact_body_call_route_package`,
  avoiding the weaker ordinary direct `ECall` scope route.
- The route layer now has
  `eval_synthetic_direct_call_body_scope_callback_from_ready_evidence_at_summary_at_prefix_call_statement`,
  which builds callee-body frame/parameter scope callbacks from the
  summary-at prefix scope route and body-env summary/evidence providers.
- The final-roots cleanup bridge now has summary-at prefix-scope route variants:
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_nested_evidence_summary_at_prefix_scope_call_route_final_roots_core`
  and
  `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_summary_at_prefix_scope_call_route_final_roots_core`.
- Component safety can now consume the summary-at prefix-scope final-roots
  bridge through
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_summary_at_prefix_scope_call_route_evidence`.
- Env-level captured-or-direct-component safety now has nested2 provider Props
  and a summary-at prefix-scope wrapper:
  `component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider`,
  `component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider`,
  and
  `env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_prefix_scope_call_route_with_component_body_nested_in_evidence`.
- Checker and end-to-end safety now have matching summary-at prefix-scope
  wrappers:
  `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_summary_at_prefix_scope_call_route_with_component_body_nested_in_evidence`
  and
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_nested_in_evidence`.
- The exact-body route package now connects to the summary-at prefix-scope
  end-to-end bridge through
  `eval_preserves_frame_param_scope_synthetic_direct_call_ready_summary_at_prefix_call_statement_of_exact_body_call_route_package`,
  `component_body_synthetic_direct_call_ready_nested2_summary_at_in_provider_of_provider`,
  `component_body_synthetic_direct_call_ready_nested2_body_env_evidence_in_provider_of_provider`,
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider`,
  and
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider`.
- The strict exact-closure entrypoint now has the same combined-sidecar and
  exact-body route-package/provider bridge shape through
  `infer_fn_env_end2end_strict_exact_closure_combined_gate`,
  `infer_fns_env_end2end_strict_exact_closure_combined_check_env_ready`,
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider`,
  and
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_body_summary_provider`.
- The strict exact-closure bridge can now build the component-body summary
  provider from the whole-env direct-component checker through
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_package_and_component_check`,
  reducing one Prop-level provider input to an executable sidecar check.
- The strict exact-closure route now has a component-scoped exact-body target
  bridge. `callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_alpha_renamed_target_any`
  generalizes exact-body target projection to arbitrary direct-call target
  witnesses, and
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_component_exact_body_target`
  lets the scoped route package derive the old global `Hexact_body_target`
  input from a component-ready exact-body target provider.
- The strict exact-closure component-body summary route package now has
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package_and_exact_body_target_provider`,
  replacing the old global exact-body target premise with an exact-body target
  provider matched to the component summary sidecar.
- The same route now has
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_component_body_summary_route_package_and_exact_closure_provider`,
  deriving that exact-body target provider from the exact-closure component
  checker provider.
- The route can now use exact-closure component-ready evidence directly via
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_component_ready_route_package`,
  combining unique-name, component-summary, and exact-closure checker facts
  into the existing scoped package.
- Strict exact-closure checker facts now expose the direct-component branch as
  paired Prop/checker evidence through
  `check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_ready`
  and
  `check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_ready`.
- Strict exact-closure program inference now exposes its accepted env sidecars
  directly through
  `infer_program_env_end2end_strict_exact_closure_check_env_ready` and
  `infer_program_env_end2end_strict_exact_closure_combined_check_env_ready`.
- Exact-closure component sidecars now have In-scoped provider forms,
  `component_body_no_capture_direct_call_component_exact_closure_check_in_provider`
  and `component_body_no_capture_direct_call_component_exact_body_target_in_provider`,
  plus constructors from the strict exact-closure env check. These avoid relying
  on Prop-to-bool completeness for component summaries.
- End-to-end strict exact-closure safety now has
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_component_check_route_package`,
  which builds exact-closure component-ready evidence from checker bool sidecars
  plus strict env sidecar checks.
- Strict exact-closure program inference now derives accepted-env in-provider
  sidecars directly through
  `infer_program_env_end2end_strict_exact_closure_exact_closure_check_in_provider`
  and
  `infer_program_env_end2end_strict_exact_closure_exact_body_target_in_provider`.
- Strict exact-closure program inference now exposes accepted-env
  component-ready evidence through
  `infer_program_env_end2end_strict_exact_closure_component_ready`, connecting
  `In` plus bool component sidecars to Prop component summary and exact-closure
  checker evidence.
- Bool component sidecars now have a target-propagation provider,
  `component_body_no_capture_direct_call_component_target_check_in_provider`,
  plus strict accepted-env derivation through
  `infer_program_env_end2end_strict_exact_closure_target_check_in_provider`.
  This avoids requiring Prop-to-bool completeness for component summaries.
- Bool component sidecars now also expose summary-at evidence through
  `component_body_synthetic_direct_call_ready_summary_at_check_in_provider`
  and strict accepted-env derivation through
  `infer_program_env_end2end_strict_exact_closure_summary_at_check_in_provider`.
- Strict exact-closure checker facts now expose a branch-local component-ready
  path when the captured-call branch is known false, through
  `check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_ready_when_not_captured`,
  its env-level counterpart, and
  `infer_program_env_end2end_strict_exact_closure_component_ready_when_not_captured`.
- The same non-captured branch now exposes component-check evidence through
  `check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_component_check_when_not_captured`,
  its env/program wrappers, and the route wrapper
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_closure_non_captured_route_package`.
- Default end-to-end inference now has the accepted-env uniqueness sidecar
  `infer_program_env_end2end_unique_by_name`, matching the strict sidecar and
  reducing repeated proof expansion in route wrappers.
- Default end-to-end inference now exposes program-level checker sidecars
  `infer_program_env_end2end_check_env_ready` and
  `infer_program_env_end2end_combined_check_env_ready`, matching the fns-level
  captured and captured-or-direct component checks.
- The default main safety theorem
  `infer_program_env_end2end_big_step_safe_checked_initial_ready` now uses
  accepted-env sidecars directly instead of reopening program inference.
- Program checker booleans now expose infer witnesses through
  `check_program_env_end2end_infer_ok` and
  `check_program_env_end2end_strict_exact_closure_infer_ok`; strict checker
  acceptance also has the constructive soundness wrapper
  `check_program_env_end2end_strict_exact_closure_sound_exists`.
- The strict alpha-evidence safety wrapper
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route`
  now uses accepted-env sidecars directly instead of reopening program inference.
- The strict summary-at prefix-scope route wrapper
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_summary_at_prefix_scope_call_route_and_component_body_summary_provider`
  also uses accepted-env uniqueness and combined-check sidecars directly.
- The default call-statement route wrapper
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_call_statement_routes_and_component_check`
  now uses accepted-env uniqueness and combined-check sidecars directly.
- The default summary exact package wrapper
  `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_summary_exact_package_and_component_check`
  now uses accepted-env uniqueness and combined-check sidecars directly.
- Five additional default summary/body-evidence route wrappers now use the
  accepted-env uniqueness and combined-check sidecars directly, instead of
  reopening `infer_program_env_end2end` in each proof.
- Four more default summary-at/alpha route wrappers now use accepted-env
  sidecars directly, further reducing direct dependence on the internal shape
  of `infer_program_env_end2end`.
- Remaining default route wrappers now derive `fn_env_unique_by_name` and
  combined checker sidecars from program-level accepted-env lemmas, leaving
  direct `infer_program_env_end2end` expansion only in the sidecar lemmas
  themselves.
- The exact-body scoped route package now has an accepted-env-shaped
  `..._in_provider` Prop plus a projection from the existing all-env scoped
  package, preparing the remaining provider assumptions for env-localization.
- Env-runtime captured safety now has env-local constructors for the scoped
  exact-body route package from component-body summary readiness, env-local
  summary-at providers, and exact-closure component readiness.
- The env-local exact-body route package now also has a constructor from
  accepted-env component checker bools plus summary-at checker providers, and
  strict exact-closure program inference exposes that package as an End2End
  sidecar.
- The store-safe evidence-at prefix route now has an env-local statement
  `..._in_env` plus a projection from the existing all-env statement, preparing
  exact-body route closure to consume accepted-env package sidecars.
- The non-store-safe evidence-at prefix route now has the same env-local
  statement/projection shape, matching the branch-local strict wrappers that
  use the non-store-safe route.
- Function-environment name uniqueness now has a local-bounds stability lemma,
  preparing strict exact-closure component providers to be lifted through
  recursive body environments.
- The scoped exact-body route package now has a local-bounds-family constructor
  from base-env component checker bools and summary-at checker providers,
  preserving accepted-env evidence through recursive body environments.
- Strict exact-closure program inference now exposes that local-bounds-family
  scoped route package directly as an End2End sidecar for the accepted env.
- The store-safe evidence-at prefix route now also has a height-indexed
  env-local statement plus projections to and from the existing all-env route
  shape, enabling future exact-body induction to stay scoped to an accepted env.
- Local-bounds environment families are now named by
  `global_env_local_bounds_family`, with base/step lemmas, and the strict
  exact-closure scoped route sidecar uses that named family instead of an
  inline existential.
- The store-safe height-indexed evidence-at prefix route now has
  env-family/local-bounds-family statement forms plus an all-env projection, so
  the next exact-body induction can quantify over only accepted-env descendants.
- The scoped exact-body package now drives a store-safe height induction over
  an arbitrary environment family, with a local-bounds-family specialization for
  accepted-env descendants.
- Local-bounds-family height routes now project to ordinary env-local routes for
  any descendant environment, preparing component-body callbacks to avoid the
  old all-env route premise.
- The no-capture direct component branch now has a lookup-evidence safety
  wrapper that consumes the component body-env local-bounds-family route instead
  of a whole-env route.
- Strict exact-closure env/checker safety now has local-bounds-family route
  variants, threading the component body-env route through the direct-component
  branch while leaving captured-call handling unchanged.
- Local-bounds families now have an inclusion lemma from a nested body-env base
  back to the accepted-env base, simplifying End2End route sidecar wiring.
- The env-family scoped exact-body height route now localizes its exact-body
  target premise to the same environment family, removing another all-env
  assumption from the accepted-env route path.
- The scoped exact-body package now has a route-specific component-ready
  constructor requiring only component safety plus alpha-renamed direct-target
  summary-at evidence, avoiding full body-summary evidence for End2End wiring.
- Strict exact-closure env/checker safety now also has branch-local
  local-bounds-family route variants, requiring the route only after the
  direct-component checker branch is known.
- Strict exact-body target evidence is now stable across
  `global_env_with_local_bounds` via
  `callee_body_root_shadow_no_capture_direct_call_component_exact_body_target_global_env_with_local_bounds`,
  preparing accepted-env exact-target sidecars for branch-local body-env route
  construction.
- Strict exact-closure program inference now projects accepted-env exact-body
  target sidecars through arbitrary local-bounds descendants via
  `infer_program_env_end2end_strict_exact_closure_exact_body_target_in_local_bounds_family`.
- Strict exact-closure program inference now also projects accepted-env
  direct-component store-safe summaries through arbitrary local-bounds
  descendants via
  `infer_program_env_end2end_strict_exact_closure_component_summary_in_local_bounds_family`.
- Strict exact-closure program inference now projects accepted-env
  direct-component route-summary readiness through local-bounds descendants via
  `infer_program_env_end2end_strict_exact_closure_component_route_summary_in_local_bounds_family`.
- Strict exact-closure program inference now exposes a route-summary based
  local-bounds-family scoped exact-body route package through
  `infer_program_env_end2end_strict_exact_closure_exact_body_route_scoped_package_local_bounds_family_with_route_summary`.
- End-to-end strict exact-closure safety now has a provider-parametric bridge,
  `infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_check_provider`,
  deriving a branch-local local-bounds-family store-safe route from accepted-env
  sidecars plus a local component-check provider.
- Exact direct-call closure checks now expose direct callee `seen` evidence via
  `check_fn_root_shadow_no_capture_direct_call_component_exact_closure_callee_seen`,
  preparing route closure to track only functions reachable from the current
  direct-component branch.
- Direct callee `seen` evidence now projects component summary and exact-body
  target facts for non-seen callees via
  `check_fn_root_shadow_no_capture_direct_call_component_exact_closure_callee_seen_head_sound`.
- Exact direct-call closure `seen` checks now expose a branch point via
  `check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_head_or_seen`,
  distinguishing already-seen recursive callees from non-seen callees with fresh
  component summary/exact-target facts.
- Exact direct-call closure `seen` checks now expose head checker booleans via
  `check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_head_checks`
  and
  `check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen_component_check`,
  so reachable-route providers can pass accepted component-check sidecars
  without converting Prop evidence back to booleans.
- End-to-end strict exact-closure safety now has a named local-bounds helper,
  `infer_program_env_end2end_strict_exact_closure_seen_component_check_in_local_bounds_family`,
  projecting reachable `seen` exact-closure evidence to accepted-env
  direct-component checker booleans.
- End-to-end strict exact-closure safety now also names the local-bounds
  callee-seen projection as
  `infer_program_env_end2end_strict_exact_closure_callee_seen_in_local_bounds_family`,
  connecting a component's exact-closure check and direct callee lookup to the
  callee's `seen` exact-closure evidence.
- The callee-seen sidecar now has a `lookup_fn`-based local-bounds wrapper,
  `infer_program_env_end2end_strict_exact_closure_callee_seen_of_lookup_in_local_bounds_family`,
  matching the lookup evidence produced by direct-call route callbacks.
- Env-runtime captured safety now has
  `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_in_local_bounds_family_of_exact_body_call_route_scoped_package_with_component_exact_target`,
  letting local-bounds exact-body route closure derive exact-target obligations
  from the route's component-ready predicate.
- The End2End provider-parametric local-bounds route bridge now uses that
  component-exact-target route wrapper, keeping component membership and
  exact-target derivation aligned for the upcoming reachable predicate.
- End-to-end strict exact-closure safety now also projects reachable `seen`
  exact-closure evidence to local-bounds exact-body target facts via
  `infer_program_env_end2end_strict_exact_closure_seen_exact_body_target_in_local_bounds_family`.
- End-to-end strict exact-closure safety now bundles local-bounds
  route-summary readiness with exact-body target evidence through
  `infer_program_env_end2end_strict_exact_closure_route_summary_and_exact_target_in_local_bounds_family`,
  preparing a compact component-ready payload for reachable-route predicates.
- Env-runtime captured safety now has
  `store_safe_synthetic_direct_call_ready_exact_body_call_route_scoped_package_of_component_route_summary_and_exact_target_ready`,
  a scoped route package constructor for component-ready payloads that already
  carry route-summary readiness plus exact-body target evidence.
- End-to-end strict exact-closure safety now has
  `infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_payload_provider`,
  a local-bounds route bridge that consumes a component payload provider carrying
  route-summary readiness plus exact-body target evidence.
- The older component-check-provider local-bounds route bridge now factors
  through the payload-provider bridge, leaving a single route-closure insertion
  point for reachable component predicates.
- End-to-end strict exact-closure safety now derives the payload-provider
  payload directly from reachable `seen` exact-closure evidence via
  `infer_program_env_end2end_strict_exact_closure_seen_route_summary_and_exact_target_in_local_bounds_family`.
- End-to-end strict exact-closure safety now handles the singleton seen-cycle
  case through
  `infer_program_env_end2end_strict_exact_closure_single_seen_route_summary_and_exact_target_in_local_bounds_family`,
  reusing the root component payload when a callee name matches the root.
- End-to-end strict exact-closure safety now derives route-summary plus
  exact-target payload for a direct callee lookup via
  `infer_program_env_end2end_strict_exact_closure_direct_callee_route_summary_and_exact_target_in_local_bounds_family`,
  splitting the reachable callee into the singleton seen-cycle case or the
  non-seen reachable `seen` payload case.
- The direct-callee route payload now has an alpha-renamed callback wrapper,
  `infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_route_summary_and_exact_target_in_local_bounds_family`,
  so route callbacks can recover the original component target before deriving
  the callee payload.
- End-to-end strict exact-closure safety now converts alpha direct-callee
  payloads into per-name synthetic direct-call summary evidence via
  `infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_summary_evidence_at_in_local_bounds_family`,
  matching the branch-local `Hsummary_at` callback shape.
- The same summary-evidence conversion is available for unrenamed direct
  component targets through
  `infer_program_env_end2end_strict_exact_closure_direct_callee_summary_evidence_at_in_local_bounds_family`,
  matching the root component `Hsummary_at` callback.
- End-to-end strict exact-closure safety now bundles the branch-local component
  body callbacks as
  `infer_program_env_end2end_strict_exact_closure_component_body_direct_callee_callbacks_in_local_bounds_family`,
  deriving root summary evidence, direct-callee component summaries, and nested
  body summary evidence from the accepted-env exact-closure sidecar.
- The branch-local component body callback bundle now has named projections for
  root summary evidence, direct-callee component summaries, and alpha nested
  summary evidence, keeping upcoming body-env route wrappers small.
- End-to-end strict exact-closure safety now exposes
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family`,
  connecting the accepted-env strict sidecar to the component-local-bounds route
  wrapper while leaving only the component route provider to discharge.
- The accepted-env component-ready sidecar now has a named exact-closure
  projection, `infer_program_env_end2end_strict_exact_closure_component_exact_closure`,
  for component route-provider construction.
- Component body callback projections now also have component-check-only wrappers,
  deriving exact-closure internally from the accepted strict sidecar before
  exposing root, direct-callee, and alpha nested summary callbacks.
- Env-runtime captured safety now has
  `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence_callbacks_in_local_bounds_family`,
  a local-bounds wrapper that consumes the branch-local callback bundle directly.
- Env-runtime strict exact-closure safety now also has
  `env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks`,
  letting each no-capture component provide its body-env route together with the
  branch-local callback bundle.
- End-to-end strict exact-closure safety now exposes
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks`,
  combining an external component body-env route provider with callback bundles
  derived from the accepted-env sidecar.
- Env-runtime strict exact-closure safety now has the matching checker-sidecar
  callback wrapper,
  `check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_local_bounds_family_callbacks`.
- End-to-end strict exact-closure safety now exposes
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_check_provider_callbacks`,
  deriving each component body-env route from a local-bounds component-check
  provider and the accepted-env callback bundle.
- End-to-end strict exact-closure safety now derives that local-bounds
  component-check provider from the all-component no-capture checker sidecar via
  `infer_program_env_end2end_strict_exact_closure_component_check_provider_of_check_env_no_capture`,
  and exposes the resulting all-component check callback wrapper.
- End-to-end strict exact-closure safety now names the combined component
  route-and-callback construction as
  `infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_check_provider`,
  keeping later strict-sidecar provider replacement localized.
- End-to-end strict exact-closure safety now derives accepted-env
  direct-component checker booleans for direct callee lookups through
  `infer_program_env_end2end_strict_exact_closure_direct_callee_component_check_of_lookup_in_local_bounds_family`,
  splitting singleton seen cycles from non-seen reachable callees.
- The direct-callee component-check projection now has an alpha-renamed wrapper,
  `infer_program_env_end2end_strict_exact_closure_alpha_direct_callee_component_check_of_lookup_in_local_bounds_family`,
  matching the alpha direct-callee route and summary-evidence callbacks.
- Component route-and-callback construction now has a payload-provider entry
  point,
  `infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_payload_provider`,
  and the older check-provider helper factors through it.
- End-to-end strict exact-closure safety now exposes the payload-provider final
  wrapper
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_payload_provider_callbacks`,
  and the check-provider callback wrapper factors through it.
- End-to-end strict exact-closure safety now derives branch-local routes from
  exact-closure component-ready providers via
  `infer_program_env_end2end_strict_exact_closure_component_local_bounds_route_of_component_ready_provider`,
  using the existing exact-closure scoped route package.
- Component-ready providers now feed the callback path through
  `infer_program_env_end2end_strict_exact_closure_component_route_and_callbacks_of_component_ready_provider`
  and the final wrapper
  `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_with_component_ready_provider_callbacks`.
- Accepted strict exact-closure inference now projects function-name uniqueness
  through nested local-bounds families via
  `infer_program_env_end2end_strict_exact_closure_unique_by_name_in_local_bounds_family`.
- Local-bounds bridge facts now preserve provenance and store-safe argument
  checker booleans, and captured-call summary facts preserve the no-capture
  direct component store-safe checker boolean under
  `global_env_with_local_bounds`.
- No-capture direct component exact-closure `seen` checks and the top-level
  exact-closure checker are now stable under `global_env_with_local_bounds`,
  preparing accepted exact-closure booleans for local-bounds providers.
- Accepted component-check booleans now project to local-bounds
  component-ready payloads through
  `infer_program_env_end2end_strict_exact_closure_component_ready_payload_in_local_bounds_family`.

Next:

- Expose the End2End strict exact-closure wrapper that derives branch-local
  component body-env routes from the accepted-env sidecar; do not narrow
  `infer_program_env_end2end_big_step_safe_checked_initial_ready`.
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
   - Done: add final-roots alpha evidence-at bridge
     `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_body_call_callback_final_roots_core`,
     replacing the route-premise cleanup helper with the concrete nested body-call
     callback helper for the alpha-renamed direct-call body.
   - Done: add exact-body store-safe route package bridge
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package`,
     allowing the self-recursive store-safe route premise to consume a narrow
     exact-`ECall` body package instead of broad synthetic-body providers.
   - Done: close the exact-body store-safe route recursion by
     `direct_call_eval_height` well-founded induction in
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_height_statement_of_exact_body_call_route_package`,
     with ordinary route projection through
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_package_height`.
   - Done: connect the height-projected exact-body route through the scoped
     component package with
     `eval_preserves_typing_roots_store_safe_synthetic_direct_call_ready_summary_at_prefix_call_statement_evidence_at_of_exact_body_call_route_scoped_package_height`,
     and remove the self-recursive store-safe route premise from
     `infer_program_env_end2end_strict_exact_closure_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package`.
   - Done: add strong-premise wrappers
     `eval_preserves_typing_roots_synthetic_direct_call_ready_prefix_call_statement_of_exact_body_call_route_scoped_package_height`
     and
     `eval_preserves_synthetic_direct_call_ready_call_routes_statement_of_exact_body_call_route_scoped_package_height`,
     connecting the exact-body scoped route to synthetic call routes.
   - Done: add non-store-safe exact-body decreasing body-call callback bridge
     `eval_preserves_typing_roots_synthetic_direct_call_ready_ecall_cleanup_bridge_with_alpha_evidence_at_decreasing_body_call_callback_prefix_store_final_roots_core_exact_body`.
   - Done: replace the strong-premise wrapper with the non-store-safe
     decreasing bridge route, removing the invalid
     `preservation_ready_args -> store_safe_function_value_call_args` premise.
   - Done: localize the remaining summary/evidence bridge premise from
     env-wide summary evidence to callee-local
     `fn_root_shadow_synthetic_direct_call_ready_summary_evidence_at`.
   - Done: thread the scoped exact-body evidence_at route into the default
     checker plus branch-local strict-check bridge with
     `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check`.
   - Done: add the component-level non-store-safe lookup-evidence safety
     wrapper
     `callee_body_root_shadow_no_capture_direct_call_component_store_safe_summary_big_step_safe_checked_initial_ready_with_body_alpha_evidence_at_call_route_lookup_evidence_non_store_safe`.
   - Done: lift that wrapper through the combined env/checker lookup-evidence
     path with
     `check_env_root_shadow_captured_call_store_safe_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe`.
   - Done: lift the non-store-safe lookup-evidence path through the strict
     exact-closure checker wrapper with
     `check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_with_component_body_lookup_evidence_non_store_safe`.
   - Done: add branch-local strict exact-closure non-store-safe wrappers ending
     at
     `check_env_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary_big_step_safe_checked_initial_ready_of_alpha_evidence_at_call_route_non_store_safe`.
   - Done: lift the non-store-safe strict path through default end-to-end safety
     with an explicit strict sidecar check via
     `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_strict_exact_closure_check_non_store_safe`.
   - Done: add the branch-local strict End2End non-store-safe bridge
     `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_alpha_evidence_at_call_route_and_branch_local_strict_exact_closure_check_non_store_safe`.
   - Done: connect the exact-body scoped package to the non-store-safe
     branch-local End2End bridge with
     `infer_program_env_end2end_big_step_safe_checked_initial_ready_with_exact_body_call_route_scoped_package_and_branch_local_strict_exact_closure_check_non_store_safe`.
   - Done: add the height-indexed scope call-route interface
     `eval_preserves_frame_param_scope_synthetic_direct_call_ready_call_height_statement`
     and projection to the ordinary call route.
   - Done: exact-body route packages now project to pointwise summary-at call
     packages without proving the weaker ordinary direct `ECall` scope route.
   - Remaining gap: thread that pointwise summary-at package through the next
     end-to-end exact-body safety bridge, then switch the extracted end-to-end
     checker gate to the strict exact-body component sidecar path and move
     direct self/mutual recursion tests from invalid to valid.
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
