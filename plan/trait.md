# Trait Roadmap

## Goal

Implement Facet traits as a statically resolved system. Rocq remains the source
of truth for accept/reject behavior: OCaml may parse and resolve names, but
trait solving, method resolution, associated type compatibility, and final
validity checks must be represented in Rocq and the extracted checker.

## Current State

- Trait and impl items are parsed, lowered into Rocq/extracted environments,
  and checked for duplicate, missing, extra, and mismatched associated types and
  methods. Impl method bodies are elaborated to hidden functions and checked by
  the extracted checker even when the method is not called.
- Method-local type parameters are supported for trait and impl methods,
  including method-local bounds and generic-trait impl remapping. Method-local
  lifetime generics remain deferred and are rejected by tests.
- Method calls use Facet's ordinary prefix call shape: `(callee args...)`.
  Explicit UFCS is `(<Ty as Trait>::method receiver args...)`; short UFCS is
  `(Trait::method receiver args...)`; the receiver is always the first
  argument. Dot method-call syntax is intentionally rejected in this phase.
- Short UFCS accepts receiver types known before checker execution: function
  parameters, syntactically typed literals, immutable pure local literals after
  receiver-let elimination, fieldless struct literals, and payloadless enum
  constructors whose store-safe argument evidence is checked in Rocq.
  Field-bearing struct literals, payload-bearing enum constructors, direct-call
  receivers, generic direct-call receivers, non-pure inferred locals, and
  general annotated locals remain gated. Direct-call receivers cannot be
  unlocked by OCaml desugaring alone: lowering the receiver through a hidden let
  still fails the extracted end-to-end safety gate. Rocq now has the direct and
  generic receiver-method path factored into executable sidecar/checker
  summaries, proof-side shape/view lemmas, hidden-let/body packages,
  replay bridge, inversion/strip/replay-prep, conditional body-strip,
  direct summary/body-replay wrapper packages including copy/consumed
  argument-frame replay, direct receiver return-roots, hidden-root
  exclusion, direct receiver store-ref exclusion packaging with exact-start final
  root naming derived, ready direct-call receiver-store freshness preservation,
  composed hidden body replay packaging that derives direct and generic
  receiver-store refs/value refs internally under exact ready premises,
  a direct receiver-method replay wrapper/package that separates the receiver
  call's actual type from the hidden-frame annotation while leaving
  compatibility available to callers, root-set naming transport, generic
  return-root, hidden-root exclusion,
  receiver-store freshness, and store-ref exclusion packaging,
  consumed-frame support, generic receiver-method runtime replay packaging,
  proof-side direct/generic hidden-let typing inversion helpers for receiver
  and method-body root typing, and a behavior-preserving split between the
  active captured-call core gate and its public base wrapper. Hidden receiver
  freshness for method arguments and for the enclosing function body context is
  now enforced by the inactive direct and generic receiver-method sidecar
  summaries and exposed by their view facts. The direct receiver-method runtime
  replay package now also exposes the receiver callee's body-env store-safe
  summary, method-argument hidden-name freshness, derivable initial
  hidden-receiver store freshness, and transport functions for receiver
  provenance/env readiness into the body environment as top-level package
  fields; the generic runtime replay package exposes the same hidden-name
  freshness, initial store freshness, and body-env transport prerequisites.
  Raw direct/generic receiver-method call evaluation is also packaged into
  inversion lemmas that expose receiver evaluation, method-argument evaluation,
  method callee lookup, alpha-renamed body evaluation, and raw final cleanup.
  The direct and generic receiver-method runtime replay packages now expose
  those raw evaluation/final-cleanup components as top-level fields alongside
  the hidden-let replay evidence. Env-consumer wrappers source body-env
  provenance/readiness premises from env-level evidence for the replay
  continuations, conditional package-consumer lemmas record how a
  preservation-ready hidden replay would yield value typing at the
  hidden-cleaned store, cleanup consumers equate the raw/base final store
  with the hidden-cleaned store once the hidden-frame relation and replay
  cleanup equations are matched, replay-package consumers now expose that
  conditional `s' = s_hidden` result alongside the hidden evaluation and replay
  witnesses, and value consumers transport a typed replayed hidden method-call
  result across hidden cleanup to the raw final store without assuming the whole
  hidden `ELet` is preservation-ready, hidden-call value bridges derive the
  replayed method-call result type from the typed `ECallGeneric` subexpression
  plus the method callee summary, direct/generic branch-level value wrappers
  now compose the final replay witness with hidden-let typing inversion, method
  call typing, and hidden cleanup while exposing the typed receiver-call evidence
  needed by provider wiring, and direct/generic hidden-start-store invariant
  providers derive the store typing, root, naming, no-shadow, and closure-summary
  facts needed to invoke those wrappers after the replayed receiver call. The
  direct and generic paths also have checked-initial body-env providers, and
  checked-initial branch-value consumers now supply those provider facts to the
  direct/generic replay-final wrappers. Both direct and generic runtime package
  branches now have checked-initial consumers that compose final-store cleanup
  with their branch-value wrappers, and both receiver-method sidecar summaries
  now have conditional summary-to-value bridges using those consumers. Env-level
  provenance and preservation-readiness evidence can now be transported through
  local-bounds body environments for the public provider layer. The direct and
  generic receiver-method replay-package final-store consumers now also have
  replay-facts variants that expose hidden/base relation, cleanup, freshness,
  and base body evaluation evidence to future final-store matching providers.
  The direct and generic checked-initial branch wrappers can now consume
  those strengthened matching continuations at the checked-initial boundary,
  and both summary-to-value bridges have replay-facts variants that carry the
  same provider shape up to the summary boundary. Both summary boundaries also
  have raw-package replay-facts variants, so matching providers can compare the
  raw call evaluation/final cleanup package against the replayed hidden/base
  facts in one continuation. The direct and generic paths now have prefix matching providers that use
  evaluator determinism to align raw receiver and method-argument
  prefixes with the replayed receiver, base argument store, and method values,
  narrowing the remaining obligations to alpha/body final-store matching.
  A shared alpha/body final-store helper now identifies matching raw and
  replayed body runs once both sides use the same base-store alpha rename,
  and the hidden receiver's index-0 name is proved not to change
  `fresh_ident` when inserted into an alpha-renaming seed. That invariant now
  reaches the function-definition seed, preserves the full parameter-renaming
  output parameters and rename environment, carries the final parameter `used`
  lists as the same hidden-receiver insertion relation, and has matching
  transport for identifier-list binder renaming, call-argument/payload
  expression-list traversal, struct-field traversal, match-branch traversal,
  let-binder fresh seeds, conditional expression chains, annotated and
  inferred let expression bodies, and deref/drop unary wrappers. Public runtime
  branch wiring still needs that relation lifted
  through expression body alpha-renaming and
  remaining hidden/base alpha transport before the direct/generic
  replay/final-store matching providers can close; receiver-method
  summaries remain inactive until that public runtime safety branch is proved
  and wired.
- Associated type projections use `<Ty as Trait>::Assoc`; `Self::Assoc` is
  accepted inside the current trait/impl context. Generic projections under
  local trait bounds are preserved and regression-tested. Raw elaboration no
  longer rewrites the entire raw function AST with `normalize_assoc_raw_*`; it
  preserves surface raw expressions and normalizes only at core checker
  boundaries such as function headers, expected types, annotations, explicit
  type arguments, closure/letrec signatures, and `RawCore` embedding. Impl
  method signature validation and duplicate impl key detection compare through
  assoc-aware normalization.
- Rocq has env-aware associated compatibility helpers and checked wrapper
  boundaries for core, env, root, shadow-safe root, function-level, and
  end-to-end checker entrypoints. These wrappers preserve store/root naming,
  no-shadow, parameter root coverage, and final-store param-scope coverage
  without converting back to ordinary `typed_env_roots`. There is also a
  checked assoc-boundary wrapper for general function-value `ECallExpr` paths.
  That wrapper now lives in an executable checker module and is exported for
  extraction; the proof file only proves its checked assoc-boundary soundness.
  Assoc-aware checked core/env/full entrypoints are executable, exported, and
  covered by assoc-boundary soundness. The OCaml CLI uses the extracted
  assoc-aware end-to-end checker as its accept/reject authority, and the
  required end-to-end soundness and base checked-initial-ready theorem names
  point at that active path. The end-to-end safety module now has assoc-aware
  counterparts for the strict-exact closure checker path, sidecar readiness,
  shallow call-route big-step wrappers, component/provider local-bounds facts,
  seen/direct-callee bridges, component-body route/callback providers,
  reachable route package/target providers, callback-height big-step safety,
  provider-style route/callback/store-safe bundles, top-level callback
  wrappers, component-body and local-bounds route-package providers,
  route-package wrappers through prefix-scope consumers, branch-local and
  exact-body branch wrappers, component-body summary-provider wrappers, and
  summary-call-package wrappers. Ordinary baseline theorem names remain
  available under explicit ordinary names.
- Haskell-style `deriving` is reserved for a future surface form. Provisional
  struct/enum deriving syntax is rejected explicitly, and `deriving` is
  reserved as a keyword.

## Remaining Tasks

1. Finish UFCS receiver hardening.
   - Keep the canonical surface syntax as prefix calls with receiver-first
     arguments.
   - Add remaining receiver shapes only when the checker and safety proofs have
     store/root-safe summary evidence. Field-bearing struct literals,
     payload-bearing enum constructors, direct-call receivers, generic
     direct-call receivers, and non-pure locals are still gated.
   - Direct-call receivers are not an OCaml-only switch: existing store-safe
     argument facts assume arg evaluation preserves static root/store shape,
     and a hidden-let receiver lowering still lacks the runtime proof needed by
     the extracted end-to-end safety gate. The next proof step is
     connecting the direct and generic receiver-method runtime replay packages
     into the runtime branch with the existing argument-strip, checked-body,
     return-roots, and hidden-let bridge packages. The raw and hidden cleanup
     evidence is now packaged together, env-level receiver provenance/readiness
     can be transported through package consumers, the conditional hidden-store
     typing helper is available when a preservation-ready replay is in hand,
     final-store cleanup has direct and replay-package consumers once raw/base
     and hidden replay evidence are matched, value consumers can move a typed
     replayed hidden method-call result across hidden cleanup to the raw final
     store, hidden-call value bridges derive that replayed method-call type
     from the typed `ECallGeneric` subexpression plus the method callee summary,
     direct/generic branch-level value wrappers now compose those facts for
     the replay-final witness while accepting typed receiver-call evidence for
     provider wiring, and direct/generic hidden-start-store invariant providers
     now derive the store/root/naming/no-shadow/closure-summary facts needed at
     the replayed method-call start store; the direct and generic paths also
     have checked-initial body-env providers, and checked-initial branch-value
     consumers feed those facts to the replay-final wrappers. Both runtime
     package branches now have checked-initial consumers that compose final-store
     cleanup with their branch-value wrappers, and the direct and generic
     receiver-method sidecar summaries have conditional summary-to-value bridges
     over their package consumers. The next proof step is carrying the preserved
     post-parameter hidden/base `used` relation through the remaining
     expression-body alpha-renaming constructors with the completed list,
     let-binder seed, conditional-chain, let-body, and unary-wrapper helpers
     before using the hidden/base alpha transport with the shared body-final helper to
     complete the direct and generic final-store matching providers before
     wiring the public receiver-method runtime safety branch through those
     providers. Only after the direct and generic receiver-method runtime safety
     branch is proved should the receiver-method summaries be enabled as outer
     alternatives on the public base checker gate.
   - Keep generic trait arguments explicit through `<Ty as Trait<...>>` for this
     roadmap slice.

## Key Decisions

- Rocq definitions are the source of truth. Generated OCaml extraction artifacts
  are not edited manually.
- No handwritten OCaml checker fallback paths are allowed. `ErrNotImplemented`
  from the extracted end-to-end checker is a rejection.
- Parser/desugar may resolve names and build hidden calls, but must not become a
  type-directed trait solver.
- Associated type defaults and equality constraints are out of scope for the
  current implementation pass.
- Dot method calls remain syntax-level rejected until they can desugar to the
  same receiver-first prefix form before Rocq checking.
- Future deriving must expand to ordinary impl declarations validated by the
  extracted checker; no parser-only generated acceptance path is allowed.

## Required Checks

For type-system or checker-facing implementation tasks, run:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|admit\b|Abort\.|TODO|DEBUG|idtac" rocq/theories
```

The final search must not introduce new proof holes or debug leftovers. Existing
legacy proof-script selector matches should be called out explicitly if they
remain unrelated to the change.
