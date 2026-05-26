# Enum/Match Roadmap

## Summary

Add enums and match expressions in staged pieces so the Rocq proofs stay
tractable. The order is:

1. nominal enum types and definitions;
2. enum construction;
3. exhaustive match without payload binders;
4. payload binders and ownership-sensitive branch typing;
5. affine/linear drop integration;
6. reference lifetime coverage;
7. variant-local lifetimes as an existential-lifetime extension.

The first implementation should support enum-level generics, trait bounds, and
reference lifetimes. Variant-local lifetimes are intentionally later because
they require branch-local lifetime opening and escape checks.

## Phase 1: Nominal Enum Types

Add enum types parallel to struct types.

Status: implemented in the Rocq core model/checker/extraction path. Surface
enum syntax and enum construction are intentionally left for later phases.

- Add `TEnum name lifetime_args type_args` beside `TStruct`.
- Add `enum_def` and `enum_variant_def` to the global program model.
- Extend `global_env` with `env_enums` and enum lookup helpers.
- Add duplicate-name checks for enum names and per-enum variant names.
- Add lifetime/type arity checks for enum uses.
- Extend type operations for `TEnum`:
  - lifetime substitution;
  - lifetime mapping;
  - bound-lifetime containment;
  - type equality;
  - type compatibility;
  - well-formedness;
  - capture-ref-free checks.

Surface syntax target:

```facet
enum Option<T> where T: Show {
  Some(affine T),
  None,
}

enum Borrowed<'a, T> {
  Ref(unrestricted &'a affine T),
  Empty,
}
```

Trait bounds and outlives constraints should reuse the existing function and
struct machinery. Do not introduce trait-solver search for enums.

## Phase 2: Enum Construction

Add value construction before match.

Status: implemented. Core/surface construction, runtime `VEnum`, checker
branches, FIR emission, borrow traversal, runtime ref safety, preservation/root
proofs, extraction, and valid/invalid regression tests are in place.

- Add a core expression for variant construction, such as
  `EEnum enum_name variant_name lifetime_args type_args args`.
- Add a raw/surface expression for `Enum::Variant(...)` or an equivalent
  unambiguous constructor syntax.
- Type-check constructor payload expressions against the instantiated variant
  field types.
- Check enum type/lifetime arity, trait bounds, and outlives constraints at
  construction sites.
- Runtime values should carry the enum name, variant name, and payload values;
  type and lifetime args remain erased.
- FIR emission currently preserves a primitive enum constructor operation.

Implementation notes kept for future phases:

- `VHT_Enum` depends on `enum_values_have_type`, the third mutual predicate of
  runtime typing. Future enum runtime proofs should recurse through that
  predicate instead of treating payloads as untyped.
- `runtime_refs_wf` recurses through enum payloads. New enum operations that
  expose or transform payloads must preserve this invariant.
- Borrow checking traverses constructor payloads through `BO_Enum` and
  `borrow_ok_args`.

Initial valid cases:

```facet
enum BoolLike {
  Yes,
  No,
}

fn yes() -> unrestricted BoolLike {
  BoolLike::Yes()
}
```

Initial invalid cases:

- unknown enum;
- unknown variant;
- constructor arity mismatch;
- unsatisfied trait bound;
- unsatisfied outlives bound.

## Phase 3: Exhaustive Match Without Payload Binders

Add simple match on no-payload variants.

Status: implemented. Core/surface `EMatch`, no-payload exhaustive checking,
root-aware and shadow-safe checker paths, structural soundness, readiness,
preservation/root proofs, FIR emission, extraction, and regression tests are in
place.

Implemented constraints:

- `match scrut { Variant => expr, ... }` consumes the scrutinee by value.
- The scrutinee must type to `TEnum`.
- Branches are checked in enum definition order.
- Duplicate, unknown, missing, and payload-carrying variants are rejected.
- Branch result core types must match and branch output contexts are merged.
- Nested patterns, guards, wildcard branches, by-reference patterns, payload
  binders, and place-pattern matching remain out of scope.

Important proof invariant:

- Prop-level match typing rejects unknown branch names. This is required for
  runtime preservation because `Eval_MatchEnum` selects branches by runtime
  variant name, and preservation must derive that the selected branch
  corresponds to an enum definition variant.

Surface syntax target:

```facet
fn to_int(x: unrestricted BoolLike) -> unrestricted isize {
  match x {
    Yes => 1,
    No => 0,
  }
}
```

This phase should prove branch exhaustiveness and branch result compatibility
before adding payload ownership.

## Phase 4: Payload Binders and Ownership

Add variant payload destructuring.

Status: partially implemented as parser/core groundwork only. Match branches
now carry payload binder lists through Rocq syntax, checker extraction, parser,
de Bruijn conversion, and FIR integration. Non-empty branch binders are parsed
but intentionally rejected by the checker as `ErrMatchPayloadUnsupported`, and
FIR lowering also guards against them. Prop-level match typing still requires
empty binders, so payload ownership typing/runtime semantics remain pending.

- Extend match branches with payload binder lists.
- Instantiate the selected variant payload types from the scrutinee `TEnum`.
- Add payload binders to the branch context.
- Linear payloads must be consumed in the branch where they are bound.
- Affine payloads may be dropped.
- Unrestricted payloads behave like ordinary unrestricted bindings.
- Merge branch contexts using the same discipline as `if`, adjusted for
  payload binders that are scoped only inside the branch.
- Do not allow moving payloads out through borrowed enum places.

Example:

```facet
enum Option<T> {
  Some(affine T),
  None,
}

fn unwrap_or(x: affine Option<affine isize>, default: affine isize)
  -> affine isize {
  match x {
    Some(v) => v,
    None => default,
  }
}
```

Invalid cases:

- payload binder arity mismatch;
- linear payload not consumed;
- branch result type mismatch;
- use of scrutinee after match when it was consumed.

Completed groundwork:

- Core `EMatch` and raw `RawMatch` branches carry `(variant, binders, body)`.
- Surface syntax accepts both `Variant => expr` and `Variant(x, y) => expr`.
- Runtime `VEnum` carries erased enum lifetime/type args:
  `VEnum enum_name variant_name lts args payloads`.
- No-payload match behavior is preserved by structural, roots, shadow-safe
  roots, readiness, preservation, runtime soundness, borrow soundness, and
  initial root facts.
- Non-empty branch binders are rejected before they can be treated as ordinary
  in-scope variables.
- Regression coverage checks no-payload match still succeeds and payload binder
  syntax is rejected until ownership-sensitive payload typing is implemented.

Remaining work:

- Keep payload branch execution as:
  `bind_params ps payloads s_scrut`, evaluate the selected branch, then
  `store_remove_params ps` from the branch result store.
- Keep `match_payload_params_opt` in the shared pre-`OperationalSemantics`
  layer; keep checker-facing `match_payload_params` as an `infer_result`
  wrapper.
- Current blocker for real payload ownership: `TypeSafetyBasePreservationMutual.v`
  is too weak for payload cleanup. After branch evaluation, preservation must
  justify `store_remove_params ps_payload s_branch`, but the base theorem does
  not carry the root/scope evidence needed to prove surviving values do not
  reference removed payload params.
- Do not remove the no-payload premises from Prop-level match typing until the
  preservation theorem is refactored. A proof-first attempt showed the old
  helper `typed_match_tail_lookup_no_payload` becomes false as soon as
  payload binders are allowed, and both base and prefix preservation currently
  depend on that no-payload fact to type the runtime branch store.
- The next proof step should introduce a payload-aware preservation package for
  match branches. It must relate runtime payload params (`ps_payload`) to typed
  branch params (`ps_head`/`ps_branch`) by binder names and exact store-entry
  types, then prove branch-result cleanup using root/scope evidence before the
  checker accepts non-empty binders.
- `TypeSafetyHiddenFrameCleanupFacts.v` now has a focused helper packaging the
  payload cleanup fact needed for returned-value typing after
  `store_remove_params`.
- Remaining blocker: wire that helper into `TypeSafetyBasePreservationMutual.v`
  to preserve store/context facts for `store_remove_params ps_payload s_branch`,
  using the exact payload param types from `match_payload_params_opt`, then
  remove obsolete no-payload shortcuts.

## Phase 5: Drop Lowering

Integrate enums with affine/linear drop.

- Extend structural drop helpers from structs to enums.
- For affine enum values, lower drop as variant dispatch that drops live payload
  fields for the actual variant.
- Linear enum values are not auto-dropped and remain ordinary consumption
  obligations.
- Extend assignment and replace old-value handling so affine enum old values are
  structurally dropped after the old value is produced.
- FIR may initially use a primitive `drop enum` operation if variant dispatch
  FIR is not yet available, but the roadmap should keep the target semantics as
  variant-specific payload dropping.

Regression coverage should include:

- scope-end affine enum drop;
- enum with affine payload drop;
- enum with partially consumed payload after match;
- assignment old-value drop for affine enum;
- mutable-reference assignment old-value drop for affine enum.

## Phase 6: Reference Lifetimes

Make enum-level lifetimes work through construction and match.

- Payload references may mention enum-level lifetime params.
- Construction instantiates payload reference lifetimes from the enum type args.
- Match payload binders preserve the instantiated reference lifetime.
- Outlives constraints on enum definitions must be checked at use sites.
- Branch result types must not leak lifetimes that are not available in the
  surrounding function context.

Example:

```facet
enum RefBox<'a, T> where T: Show {
  Ref(unrestricted &'a affine T),
  Empty,
}

fn get<'a, T>(x: affine RefBox<'a, T>)
  -> unrestricted &'a affine T {
  match x {
    Ref(r) => r,
    Empty => /* rejected until a valid same-type value exists */,
  }
}
```

Invalid cases:

- enum use with unknown lifetime;
- enum outlives bound not satisfied;
- returned reference lifetime not available outside the branch/function.

## Phase 7: Variant-Local Lifetimes

Add variant-local lifetimes after enum-level lifetimes and match are stable.
This is an existential-lifetime feature, not just more generic syntax.

Syntax target:

```facet
enum E<T> {
  Borrowed<'a>(unrestricted &'a affine T),
  Owned(affine T),
}
```

Semantics:

- `Borrowed<'a>(...)` stores a value whose lifetime is hidden inside the enum.
- Matching `Borrowed(r)` opens a fresh branch-local abstract lifetime.
- The opened lifetime may be used inside that branch.
- The opened lifetime must not escape through the branch result unless it is
  proven to be tied to an outer lifetime.
- Variant-local outlives bounds should be added only after basic existential
  unpacking is proven.

Required proof/checker additions:

- variant-local lifetime binders on `enum_variant_def`;
- branch-local lifetime context extension;
- opened-lifetime escape checks for match branch result types;
- no unresolved opened lifetime in merged match result;
- runtime/FIR erasure of variant-local lifetime evidence.

Invalid cases:

```facet
enum Hidden<T> {
  Borrowed<'a>(unrestricted &'a affine T),
}

fn leak<T>(x: affine Hidden<T>) -> unrestricted &'static affine T {
  match x {
    Borrowed(r) => r, // reject: branch-local lifetime escapes
  }
}
```

## Required Checks

Run these before marking any phase complete:

```sh
cd rocq && make
dune build
sh tests/run.sh
sh tests/fir/run.sh
git diff --check
rg -n "\bAxiom\b|Admitted\.|admit\b|Abort\.|[D]EBUG|idtac" rocq/theories
```

The final `rg` should not report new proof holes or debug leftovers. Existing
legacy proof-script selectors should be documented if they remain.

## Assumptions

- Enum-level lifetimes cover v1 reference payloads.
- Variant-local lifetimes are existential and branch-local.
- Match consumes the scrutinee by value in the first implementation.
- By-reference patterns, guards, nested patterns, wildcard branches, and
  partial move from enum places are out of scope until simple match and enum
  drop are proven.
- Trait-bound inference remains syntactic, matching the current function
  generics implementation.
