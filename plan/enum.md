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

Status: core Phase 3 path implemented for ordinary structural checking,
runtime preservation, frontend parsing, and FIR emission. Root/shadow-safe
checker variants intentionally still reject `EMatch` until a dedicated
Prop-level `typed_env_roots` match rule is designed and proved; do not widen
those root checker branches without adding that rule first.

- Add `EMatch scrutinee branches`.
- Require the scrutinee type to be `TEnum`.
- Require one branch per enum variant.
- Reject duplicate branches.
- Reject unknown variant branches.
- Reject missing variant branches.
- Reject payload variants in this phase.
- Require all branch result types to be compatible.
- Treat `match x` as consuming the scrutinee value.
- Do not support nested patterns, guards, wildcard branches, by-reference
  patterns, or place-pattern matching in this phase.

Implementation order:

1. Add the Prop specification first:
   - add `T_Match` in `TypingRules.v`;
   - add a helper such as `typed_match_branches` that walks enum variants in
     enum definition order;
   - require `lookup_branch` for each variant;
   - require every matched variant to have no payload fields;
   - type every branch from the same post-scrutinee context;
   - require all branch result core types to match;
   - merge branch output contexts with the same discipline as `T_If`;
   - compute result usage with the max of branch result usages.
2. Align the executable checker with that Prop rule:
   - keep branch processing in enum definition order;
   - mirror duplicate, unknown, missing, payload, type, and context errors;
   - do not accept a checker success case that cannot construct `T_Match`.
3. Add structural/soundness counterparts:
   - extend `EnvStructuralRules.v` for structural match;
   - connect `CheckerSoundness.v` and `EnvTypingSoundness.v` to match;
   - keep root/shadow-safe match unsupported until its Prop rule exists;
   - only use `discriminate` for genuinely impossible or intentionally
     unsupported checker cases.
4. Extend readiness/provenance/preservation:
   - add `PRE_Match` and branch lookup readiness lemmas;
   - handle `Eval_MatchEnum` in preservation/root proofs;
   - keep payload binders out of this phase.
5. Finish frontend/FIR/tests after the verified checker path compiles:
   - parser syntax is `match scrut { Variant => expr, ... }`;
   - FIR may use a primitive enum match dispatch for no-payload variants;
   - tests must cover valid exhaustive match and invalid missing, duplicate,
     unknown, payload, non-enum scrutinee, and branch type mismatch cases.

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
rg -n "\bAxiom\b|Admitted\.|admit\b|Abort\.|TODO|DEBUG|idtac" rocq/theories
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
