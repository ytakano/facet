#!/bin/sh
set -eu

root_dir=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root_dir"

status=0

normalize_fir_stream() {
  sed 's/\(^\|[^%[:alnum:]_]\)\([[:alpha:]_][[:alnum:]_]*\)#[0-9][0-9]*/\1\2#_/g'
}

normalize_fir_text() {
  printf '%s\n' "$1" | normalize_fir_stream
}

run_case() {
  file=$1
  expected=$2
  tmp=$(mktemp)

  if dune exec ocaml/main.exe -- --emit-fir "$tmp" "$file" >/dev/null 2>&1; then
    expected_norm=$(normalize_fir_text "$expected")
    if normalize_fir_stream < "$tmp" | grep -Fq "$expected_norm"; then
      printf 'ok   %s\n' "$file"
    else
      printf 'FAIL %s: expected FIR to contain %s\n' "$file" "$expected"
      cat "$tmp"
      status=1
    fi
  else
    printf 'FAIL %s: --emit-fir failed\n' "$file"
    status=1
  fi

  rm -f "$tmp"
}

run_drop_case() {
  file=$1
  place=$2
  tmp=$(mktemp)

  if dune exec ocaml/main.exe -- --emit-fir "$tmp" "$file" >/dev/null 2>&1; then
    place_norm=$(normalize_fir_text "$place")
    if normalize_fir_stream < "$tmp" | grep -F "drop " | grep -Fq "$place_norm"; then
      printf 'ok   %s\n' "$file"
    else
      printf 'FAIL %s: expected FIR drop line to contain %s\n' "$file" "$place"
      cat "$tmp"
      status=1
    fi
  else
    printf 'FAIL %s: --emit-fir failed\n' "$file"
    status=1
  fi

  rm -f "$tmp"
}

run_drop_absent() {
  file=$1
  place=$2
  tmp=$(mktemp)

  if dune exec ocaml/main.exe -- --emit-fir "$tmp" "$file" >/dev/null 2>&1; then
    place_norm=$(normalize_fir_text "$place")
    if normalize_fir_stream < "$tmp" | grep -F "drop " | grep -Fq "$place_norm"; then
      printf 'FAIL %s: FIR unexpectedly contained drop of %s\n' "$file" "$place"
      cat "$tmp"
      status=1
    else
      printf 'ok   %s\n' "$file"
    fi
  else
    printf 'FAIL %s: --emit-fir failed\n' "$file"
    status=1
  fi

  rm -f "$tmp"
}

run_case tests/valid/replace/replace_through_nested_ref.facet "replace old#1 as unrestricted isize = **rr#1 as unrestricted isize"
run_case tests/valid/replace/replace_through_immut_bound_nested_mut_ref.facet "replace old#1 as unrestricted isize = **rr#1 as unrestricted isize"
run_case tests/valid/assign/assign_through_nested_ref.facet "= **rr#1 as unrestricted isize with 42"
run_case tests/valid/reborrow/reborrow_mut_from_immut_bound_nested_mut_ref.facet "= &mut **rr#1 as unrestricted isize"
run_case tests/fir/function_value_call.facet "let f#1 as unrestricted fn(unrestricted isize) -> unrestricted isize = closure id#0 as unrestricted fn(unrestricted isize) -> unrestricted isize"
run_case tests/fir/function_value_call.facet "call %t0#0 as unrestricted isize = f#1 as unrestricted fn(unrestricted isize) -> unrestricted isize"
run_case tests/fir/explicit_generic_call.facet "call %t0#0 as affine isize = id#0 (1 as unrestricted isize)"
run_case tests/fir/hrt_function_value_param.facet "call %t0#0 as unrestricted & unrestricted isize = f#1 as unrestricted for<'_0> unrestricted fn(unrestricted & unrestricted isize) -> unrestricted & unrestricted isize"
run_case tests/fir/generic_direct_call.facet "call %t0#0 as affine isize = id#0 (1 as unrestricted isize)"
run_case tests/valid/struct/basic_literal.facet "Pair { x = 1 as unrestricted isize, y = true as unrestricted bool } as unrestricted Pair"
run_case tests/fir/enum_match.facet "match b#1 as unrestricted BoolLike { Yes => match_Yes_"
run_case tests/fir/enum_match.facet "No => match_No_"
run_case tests/fir/enum_no_payload_match_regression.facet "match s#1 as unrestricted Switch { Off => match_Off_"
run_case tests/fir/enum_no_payload_match_regression.facet "On => match_On_"
run_case tests/fir/enum_structural_no_payload_match.facet "match d#1 as unrestricted Direction { North => match_North_"
run_case tests/fir/enum_structural_no_payload_match.facet "West => match_West_"
run_case tests/valid/struct/basic_literal.facet "project %t0#0 as unrestricted isize = p#1.x as unrestricted isize"
run_case tests/fir/struct_field_borrow.facet "borrow %t0#0 = &p#1.y as unrestricted bool"
run_case tests/fir/nested_field_access.facet "project %t0#0 as unrestricted isize = o#1.inner.value as unrestricted isize"
run_case tests/fir/structural_drop.facet "drop %t1#0 as unrestricted unit = p#1.x as affine isize"
run_case tests/fir/structural_drop.facet "drop %t0#0 as unrestricted unit = p#1.y as affine bool"
run_case tests/fir/closure_capture_value.facet "closure __facet_closure"
run_case tests/fir/closure_capture_value.facet "[y#"
run_case tests/fir/closure_capture_value.facet "fn __facet_closure"
run_drop_case tests/fir/auto_drop_affine_scalar.facet "x#1 as affine isize"
run_drop_case tests/fir/auto_drop_affine_struct.facet "p#1.x as affine isize"
run_drop_case tests/fir/auto_drop_affine_struct.facet "p#1.y as affine bool"
run_drop_case tests/fir/auto_drop_partial_struct.facet "p#1.y as affine bool"
run_drop_absent tests/fir/auto_drop_partial_struct.facet "p#1.x as affine isize"
run_case tests/fir/assign_affine_struct_drop_old.facet "replace %t0#0 as affine Pair = p#1 as affine Pair"
run_drop_case tests/fir/assign_affine_struct_drop_old.facet "%t0#0.x as affine isize"
run_drop_case tests/fir/assign_affine_struct_drop_old.facet "%t0#0.y as affine bool"
run_case tests/fir/assign_mut_ref_affine.facet "replace %t1#0 as affine isize = *r#1 as affine isize"
run_drop_case tests/fir/assign_mut_ref_affine.facet "%t1#0 as affine isize"
run_case tests/fir/assign_mut_ref_affine.facet "replace %t1#0 as affine Pair = *r#2 as affine Pair"
run_drop_case tests/fir/assign_mut_ref_affine.facet "%t1#0.x as affine isize"
run_drop_case tests/fir/assign_mut_ref_affine.facet "%t1#0.y as affine bool"
run_case tests/fir/replace_affine_no_immediate_drop.facet " = x#1 as affine isize with 2"
run_drop_absent tests/fir/replace_affine_no_immediate_drop.facet "old#1 as affine isize"

exit "$status"
