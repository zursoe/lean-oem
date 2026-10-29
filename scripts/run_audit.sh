#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
run_build=true

if [[ "${1:-}" == "--no-build" ]]; then
  run_build=false
fi

cd "$repo_root"

if [[ "$run_build" == true ]]; then
  lake build
fi

printf '%s\n' '-- 公理审计 --'
axiom_output="$(lake env lean LeanOEM/Tests/Axioms.lean 2>&1)"
printf '%s\n' "$axiom_output"

if printf '%s\n' "$axiom_output" | rg -n 'sorryAx|admit'; then
  printf '%s\n' '错误：公理审计发现占位证明。' >&2
  exit 1
fi

printf '%s\n' '-- 占位证明扫描 --'
placeholder_output="$(rg -n '\b(sorry|admit|axiom)\b|sorryAx' \
  LeanOEM LeanOEM.lean LeanOEMTests.lean \
  --glob '*.lean' \
  --glob '!LeanOEM/Tests/Axioms.lean' || true)"

if [[ -n "$placeholder_output" ]]; then
  printf '%s\n' "$placeholder_output" >&2
  printf '%s\n' '错误：源代码发现占位证明或未登记公理。' >&2
  exit 1
fi
printf '%s\n' '源代码没有发现 sorry、admit 或自定义 axiom。'

printf '%s\n' '-- 编译产物跟踪检查 --'
tracked_build_output="$(git ls-files | rg '(^|/)\.lake/|\.(olean|ilean)$' || true)"

if [[ -n "$tracked_build_output" ]]; then
  printf '%s\n' "$tracked_build_output" >&2
  printf '%s\n' '错误：Git 跟踪了本机编译产物。' >&2
  exit 1
fi
printf '%s\n' 'Git 没有跟踪 .lake 或 Lean 编译产物。'

printf '%s\n' '审计通过。'
