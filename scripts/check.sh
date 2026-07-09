#!/usr/bin/env bash
# check.sh — 證明輔助工具：一鍵 build + sorry 掃描 + axiom 檢查（硬規則守門）
#
# 用法：
#   scripts/check.sh                      # 只 build + 掃 sorry
#   scripts/check.sh decl1 decl2 ...      # 額外印指定宣告的 axioms + 硬規則檢查
#
# 硬規則：零 sorry + 零自訂 axiom（只准 propext / Classical.choice / Quot.sound）。
# 本工具把每塊 verified brick 的收尾（先前手寫 AxCheck.lean→印→刪）自動化。
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

STD='propext|Classical.choice|Quot.sound'

echo "== lake build =="
build_out=$(lake build 2>&1)
build_rc=$?
if [ $build_rc -ne 0 ]; then
  echo "$build_out" | grep -E "error|unsolved|Type mismatch" | head -20
  echo "❌ build FAILED (rc=$build_rc)"
  exit 1
fi
echo "$build_out" | grep -E "Build completed" | tail -1

sorry_n=$(printf '%s\n' "$build_out" | grep -cE "declaration uses .sorry")
if [ "$sorry_n" -eq 0 ]; then
  echo "✓ sorry: 0"
else
  echo "⚠ sorry: $sorry_n"
  printf '%s\n' "$build_out" | grep -E "declaration uses .sorry" | head
fi

warn_n=$(printf '%s\n' "$build_out" | grep -icE "warning:")
[ "$warn_n" -gt 0 ] && echo "⚠ warnings: $warn_n (跑 lake build 看細節)"

if [ $# -gt 0 ]; then
  echo "== axioms（$# 個宣告）=="
  tmp="FluidTuringLean/_AxCheck.lean"
  { echo "import FluidTuringLean"; echo "open FluidTuring"; for d in "$@"; do echo "#print axioms $d"; done; } > "$tmp"
  ax_out=$(lake env lean "$tmp" 2>&1)
  rm -f "$tmp"
  # 逐行判斷：非標準三公理 or sorryAx = 硬規則違反
  bad=0
  while IFS= read -r line; do
    case "$line" in
      *"depends on axioms"*)
        # 抽出 [ ... ] 裡的 axiom，剔除標準三者，剩下的即違規
        extras=$(printf '%s\n' "$line" | grep -oE '\[[^]]*\]' | tr ',[]' '\n' | sed 's/ //g' \
                 | grep -vE "^($STD)$" | grep -v '^$')
        if [ -n "$extras" ]; then
          echo "⚠ $line"
          echo "   ↳ 非標準 axiom: $(printf '%s ' $extras)"
          bad=1
        else
          echo "✓ $line"
        fi
        ;;
      *sorryAx*) echo "❌ $line"; bad=1 ;;
      *error*) echo "❌ $line"; bad=1 ;;
    esac
  done <<< "$ax_out"
  [ "$bad" -eq 0 ] && echo "✓ 全部僅標準三公理、無 sorryAx、無自訂 axiom"
fi

echo "== done =="
[ "$sorry_n" -eq 0 ] && exit 0 || exit 2
