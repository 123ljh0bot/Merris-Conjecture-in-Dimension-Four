#!/usr/bin/env bash

set -euo pipefail

project_dir=$(cd "$(dirname "$0")/.." && pwd)
log_dir="$project_dir/.lake/merris_n4_logs"
parallel_jobs=${MERRIS_N4_LEAN_JOBS:-4}

mkdir -p "$log_dir"
cd "$project_dir"

echo "Building shared block data with $parallel_jobs-way slice concurrency"
lake build \
  +MerrisN4.Block0Base \
  +MerrisN4.Block1Base \
  +MerrisN4.Block2Base \
  +MerrisN4.Block3Base

build_slice() {
  local module=$1
  local safe_name=${module//./_}
  local log_file="$MERRIS_N4_LOG_DIR/$safe_name.log"
  local start_time=$SECONDS
  if lake build "+$module" >"$log_file" 2>&1; then
    echo "PASS $module $((SECONDS - start_time))s"
  else
    echo "FAIL $module"
    tail -n 40 "$log_file"
    return 1
  fi
}

export -f build_slice
export MERRIS_N4_LOG_DIR="$log_dir"

modules=()
for block in 0 1; do
  count=$((block == 0 ? 8 : 16))
  for ((slice = 0; slice < count; slice++)); do
    modules+=("MerrisN4.Block${block}.Slice${slice}")
  done
done
for block in 2 3; do
  for ((slice = 0; slice < 24; slice++)); do
    modules+=("MerrisN4.Block${block}.Slice${slice}")
  done
done

printf '%s\0' "${modules[@]}" |
  xargs -0 -n 1 -P "$parallel_jobs" bash -c 'build_slice "$1"' _

echo "Building block aggregates"
lake build \
  +MerrisN4.Block0 \
  +MerrisN4.Block1 \
  +MerrisN4.Block2 \
  +MerrisN4.Block3

echo "Building final theorem"
lake build +MerrisN4.Root
