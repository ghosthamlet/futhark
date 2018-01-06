#!/bin/sh
#
# Focus only on getting runtime.  Gathers both CPU and GPU data.

set -ex # Exit on first error, be verbose.

result_dir_base="$1"
if ! [ "$result_dir_base" ]; then
    echo 'error: specify output directory base as first argument' > /dev/stderr
    exit 1
fi

cpu_benchmarks_file="$2"
gpu_benchmarks_file="$3"

#"$(dirname "$0")/gather-data-coarse.sh" "${result_dir_base}-cpu" futhark-c '' '' "$cpu_benchmarks_file"

"$(dirname "$0")/gather-data-coarse.sh" "${result_dir_base}-gpu" futhark-opencl '' '' "$gpu_benchmarks_file"
