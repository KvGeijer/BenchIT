#!/bin/bash

./COMPILE.SH kernel/memory/latencies/C/0/0/pointerchasing
./RUN.SH bin/memory.latencies.C.0.0.pointerchasing.0 | tee /tmp/run_output.txt

output_dir="./output/memory/latencies/C/0/0/pointerchasing"
filename=$(grep -oP 'Wrote output to "\K[^"]*' /tmp/run_output.txt)
full_path="$output_dir/$filename"

./tools/QUICKVIEW.SH $full_path
