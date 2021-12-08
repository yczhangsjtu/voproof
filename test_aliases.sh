prefix="cargo test --release --features print-trace"
postfix="-- --nocapture"
for scale in 1000 2000 4000 8000 16000 32000 64000 128000 256000 512000 1024000; do
  alias tr1cs$scale="$prefix test_simple_r1cs_large_scale_$scale $postfix"
  alias tr1cspe$scale="$prefix test_simple_r1cs_pe_large_scale_$scale $postfix"
  alias tmarlin$scale="$prefix test_marlin_prover_test_circuit_scale_$scale $postfix"
done
alias tr1cssmall="$prefix test_simple_r1cs_small_scales $postfix"
alias tr1cspesmall="$prefix test_simple_r1cs_pe_small_scales $postfix"
