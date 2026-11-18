#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
: "${NANODA_BIN:=nanoda_bin}"
: "${PROOF_FILE:=complex_contract_proof.jsonl.gz}"
printf '%s  %s\n' f95f7999e437cc943f0fc2a27828089f8eb800fcb3e720d0923e7a42f19a6319 "$PROOF_FILE" | sha256sum -c -
# The checker opens an existing pretty-printer destination.
touch nanoda_type.txt
gzip -dc "$PROOF_FILE" | "$NANODA_BIN" nanoda.json
