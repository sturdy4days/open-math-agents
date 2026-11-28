#!/usr/bin/env bash
set -euo pipefail

bundle=$(cd -- "$(dirname -- "$0")" && pwd)
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
mkdir -p "$build/OMAStatements"
cd "$build"

commit=c0be4a092d417fd65738fd3672fd0f8026e57de2
raw="https://raw.githubusercontent.com/connoranderson/open-math-agents/$commit"
curl --fail --silent --show-error --location "https://raw.githubusercontent.com/lefttosolve2/open-math-agents/cd9cc5af37093d318091ca0589f6ede67e4986bc/statements/oeis-a230496.lean" -o OMAStatements/S_oeis_a230496.lean
curl --fail --silent --show-error --location "$raw/proofs/oeis-a230496.lean" -o Lead.lean
sha256sum -c <<'DIGESTS'
127ea2adc9d5a0d643ce9fdd42f2a6863931fc327cc6c3e4dcb5a00b69bb79cc  OMAStatements/S_oeis_a230496.lean
c315e5458fcdff5614f841a9b260afd5b1f726bbc5663320818cc66edd4614dd  Lead.lean
DIGESTS
cp -- "$bundle/IPReturns.lean" .
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean -j1 -o OMAStatements/S_oeis_a230496.olean OMAStatements/S_oeis_a230496.lean
lean -j1 -o Lead.olean Lead.lean
lean -j1 -o IPReturns.olean IPReturns.lean
cat > Audit.lean <<'LEAN'
import IPReturns
#print axioms OMA.FiniteSums.exists_sequence
#print axioms OMA.FiniteSums.subsum_injective
#print axioms OMA.OdiousIP.polynomial_ip_returns
#print axioms OMA.OdiousIP.odious_family
LEAN
lean -j1 Audit.lean | tee AxiomAudit.log
python3 - <<'PYTHON'
from pathlib import Path
import re
rows = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",Path("AxiomAudit.log").read_text())
assert len(rows) == 4
assert all(set(map(str.strip, symbols.split(","))) <= {"propext", "Classical.choice", "Quot.sound"} for _,symbols in rows)
PYTHON
