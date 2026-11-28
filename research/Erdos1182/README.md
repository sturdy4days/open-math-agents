# The finite upper bounds in Erdos problem 1182

Lean certifies all 22 upper bounds in the table of the two extremal functions at orders 2 through 12. The full equalities use the remaining sparse classification and maximal triangle-free census hypotheses. `E1182Complete.fixed_hosts` discharges H4 of the original public second reduction. `E1182Portfolio.forced11` and `forced12` identify necessary catalogue members.

The manifest lists each source and its verification object checksum in dependency order. The checked finite results use the three standard Lean axioms. The order-twelve case is a modular proof. This archive reproduces that proof using separate Lean modules.

Set `LEAN` to the pinned Lean 4.33.1 binary and `LEAN_PATH` to the genuine mathlib, formal-conjectures and package build directories for the same release. Then run `python3 replay.py`. The archive includes the original formal statement, the published reduction, both graph searches, the exact finite certificates and the final audits.

The Formal Conjectures pin is 9097e2f90e66 and the Mathlib pin is 0df444a360eaa60ab8c11dca51a86af692955474.

Archive SHA-256: cfc6d68aca90787681d706f326c09f79af49d6912f4b15af0a86d87b98cffdf6
