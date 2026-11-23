# Verification scripts

`check_audit.py` is called by the top-level `check.sh`. It compares every
`#print axioms NAME` command in `Audit.lean` against Lean's completed reports,
rejects missing or unexpected reports, and permits only no axioms or a subset
of `propext`, `Classical.choice`, and `Quot.sound`.

It is a mechanical proof/trust check, not a fidelity or theorem-status check.
`docs/PROOF-STATUS.md` supplies the latter. The `.lake/audit-output.txt` file
is generated during verification and should not be published as a source file.
