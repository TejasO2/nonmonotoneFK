"""Verify that every requested axiom audit elaborated to an allowed report."""
import collections
import pathlib
import re
import sys

source = pathlib.Path(sys.argv[1]).read_text()
output = pathlib.Path(sys.argv[2]).read_text()
expected = re.findall(r"^#print axioms ([^\s]+)\s*$", source, re.M)
pattern = r"'(?P<name>[^']+)' (?:(?P<depends>depends on axioms): \[(?P<axioms>[^\]]*)\]|(?P<none>does not depend on any axioms))"
allowed = {"propext", "Classical.choice", "Quot.sound"}
found = []
for match in re.finditer(pattern, output, re.S):
    names = match.group("name")
    axioms = {s.strip() for s in match.group("axioms").split(",")} if match.group("depends") else set()
    if not axioms <= allowed:
        raise SystemExit(f"Unexpected axioms for {names}: {sorted(axioms)}")
    found.append(names)
missing = sorted(set(expected) - set(found))
extra = sorted(set(found) - set(expected))
if missing or extra:
    raise SystemExit(f"Audit mismatch: missing={missing}; unexpected={extra}")
if len(expected) != len(set(expected)):
    duplicates = [n for n, count in collections.Counter(expected).items() if count > 1]
    raise SystemExit(f"Duplicate audit declarations: {duplicates}")
if not expected:
    raise SystemExit("No axiom audits were declared")
print(f"Verified {len(found)} declaration audits; only standard Lean axioms were reported.")
