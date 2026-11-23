"""Check that the repository's reader guide covers source modules and links."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
modules = sorted(p.stem for p in (root / "FK").glob("*.lean"))
guide = (root / "docs" / "MODULES.md").read_text()
missing = [name for name in modules if f"`{name}`" not in guide]
if missing:
    raise SystemExit(f"Modules missing from docs/MODULES.md: {missing}")
errors = []
for page in [root / "README.md", *sorted((root / "docs").glob("*.md"))]:
    text = page.read_text()
    for target in re.findall(r"\]\(([^)\s]+)\)", text):
        if target.startswith(("http://", "https://", "#")):
            continue
        local = target.split("#")[0]
        if local and not (page.parent / local).is_file():
            errors.append(f"{page.relative_to(root)}: broken link {target}")
if errors:
    raise SystemExit("\n".join(errors))
print(f"Documentation covers {len(modules)} FK modules and has valid internal links.")
