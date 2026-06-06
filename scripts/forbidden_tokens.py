#!/usr/bin/env python3
"""Reject axiom-laundering tokens in live ArkLib source.

Scans every .lean file under ArkLib/ and fails if live (non-comment) code
contains:
  - `native_decide` / `bv_decide` (kernel-bypassing decision procedures), or
  - a custom `axiom` declaration.

Comment and docstring occurrences are ignored. `sorry`/`admit` are handled
separately by scripts/sorry_census.py --fail-on-holes; this precheck runs
before any Lean toolchain is set up, so CI fails fast on laundering attempts.

Documented residual `axiom` declarations may be explicitly exempted by listing
their declaration name in `scripts/allowed_axioms.txt` (one name per line; `#`
comments allowed). This is the auditable allow-list for deliberate, documented
named residuals (e.g. coding-theory residuals owed by an in-progress port); the
file is the single reviewable place where such exemptions live, so a stray or
undocumented `axiom` still fails the gate. Exempting an axiom here does not make
it sound — it records that the residual is tracked, not laundered.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

TOKEN_RE = re.compile(r"\b(native_decide|bv_decide)\b")
AXIOM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|scoped\s+)*axiom\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
# An `axiom` keyword whose name is not on the same line (rare); still forbidden
# unless allow-listed, but we cannot read a name for it, so it can never match
# the allow-list and therefore always fails (fail-safe).
AXIOM_KW_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|scoped\s+)*axiom\b")


def load_allowed_axioms(root: Path) -> set[str]:
    """Load the allow-list of documented residual axiom names, if present."""
    allow_path = root / "scripts" / "allowed_axioms.txt"
    if not allow_path.is_file():
        return set()
    names: set[str] = set()
    for raw in allow_path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            names.add(line)
    return names


def comment_mask(text: str) -> list[bool]:
    """Return per-char mask: True if the char is inside a comment/docstring."""
    mask = [False] * len(text)
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                mask[k] = True
            i = j
        elif text.startswith("/-", i):
            depth += 1
            mask[i] = mask[i + 1 if i + 1 < n else i] = True
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            mask[i] = mask[i + 1 if i + 1 < n else i] = True
            i += 2
        else:
            if depth > 0:
                mask[i] = True
            i += 1
    return mask


def main() -> int:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    allowed = load_allowed_axioms(root)
    used_allowances: set[str] = set()
    failures: list[str] = []
    exempted: list[str] = []
    for path in sorted((root / "ArkLib").rglob("*.lean")):
        text = path.read_text(encoding="utf-8", errors="replace")
        mask = comment_mask(text)
        for m in TOKEN_RE.finditer(text):
            if not mask[m.start()]:
                line = text.count("\n", 0, m.start()) + 1
                failures.append(f"{path}:{line}: forbidden token {m.group(1)}")
        pos = 0
        for idx, line in enumerate(text.splitlines(True), start=1):
            first_live = next((off for off, ch in enumerate(line) if not ch.isspace()), None)
            if first_live is not None and not mask[pos + first_live] and AXIOM_KW_RE.match(line):
                named = AXIOM_RE.match(line)
                name = named.group(1) if named else None
                if name is not None and name in allowed:
                    exempted.append(f"{path}:{idx}: {name}")
                    used_allowances.add(name)
                else:
                    suffix = f" ({name})" if name else ""
                    failures.append(f"{path}:{idx}: forbidden custom axiom declaration{suffix}")
            pos += len(line)

    # A stale allow-list entry (no longer present in source) is itself a failure:
    # it lets a future re-introduced axiom slip through silently.
    for stale in sorted(allowed - used_allowances):
        failures.append(f"scripts/allowed_axioms.txt: stale allow-list entry '{stale}' "
                        f"(no matching axiom in live source)")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(f"\nFORBIDDEN: {len(failures)} laundering token(s) in live source", file=sys.stderr)
        return 1
    msg = "forbidden-token precheck: clean (no native_decide / bv_decide / unlisted axiom)"
    if exempted:
        msg += f"\n  {len(exempted)} documented residual axiom(s) allow-listed:"
        msg += "".join(f"\n    {e}" for e in exempted)
    print(msg)
    return 0


if __name__ == "__main__":
    sys.exit(main())
