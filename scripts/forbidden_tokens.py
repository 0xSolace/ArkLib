#!/usr/bin/env python3
"""Reject axiom-laundering tokens in live ArkLib source.

By default, scans every .lean file under ArkLib/. If one or more paths are
provided, scans only those Lean files/directories. Fails if live
(non-comment) code contains:
  - `native_decide` / `bv_decide` (kernel-bypassing decision procedures), or
  - a custom `axiom` declaration whose name is not an allowlisted, documented
    residual (see scripts/residual_axioms.txt), or
  - a residual-named theorem/lemma/def whose result type is `True`, which is a
    vacuous proof placeholder rather than a residual obligation.

Comment and docstring occurrences are ignored. `sorry`/`admit` are handled
separately by scripts/sorry_census.py --fail-on-holes; this precheck runs
before any Lean toolchain is set up, so CI fails fast on laundering attempts.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Optional

TOKEN_RE = re.compile(r"\b(native_decide|bv_decide)\b")
# Capture the declared axiom name so it can be checked against the residual
# allowlist. The name may be namespaced/contain primes; we keep the simple
# token as written at the declaration site.
AXIOM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|scoped\s+)*axiom\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|scoped\s+)*"
    r"(?:theorem|lemma|def)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
TRUE_RESULT_RE = re.compile(r":\s*\(?\s*True\s*\)?\s*$", re.S)

ALLOWLIST_PATH = Path(__file__).resolve().parent / "residual_axioms.txt"


def load_allowlist(path: Path) -> set[str]:
    """Names of documented residual axioms permitted in live source."""
    if not path.exists():
        return set()
    names: set[str] = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            names.add(line.split()[0])
    return names


def scan_plan(args: list[str]) -> tuple[list[Path], bool, list[str]]:
    """Return files to scan, whether this is a full-ArkLib scan, and path errors."""
    if not args:
        return sorted(Path("ArkLib").rglob("*.lean")), True, []

    files: set[Path] = set()
    full_arklib_scan = False
    errors: list[str] = []
    arklib_root = Path("ArkLib").resolve()

    for raw in args:
        path = Path(raw)
        if not path.exists():
            errors.append(f"{path}: path does not exist")
            continue
        if path.is_file():
            if path.suffix == ".lean":
                files.add(path)
            else:
                errors.append(f"{path}: expected a .lean file")
            continue

        nested_arklib = path / "ArkLib"
        if nested_arklib.is_dir():
            files.update(nested_arklib.rglob("*.lean"))
            full_arklib_scan = True
        else:
            files.update(path.rglob("*.lean"))
            if path.resolve() == arklib_root:
                full_arklib_scan = True

    return sorted(files), full_arklib_scan, errors


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


def live_text_with_comments_blank(text: str, mask: list[bool]) -> str:
    """Return text with comment/docstring chars replaced by spaces."""
    return "".join(" " if mask[i] else ch for i, ch in enumerate(text))


def declaration_header_before_value(live_text: str, start: int) -> Optional[str]:
    """Return the live declaration header before `:=`, capped before the next declaration."""
    next_value = live_text.find(":=", start)
    if next_value == -1:
        return None
    next_decl = re.search(r"\n\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|scoped\s+)*"
                          r"(?:axiom|theorem|lemma|def)\s+", live_text[start + 1:next_value])
    if next_decl is not None:
        return None
    return live_text[start:next_value].strip()


def is_residual_name(name: str) -> bool:
    return "residual" in name.lower()


def main() -> int:
    files, full_arklib_scan, path_errors = scan_plan(sys.argv[1:])
    if path_errors:
        print("\n".join(path_errors), file=sys.stderr)
        return 1

    allowlist = load_allowlist(ALLOWLIST_PATH)
    failures: list[str] = []
    allowed_hits: list[str] = []
    seen_allowed: set[str] = set()
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        mask = comment_mask(text)
        live_text = live_text_with_comments_blank(text, mask)
        for m in TOKEN_RE.finditer(text):
            if not mask[m.start()]:
                line = text.count("\n", 0, m.start()) + 1
                failures.append(f"{path}:{line}: forbidden token {m.group(1)}")
        pos = 0
        for idx, line in enumerate(text.splitlines(True), start=1):
            first_live = next((off for off, ch in enumerate(line) if not ch.isspace()), None)
            if first_live is None or mask[pos + first_live]:
                pos += len(line)
                continue
            am = AXIOM_RE.match(line)
            if am:
                name = am.group(1)
                if name in allowlist:
                    seen_allowed.add(name)
                    allowed_hits.append(f"{path}:{idx}: allowed documented residual axiom {name}")
                else:
                    failures.append(
                        f"{path}:{idx}: forbidden custom axiom declaration {name} "
                        f"(add to scripts/residual_axioms.txt only if it is a documented, "
                        f"tracked residual)"
                    )
            dm = DECL_RE.match(line)
            if dm:
                name = dm.group(1)
                if is_residual_name(name):
                    header = declaration_header_before_value(live_text, pos)
                    if header is not None and TRUE_RESULT_RE.search(header):
                        failures.append(
                            f"{path}:{idx}: forbidden vacuous residual declaration {name} "
                            "with result type True"
                        )
            pos += len(line)

    stale = sorted(allowlist - seen_allowed)
    if full_arklib_scan and stale:
        print(
            "WARNING: residual_axioms.txt entries match no live axiom (discharged? "
            "remove the line): " + ", ".join(stale),
            file=sys.stderr,
        )

    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(f"\nFORBIDDEN: {len(failures)} laundering token(s) in live source", file=sys.stderr)
        return 1
    if allowed_hits:
        print("\n".join(allowed_hits))
    print(
        "forbidden-token precheck: clean (no native_decide / bv_decide / "
        f"undocumented custom axiom; {len(allowed_hits)} allowlisted residual axiom(s))"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
