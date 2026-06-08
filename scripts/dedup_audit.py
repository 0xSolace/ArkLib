#!/usr/bin/env python3
"""Duplication / similarity audit for the ArkLib Lean sources.

Finds opportunities to deduplicate, unify, and simplify by surfacing:

  1. Duplicate declaration *names*    (same fully-qualified name in >1 place)
  2. Duplicate declaration *proofs*   (byte-identical proof bodies, modulo whitespace)
  3. Recurring proof-*line* patterns  (single lines / short proofs that repeat a lot)
  4. Duplicate *file* basenames       (same filename under different directories)
  5. Near-duplicate *signatures*      (same name stem + same statement, different proof)

Pure stdlib, read-only. Intended to be run from the repo root:

    python3 scripts/dedup_audit.py            # human summary
    python3 scripts/dedup_audit.py --json out.json
    python3 scripts/dedup_audit.py --top 40   # widen the recurring-line table

The goal is signal, not a build gate: the output is a worklist for manual DRYing.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

# Declaration keywords that introduce a named, top-level statement we care about.
DECL_RE = re.compile(
    r"^(?P<indent>\s*)"
    r"(?P<mods>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<kw>theorem|lemma|def|abbrev|instance)\s+"
    r"(?P<name>[^\s({\[:=]+)",
)

PROOF_START_RE = re.compile(r":=\s*(?:by\b|$)|^\s*by\b")

NS_OPEN_RE = re.compile(r"^\s*namespace\s+([\w.]+)")
NS_END_RE = re.compile(r"^\s*end\s+([\w.]+)\s*$")
SECTION_RE = re.compile(r"^\s*section\b")

# Lines that sit *between* declarations (modifiers, section structure, comments).
# When they trail a parsed block they belong to the NEXT decl, so we trim them.
BETWEEN_DECL_RE = re.compile(
    r"^\s*(?:"
    r"end\b|namespace\b|section\b|variable\b|attribute\b|"
    r"open\b.*\bin\s*$|omit\b.*\bin\s*$|set_option\b.*\bin\s*$|"
    r"@\[[^\]]*\]\s*$|--|/-|-/|/-!"
    r")"
)

# Noise lines we don't want polluting the "recurring proof line" histogram.
TRIVIAL_LINES = {
    "by", "·", "<;>", "intro", "constructor", "exact?", "simp", "rfl",
    "done", "sorry", "ring", "omega", "decide", "trivial", "rfl)",
}


@dataclass
class Decl:
    name: str            # leaf name as written
    fqn: str             # namespace-qualified name (best effort)
    kind: str
    file: str
    line: int
    signature: str          # text from keyword up to `:=` (statement type)
    body: str               # raw proof/definition body text
    body_norm: str          # whitespace-normalized body

    @property
    def stem(self) -> str:
        """Final dotted component, e.g. `Foo.bar.baz` -> `baz`."""
        return self.fqn.rsplit(".", 1)[-1]


def normalize(text: str) -> str:
    """Collapse all runs of whitespace to single spaces; strip ends."""
    return re.sub(r"\s+", " ", text).strip()


def split_signature_body(block: str) -> tuple[str, str]:
    """Split a declaration block into (signature, body) at the top-level `:=`.

    Best-effort: respects (), {}, [] nesting and skips `:=` inside them so that
    e.g. structure-instance defaults don't fool us. Falls back to the first
    `:=` if no balanced one is found.
    """
    depth = 0
    i = 0
    n = len(block)
    first = -1
    while i < n - 1:
        c = block[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and block[i + 1] == "=":
            if first < 0:
                first = i
            if depth <= 0:
                return block[:i], block[i + 2:]
            i += 2
            continue
        i += 1
    if first >= 0:
        return block[:first], block[first + 2:]
    return block, ""


def rel_to(path: Path, base: Path) -> str:
    """Path relative to `base` if possible, else to `base.parent` (so a scan
    root of `.../ArkLib` yields clickable `ArkLib/Data/...` paths)."""
    try:
        return str(path.relative_to(base.parent))
    except ValueError:
        return str(path.relative_to(base))


def parse_file(path: Path, root: Path) -> list[Decl]:
    rel = rel_to(path, root)
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    decls: list[Decl] = []

    # Mask out lines whose start is inside a `/- ... -/` block comment, so the
    # decl keywords (`lemma`, `theorem`, ...) appearing in prose don't parse as
    # declarations. Tracks nested block comments.
    in_block = [False] * len(lines)
    depth = 0
    for idx, line in enumerate(lines):
        in_block[idx] = depth > 0
        j = 0
        while j < len(line) - 1:
            two = line[j:j + 2]
            if two == "/-":
                depth += 1
                j += 2
                continue
            if two == "-/" and depth > 0:
                depth -= 1
                j += 2
                continue
            j += 1

    # Track the namespace stack so we can build fully-qualified names. `end`
    # without a name closes a `section`; `end Foo` closes `namespace Foo`.
    ns_at_line: list[list[str]] = []
    ns_stack: list[str] = []
    for line in lines:
        nm = NS_OPEN_RE.match(line)
        em = NS_END_RE.match(line)
        if nm:
            ns_stack.append(nm.group(1))
        elif em and ns_stack and ns_stack[-1].split(".")[-1] == em.group(1).split(".")[-1]:
            ns_stack.pop()
        ns_at_line.append(list(ns_stack))

    starts: list[tuple[int, re.Match]] = []
    for idx, line in enumerate(lines):
        if in_block[idx]:
            continue
        m = DECL_RE.match(line)
        if m and not line.lstrip().startswith("--"):
            starts.append((idx, m))

    for si, (idx, m) in enumerate(starts):
        end = starts[si + 1][0] if si + 1 < len(starts) else len(lines)
        block_lines = lines[idx:end]
        # Drop trailing lines that actually introduce the NEXT declaration
        # (modifiers, namespace/section structure, comments). Otherwise they
        # leak into this decl's body and pollute the dedup/line analyses.
        while block_lines and (
            not block_lines[-1].strip()
            or BETWEEN_DECL_RE.match(block_lines[-1])
        ):
            block_lines.pop()
        block = "\n".join(block_lines).rstrip()
        sig, body = split_signature_body(block)
        leaf = m.group("name")
        ns = ".".join(ns_at_line[idx])
        fqn = f"{ns}.{leaf}" if ns else leaf
        decls.append(
            Decl(
                name=leaf,
                fqn=fqn,
                kind=m.group("kw"),
                file=rel,
                line=idx + 1,
                signature=normalize(sig),
                body=body,
                body_norm=normalize(body),
            )
        )
    return decls


def gather(root: Path) -> list[Decl]:
    decls: list[Decl] = []
    for path in sorted(root.rglob("*.lean")):
        if any(part in (".lake", "blueprint", "home_page") for part in path.parts):
            continue
        try:
            decls.extend(parse_file(path, root))
        except Exception as exc:  # pragma: no cover - defensive
            print(f"!! failed to parse {path}: {exc}", file=sys.stderr)
    return decls


# ---------------------------------------------------------------------------
# Analyses
# ---------------------------------------------------------------------------

def dup_names(decls: list[Decl]) -> dict:
    """Same *fully-qualified* name in more than one location (true collisions)."""
    by_name: dict[str, list[Decl]] = defaultdict(list)
    for d in decls:
        by_name[d.fqn].append(d)
    groups = {n: ds for n, ds in by_name.items() if len(ds) > 1}
    # Also same final stem across different namespaces (weaker signal).
    by_stem: dict[str, set[str]] = defaultdict(set)
    for d in decls:
        by_stem[d.stem].add(d.fqn)
    stem_groups = {
        s: sorted(ns) for s, ns in by_stem.items() if len(ns) > 1
    }
    return {"exact": groups, "stem": stem_groups}


def dup_proofs(decls: list[Decl]) -> dict:
    """Byte-identical (whitespace-normalized) proof bodies, length-gated."""
    by_body: dict[str, list[Decl]] = defaultdict(list)
    for d in decls:
        b = d.body_norm
        if len(b) < 25:
            continue
        h = hashlib.sha1(b.encode()).hexdigest()
        by_body[h].append(d)
    return {h: ds for h, ds in by_body.items() if len(ds) > 1}


def recurring_lines(decls: list[Decl], min_count: int) -> Counter:
    """Histogram of individual proof lines across all bodies."""
    counter: Counter = Counter()
    for d in decls:
        for raw in d.body.splitlines():
            line = raw.strip()
            if not line or line in TRIVIAL_LINES:
                continue
            if line.startswith("--") or line.startswith("/-"):
                continue
            if len(line) < 12:
                continue
            counter[line] += 1
    return Counter({k: v for k, v in counter.items() if v >= min_count})


def dup_files(root: Path) -> dict:
    by_base: dict[str, list[str]] = defaultdict(list)
    for path in root.rglob("*.lean"):
        if any(part in (".lake", "blueprint", "home_page") for part in path.parts):
            continue
        by_base[path.name].append(rel_to(path, root))
    return {b: sorted(ps) for b, ps in by_base.items() if len(ps) > 1}


def same_statement(decls: list[Decl]) -> dict:
    """Same stem + same normalized statement but proofs differ or locations differ.

    These are the strongest unification candidates: two places proving the
    *same theorem* (identical type), possibly with different proofs.
    """
    by_key: dict[str, list[Decl]] = defaultdict(list)
    for d in decls:
        if d.kind not in ("theorem", "lemma"):
            continue
        if len(d.signature) < 20:
            continue
        key = f"{d.stem}|{d.signature}"
        by_key[key].append(d)
    out = {}
    for key, ds in by_key.items():
        if len(ds) > 1:
            proofs = {d.body_norm for d in ds}
            out[key] = {
                "decls": ds,
                "identical_proofs": len(proofs) == 1,
            }
    return out


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def loc(d: Decl) -> str:
    return f"{d.file}:{d.line}"


def report(decls: list[Decl], root: Path, top: int) -> dict:
    names = dup_names(decls)
    proofs = dup_proofs(decls)
    lines = recurring_lines(decls, min_count=8)
    files = dup_files(root)
    stmts = same_statement(decls)

    print(f"\n{'='*72}")
    print(f"  ArkLib dedup audit — {len(decls)} declarations parsed")
    print(f"{'='*72}")

    print(f"\n[1] DUPLICATE FULLY-QUALIFIED NAMES: {len(names['exact'])}")
    for n, ds in sorted(names["exact"].items(), key=lambda kv: -len(kv[1]))[:top]:
        print(f"    {n}  ({len(ds)}x)")
        for d in ds:
            print(f"        {loc(d)}  [{d.kind}]")

    ident = {k: v for k, v in stmts.items() if v["identical_proofs"]}
    diff = {k: v for k, v in stmts.items() if not v["identical_proofs"]}
    print(f"\n[2] SAME STEM + IDENTICAL STATEMENT TYPE: {len(stmts)} "
          f"({len(ident)} also identical proof, {len(diff)} differing proof)")
    for key, info in sorted(stmts.items(), key=lambda kv: -len(kv[1]["decls"]))[:top]:
        stem = key.split("|", 1)[0]
        tag = "IDENTICAL-PROOF" if info["identical_proofs"] else "diff-proof"
        print(f"    {stem}  ({len(info['decls'])}x, {tag})")
        for d in info["decls"]:
            print(f"        {loc(d)}")

    print(f"\n[3] IDENTICAL PROOF BODIES (>=25 chars, normalized): "
          f"{len(proofs)} groups")
    ranked = sorted(proofs.values(), key=lambda ds: -len(ds))
    for ds in ranked[:top]:
        sample = ds[0].body_norm
        if len(sample) > 90:
            sample = sample[:87] + "..."
        print(f"    ({len(ds)}x) {sample}")
        for d in ds:
            print(f"        {loc(d)}  {d.name}")

    print(f"\n[4] RECURRING PROOF LINES (>=8 occurrences): "
          f"{len(lines)} distinct")
    for line, cnt in lines.most_common(top):
        disp = line if len(line) <= 80 else line[:77] + "..."
        print(f"    {cnt:5d}x  {disp}")

    print(f"\n[5] DUPLICATE FILE BASENAMES: {len(files)}")
    for base, paths in sorted(files.items(), key=lambda kv: -len(kv[1]))[:top]:
        print(f"    {base}  ({len(paths)}x)")
        for p in paths:
            print(f"        {p}")

    print(f"\n{'='*72}")
    print("  Summary counts (for tracking over time):")
    print(f"    dup_names_exact        = {len(names['exact'])}")
    print(f"    dup_names_stem         = {len(names['stem'])}")
    print(f"    same_statement_groups  = {len(stmts)}")
    print(f"      of which ident proof = {len(ident)}")
    print(f"    identical_proof_bodies = {len(proofs)}")
    print(f"    recurring_lines        = {len(lines)}")
    print(f"    dup_file_basenames     = {len(files)}")
    print(f"{'='*72}\n")

    return {
        "n_decls": len(decls),
        "dup_names_exact": {
            n: [loc(d) for d in ds] for n, ds in names["exact"].items()
        },
        "dup_names_stem": names["stem"],
        "same_statement": {
            k: {
                "identical_proofs": v["identical_proofs"],
                "locs": [loc(d) for d in v["decls"]],
            }
            for k, v in stmts.items()
        },
        "identical_proof_bodies": [
            {
                "count": len(ds),
                "body": ds[0].body_norm,
                "decls": [{"name": d.name, "loc": loc(d)} for d in ds],
            }
            for ds in ranked
        ],
        "recurring_lines": dict(lines.most_common()),
        "dup_file_basenames": files,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default="ArkLib", help="source root to scan")
    ap.add_argument("--json", help="write full machine-readable report here")
    ap.add_argument("--top", type=int, default=25,
                    help="max rows per section in the console report")
    args = ap.parse_args()

    root = Path(args.root).resolve()
    if not root.exists():
        print(f"root not found: {root}", file=sys.stderr)
        return 1

    decls = gather(root)
    data = report(decls, root, args.top)

    if args.json:
        Path(args.json).write_text(json.dumps(data, indent=2))
        print(f"wrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
