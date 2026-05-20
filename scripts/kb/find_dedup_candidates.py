#!/usr/bin/env python3
"""Find likely-duplicated declarations across ArkLib subtrees.

Consumes the JSON produced by `extract_declarations.py` and surfaces:

* **same-short-name** groups across multiple files / namespaces, ranked
  by how likely the entries are to be unintentional duplicates;
* **near-duplicate docstrings** between distinct declarations (Jaccard
  similarity over word sets), useful for spotting "same concept,
  different name" cases.

Usage::

    python3 scripts/kb/find_dedup_candidates.py \\
        --in docs/kb/_generated/declarations.json \\
        --out docs/kb/_generated/dedup-report.md

The output is a markdown report grouped by category, with one line
per group + brief context. It is intended for human review (or further
agent triage), not as a hard fail signal.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Short names so common they'd dominate the report without telling us
# anything. (Conservative blacklist; expand on demand.)
TRIVIAL_NAMES = frozenset({
    "mk", "rec", "noConfusion", "casesOn", "recOn", "ext", "intro",
    "elim", "id", "comp", "default", "instance", "cast",
    "add", "sub", "mul", "div", "neg", "one", "zero", "inv",
    "le", "lt", "ge", "gt", "eq", "ne",
    "and", "or", "not", "iff", "imp",
    "succ", "pred", "min", "max",
    "of", "from", "to", "coe", "val",
    "true", "false",
    # Mathlib-bridge metanames that occur all over.
    "isUnit", "isEmpty", "isSubsingleton", "isFinite",
})

DOC_WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9_-]+")


def _doc_words(doc: str) -> set[str]:
    return {w.lower() for w in DOC_WORD_RE.findall(doc) if len(w) >= 4}


def _jaccard(a: set[str], b: set[str]) -> float:
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def collect_groups(data: dict) -> dict[str, list[dict]]:
    """Bucket declarations by short_name."""
    groups: dict[str, list[dict]] = defaultdict(list)
    for fpath, entry in data["files"].items():
        for d in entry["declarations"]:
            short = d.get("short_name") or ""
            if not short or short.startswith("_anon_"):
                continue
            d2 = dict(d)
            d2["file"] = fpath
            groups[short].append(d2)
    return groups


def _interestingness(group: list[dict]) -> int:
    """Heuristic ranking: bigger = more likely worth a look."""
    files = {d["file"] for d in group}
    namespaces = {d["namespace"] for d in group}
    n_files = len(files)
    n_ns = len(namespaces)
    # Cross-file is more interesting than within-file (within-file is
    # usually overloaded notation / typeclass instances of distinct kinds).
    return n_files * 10 + n_ns


def render_short_name_report(groups: dict[str, list[dict]], min_group: int) -> list[str]:
    lines: list[str] = []
    candidates = []
    for short, ds in groups.items():
        if short in TRIVIAL_NAMES or len(short) <= 2:
            continue
        if len(ds) < min_group:
            continue
        # Skip groups where everything is in the same file (likely
        # intentional overloads / typeclass instances).
        if len({d["file"] for d in ds}) <= 1:
            continue
        candidates.append((short, ds))
    candidates.sort(key=lambda kv: (-_interestingness(kv[1]), kv[0]))

    lines.append(f"## Same short-name across multiple files ({len(candidates)} groups)")
    lines.append("")
    lines.append(
        "Each group lists declarations sharing a short name across "
        "≥2 files. Most are legitimate (overloaded interface, paper-"
        "shape vs general form), but the list is the right anchor to "
        "look for duplicates."
    )
    lines.append("")
    for short, ds in candidates:
        lines.append(f"### `{short}` ({len(ds)} declarations, "
                     f"{len({d['file'] for d in ds})} files)")
        lines.append("")
        for d in sorted(ds, key=lambda x: (x["file"], x["line"])):
            ns = d["namespace"] or "(root)"
            doc = d["doc"][:100].replace("|", "\\|")
            lines.append(
                f"- `{d['kind']} {d['name']}` "
                f"[{d['file']}:{d['line']}](../../../{d['file']}#L{d['line']}) "
                f"— {doc or '(no docstring)'}"
            )
        lines.append("")
    return lines


def render_doc_similarity_report(data: dict, threshold: float) -> list[str]:
    """Pairs of declarations with high docstring Jaccard similarity."""
    decls: list[dict] = []
    for fpath, entry in data["files"].items():
        for d in entry["declarations"]:
            short = d.get("short_name") or ""
            if not short or short.startswith("_anon_"):
                continue
            words = _doc_words(d["doc"])
            if len(words) < 5:
                continue
            d2 = dict(d)
            d2["file"] = fpath
            d2["_words"] = words
            decls.append(d2)

    # Bucket by sorted word-prefix to avoid the n^2 explosion across 2.5k decls.
    buckets: dict[str, list[dict]] = defaultdict(list)
    for d in decls:
        # Anchor each decl in 3 buckets keyed by the longest words present.
        anchors = sorted(d["_words"], key=lambda w: (-len(w), w))[:3]
        for a in anchors:
            buckets[a].append(d)

    seen_pairs: set[tuple[str, str]] = set()
    hits: list[tuple[float, dict, dict]] = []
    for bucket in buckets.values():
        if len(bucket) < 2 or len(bucket) > 40:
            # >40 = bucket too broad; >1 needed for any pair.
            continue
        for i, a in enumerate(bucket):
            for b in bucket[i + 1:]:
                if a["name"] == b["name"]:
                    continue
                key = tuple(sorted([a["name"], b["name"]]))
                if key in seen_pairs:
                    continue
                seen_pairs.add(key)
                s = _jaccard(a["_words"], b["_words"])
                if s >= threshold:
                    hits.append((s, a, b))
    hits.sort(key=lambda h: -h[0])

    lines: list[str] = []
    lines.append(f"## Near-duplicate docstrings (Jaccard ≥ {threshold:.2f}, "
                 f"{len(hits)} pairs)")
    lines.append("")
    lines.append(
        "Each pair has docstrings sharing a high fraction of (4+-letter) "
        "words. Most are unrelated coincidences in coding-theory boilerplate; "
        "look for pairs in different files where the *concept* matches."
    )
    lines.append("")
    for s, a, b in hits[:80]:  # cap the report
        if a["file"] == b["file"]:
            continue  # same file = usually overloads
        lines.append(
            f"- **{s:.2f}** `{a['name']}` "
            f"[{a['file']}:{a['line']}](../../../{a['file']}#L{a['line']}) "
            f"vs `{b['name']}` "
            f"[{b['file']}:{b['line']}](../../../{b['file']}#L{b['line']})"
        )
        lines.append(f"    - a: {a['doc'][:100]}")
        lines.append(f"    - b: {b['doc'][:100]}")
    lines.append("")
    return lines


def render_stats(data: dict) -> list[str]:
    lines = ["## Stats", ""]
    for root, s in data["stats"].items():
        lines.append(f"- `{root}` — {s['files']} files, {s['declarations']} declarations")
    lines.append("")
    return lines


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--in", dest="inp", required=True,
                   help="JSON produced by extract_declarations.py")
    p.add_argument("--out", required=True, help="Markdown report path")
    p.add_argument("--min-group", type=int, default=2,
                   help="Minimum group size to report (default 2)")
    p.add_argument("--doc-threshold", type=float, default=0.7,
                   help="Jaccard similarity threshold (default 0.7)")
    args = p.parse_args()

    data = json.loads((REPO_ROOT / args.inp).read_text())
    groups = collect_groups(data)
    lines: list[str] = []
    lines.append("# ArkLib dedup-candidate report")
    lines.append("")
    lines.append(
        "Generated from `docs/kb/_generated/declarations.json`. "
        "**Eyeball, do not auto-rewrite.** The point is to surface "
        "name collisions and doc-string overlap that *might* indicate "
        "an opportunity to consolidate."
    )
    lines.append("")
    lines.extend(render_stats(data))
    lines.extend(render_short_name_report(groups, args.min_group))
    lines.extend(render_doc_similarity_report(data, args.doc_threshold))

    out = REPO_ROOT / args.out
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines))
    print(f"Wrote {out.relative_to(REPO_ROOT)}")


if __name__ == "__main__":
    main()
