#!/usr/bin/env python3
"""Count theorem and lemma declarations in public Lean complexity libraries.

Reads Audit/size_pins.json, makes a shallow clone of each repository at its pinned commit in a
temporary directory (deleted afterwards), counts declaration lines in all .lean files, and writes
Audit/size_table.md. The claim may say "the largest Lean complexity library" only if
cslib-frontier is first in this table.

Usage: python3 Audit/size_count.py [--check]
  --check  exit with status 1 if cslib-frontier (Computability) is not first.
"""
import json
import pathlib
import re
import sys
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
DECL = re.compile(
    rb"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public|partial)\s+)*"
    rb"(?:theorem|lemma)\s"
)


def count(repo: str, commit: str, subdir: str) -> tuple[int, int]:
    """Count declaration lines in every .lean file of a full clone at the pinned commit.

    A clone has every tracked file. (GitHub's source archives leave out paths marked
    `export-ignore`, so they can undercount.)"""
    with tempfile.TemporaryDirectory() as tmp:
        git = ["git", "-C", tmp, "-c", "advice.detachedHead=false"]
        subprocess.run(["git", "init", "-q", tmp], check=True)
        subprocess.run(git + ["remote", "add", "origin", f"https://github.com/{repo}"], check=True)
        subprocess.run(git + ["fetch", "-q", "--depth", "1", "origin", commit], check=True)
        subprocess.run(git + ["checkout", "-q", "FETCH_HEAD"], check=True)
        root = pathlib.Path(tmp) / subdir if subdir else pathlib.Path(tmp)
        decls = files = 0
        for path in root.rglob("*.lean"):
            if ".git" in path.relative_to(tmp).parts or not path.is_file():
                continue
            files += 1
            decls += sum(1 for line in path.read_bytes().splitlines() if DECL.match(line))
    return decls, files


def main() -> int:
    pins = json.loads((ROOT / "Audit" / "size_pins.json").read_text())
    rows = []
    for lib in pins["libraries"]:
        decls, files = count(lib["repo"], lib["commit"], lib["subdir"])
        rows.append((lib, decls, files))
        print(f"{decls:>8}  {files:>6} files  {lib['name']}", flush=True)
    ranked = sorted((r for r in rows if r[0]["name"] != "cslib-frontier (whole repo)"),
                    key=lambda r: -r[1])
    lines = [
        "# Theorem counts in public Lean complexity libraries",
        "",
        f"Counted on {pins['counted_on']} by `Audit/size_count.py` at the pinned commits in "
        "`Audit/size_pins.json`.",
        f"A declaration is {pins['pattern']}.",
        "",
        "| Rank | Library | Theorems and lemmas | .lean files | Commit |",
        "|------|---------|--------------------:|------------:|--------|",
    ]
    for rank, (lib, decls, files) in enumerate(ranked, 1):
        scope = f" (`{lib['subdir']}`)" if lib["subdir"] else ""
        lines.append(f"| {rank} | [{lib['name']}](https://github.com/{lib['repo']}){scope} | "
                     f"{decls:,} | {files:,} | `{lib['commit'][:7]}` |")
    if pins.get("notes"):
        lines += ["", "Notes:", ""] + [f"- {n}" for n in pins["notes"]]
    whole = next(r for r in rows if r[0]["name"] == "cslib-frontier (whole repo)")
    lines += ["", f"For reference, the whole cslib-frontier repository has {whole[1]:,} "
              f"declarations in {whole[2]:,} files."]
    first = ranked[0][0]["name"] == "cslib-frontier (Computability)"
    lines += ["", "Result: cslib-frontier is " + ("first. The claim can say \"the largest\"."
              if first else "not first. The claim must say \"a major\".")]
    (ROOT / "Audit" / "size_table.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    if "--check" in sys.argv and not first:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
