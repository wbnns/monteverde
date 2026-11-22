#!/usr/bin/env python3
"""Count theorem and lemma declarations in public Lean complexity libraries.

Reads Audit/size_pins.json, streams each repository's tarball at its pinned commit from
GitHub (nothing is written to disk), counts declaration lines in .lean files, and writes
Audit/size_table.md. The claim may say "the largest Lean complexity library" only if
cslib-frontier is first in this table.

Usage: python3 Audit/size_count.py [--check]
  --check  exit with status 1 if cslib-frontier (Computability) is not first.
"""
import json
import pathlib
import re
import sys
import tarfile
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
DECL = re.compile(
    rb"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public|partial)\s+)*"
    rb"(?:theorem|lemma)\s"
)


def count(repo: str, commit: str, subdir: str) -> tuple[int, int]:
    url = f"https://codeload.github.com/{repo}/tar.gz/{commit}"
    request = urllib.request.Request(url, headers={"User-Agent": "monteverde-size-count"})
    decls = files = 0
    with urllib.request.urlopen(request, timeout=600) as response:
        with tarfile.open(fileobj=response, mode="r|gz") as tar:
            for member in tar:
                if not member.isfile() or not member.name.endswith(".lean"):
                    continue
                # Strip the top-level "<repo>-<commit>/" directory.
                path = member.name.split("/", 1)[1] if "/" in member.name else member.name
                if subdir and not path.startswith(subdir.rstrip("/") + "/"):
                    continue
                data = tar.extractfile(member).read()
                files += 1
                decls += sum(1 for line in data.splitlines() if DECL.match(line))
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
