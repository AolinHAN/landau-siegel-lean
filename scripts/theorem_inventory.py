"""Inventory public theorem names, tracking Lean namespaces and sections.

Private helpers are checked transitively by the kernel dependency audit of
their public callers. This module deliberately supports the source style
used in this project; the actual axiom check is performed by Lean.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent


def without_comments(source):
    result, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result.append("  ")
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i] if not depth or source[i] == "\n" else " ")
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(result)


def theorem_names():
    names = []
    for source in sorted((ROOT / "Siegel").glob("*.lean")):
        text = without_comments(source.read_text())
        if re.search(r"\b(?:sorry|admit|axiom|unsafe|opaque)\b", text):
            raise ValueError(f"Unexpected placeholder or declaration in {source.name}")
        scopes = []
        for line in text.splitlines():
            scope = re.match(r"^(namespace|section)(?:\s+([\w.]+))?\s*$", line)
            if scope:
                scopes.append((scope[1], scope[2] or ""))
                continue
            if re.match(r"^end(?:\s+[\w.]+)?\s*$", line):
                if not scopes:
                    raise ValueError(f"Unmatched scope end in {source.name}")
                scopes.pop()
                continue
            theorem = re.match(r"^(?:@\[[^\]]*\]\s*)?theorem\s+(\w+)", line)
            if theorem:
                prefix = ".".join(name for kind, name in scopes if kind == "namespace")
                names.append(prefix + "." + theorem[1])
        if scopes:
            raise ValueError(f"Unclosed scope in {source.name}")
    if len(set(names)) != len(names):
        raise ValueError("Duplicate theorem name")
    return names


if __name__ == "__main__":
    names = theorem_names()
    header = '''import Siegel

/-! Generated dependency audit of the unconditional main theorem and
every public theorem in the formalization. -/

#check Siegel.UniformExclusion
#check Siegel.PrimeBiasStatement
#check Siegel.LogDerivativeUpperStatement
#check Siegel.QuadraticModelStatement
#check Siegel.Interpolation.interpolation
#check Siegel.uniform_exclusion_of_landau_siegel_zeros
#check Siegel.uniformExclusion
#check Siegel.primeBias
#check Siegel.logDerivativeUpper

'''
    (ROOT / "Audit.lean").write_text(header + "".join(f"#print axioms {name}\n" for name in names))
    print(f"Prepared the dependency audit for {len(names)} public theorems.")
