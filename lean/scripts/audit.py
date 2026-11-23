"""Verify imported theorem dependencies and regenerate AUDIT.md."""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAME = r"[\w.']+"
REPORT = re.compile(
    rf"^'({NAME})' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
    re.MULTILINE,
)
MAIN = {
    "Springer." + name for name in (
        "odd_theorem_of_loewner_and_area", "catalan_factorial_real",
        "disk_theorem_of_loewner", "actual_coefficient_flow",
        "even_order_counterexamples", "even_four", "even_family",
        "omitted_disk_improvement_of_loewner",
    )
}


def parse_reports(output, expected):
    reports = {}
    for match in REPORT.finditer(output):
        name, dependencies = match.groups()
        if name in reports:
            raise ValueError(f"Duplicate axiom report for {name}")
        axioms = {item.strip() for item in dependencies.split(",")} if dependencies else set()
        unexpected = axioms - STANDARD
        if unexpected:
            raise ValueError(f"{name} depends on unapproved axioms {sorted(unexpected)}")
        reports[name] = sorted(axioms)
    if expected != reports.keys():
        raise ValueError(f"Axiom reports differ from inventory: missing {sorted(expected - reports.keys())}, "
                         f"unexpected {sorted(reports.keys() - expected)}")
    return reports


def check_lean(path, expected):
    run = subprocess.run(["lake", "env", "lean", "-j1", str(path)], cwd=ROOT, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if run.returncode:
        print(run.stdout, end="")
        run.check_returncode()
    return parse_reports(run.stdout, expected)


def render(reports):
    rows = ["# Springer theorem audit", "",
            f"Lean checked the axiom dependencies of {len(reports)} public theorems. "
            "The imported main-statement file also checks the paper's three main theorem types.", "",
            "## Mathematical premises", "",
            "Theorem 1.4 proves the even-order counterexamples unconditionally. The numerical bound "
            "and first-coefficient equality condition in Theorem 1.2, and the disk bounds of Theorem 1.3, "
            "use normalized disk Loewner existence. The full slit-map equality characterization in "
            "Theorem 1.2 also assumes the classical exterior area-sum estimate for the map.", "",
            "## Kernel axioms", "",
            "Each row lists the kernel axioms of the full Lean declaration, including its hypotheses. "
            "The inventory includes supporting lemmas.", "",
            "| Declaration | Kernel axioms |", "| --- | --- |"]
    for name, axioms in sorted(reports.items()):
        labels = ", ".join(f"`{axiom}`" for axiom in axioms) or "None"
        rows.append(f"| `{name}` | {labels} |")
    return "\n".join(rows) + "\n"


def main():
    names = (ROOT / "scripts/public-theorems.txt").read_text().splitlines()
    expected = set(names)
    if not expected or len(names) != len(expected) or any(
        not re.fullmatch(r"Springer\.[\w.']+", name) for name in names
    ):
        raise ValueError("The theorem inventory is empty or contains duplicate or invalid names")
    check_lean("checks/ReviewMainTypes.lean", MAIN)
    print("Main theorem types checked.", flush=True)
    with tempfile.TemporaryDirectory(dir=ROOT) as tmp:
        query = Path(tmp) / "PublicTheorems.lean"
        query.write_text("import Springer\n" + "".join(f"#print axioms {name}\n" for name in names))
        reports = check_lean(query, expected)
    (ROOT / "AUDIT.md").write_text(render(reports))
    print(f"Verified {len(reports)} public theorems against the permitted kernel axioms.")


if __name__ == "__main__":
    main()
