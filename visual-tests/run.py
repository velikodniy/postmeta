#!/usr/bin/env python3
"""Generate visual test outputs for PostMeta from .mp case files.

Usage:
  python3 visual-tests/run.py
  python3 visual-tests/run.py --bless
  python3 visual-tests/run.py --filter 33
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

SOURCE_URL = "http://www.tlhiv.org/MetaPost/examples/examples.html"
RUN_TIMEOUT_SECONDS = 10


@dataclass
class Case:
    id: str
    title: str
    file: str
    notes: str
    source: str
    example: int | None
    path: Path


def parse_example_number(stem: str) -> int | None:
    match = re.fullmatch(r"example_(\d+)", stem)
    if not match:
        return None
    return int(match.group(1))


def load_cases(cases_dir: Path) -> list[Case]:
    cases: list[Case] = []
    for case_path in cases_dir.glob("*.mp"):
        stem = case_path.stem
        number = parse_example_number(stem)
        title = f"Example {number}" if number is not None else stem
        cases.append(
            Case(
                id=stem,
                title=title,
                file=case_path.name,
                notes="Loaded from cases/",
                source=SOURCE_URL if number is not None else "",
                example=number,
                path=case_path,
            )
        )

    cases.sort(
        key=lambda case: (
            1 if case.example is None else 0,
            case.example if case.example is not None else 0,
            case.id,
        )
    )
    return cases


def run_case(
    repo_root: Path, case_file: Path, current_dir: Path
) -> tuple[int, str, str, bool]:
    cmd = [
        "cargo",
        "run",
        "--release",
        "-p",
        "postmeta-cli",
        "--",
        "--output",
        str(current_dir),
        str(case_file),
    ]
    try:
        proc = subprocess.run(
            cmd,
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=False,
            timeout=RUN_TIMEOUT_SECONDS,
        )
        return proc.returncode, proc.stdout, proc.stderr, False
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="ignore")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="ignore")
        stderr = f"{stderr}\nTimed out after {RUN_TIMEOUT_SECONDS}s".strip()
        return 124, stdout, stderr, True


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate PostMeta visual tests")
    parser.add_argument(
        "--bless", action="store_true", help="Copy current outputs to baseline"
    )
    parser.add_argument(
        "--filter", default="", help="Only run cases matching substring"
    )
    args = parser.parse_args()

    visual_dir = Path(__file__).resolve().parent
    repo_root = visual_dir.parent
    generated_dir = visual_dir / "generated"
    cases_dir = visual_dir / "cases"
    current_dir = generated_dir / "current"
    baseline_dir = generated_dir / "baseline"
    report_path = generated_dir / "report.json"

    cases_dir.mkdir(parents=True, exist_ok=True)
    current_dir.mkdir(parents=True, exist_ok=True)
    baseline_dir.mkdir(parents=True, exist_ok=True)

    cases = load_cases(cases_dir)
    if not cases:
        print(f"No .mp case files found in: {cases_dir}")
        return 1

    if args.filter:
        needle = args.filter.lower()
        cases = [
            case
            for case in cases
            if needle in case.id.lower()
            or needle in case.title.lower()
            or needle in str(case.example)
        ]

    if not cases:
        print("No matching cases.")
        return 0

    summary: list[dict[str, object]] = []
    failures = 0

    total = len(cases)
    for idx, case in enumerate(cases, start=1):
        case_path = case.path

        output_svg = current_dir / f"{case_path.stem}.svg"
        if output_svg.exists():
            output_svg.unlink()

        code, stdout, stderr, timed_out = run_case(repo_root, case_path, current_dir)
        ok = code == 0 and output_svg.is_file() and "Error:" not in stderr
        if not ok:
            failures += 1

        if ok and args.bless:
            shutil.copyfile(output_svg, baseline_dir / output_svg.name)

        baseline_file = baseline_dir / output_svg.name
        baseline_exists = baseline_file.is_file()
        matches_baseline = None
        if ok and baseline_exists:
            matches_baseline = output_svg.read_text(
                encoding="utf-8"
            ) == baseline_file.read_text(encoding="utf-8")

        summary.append(
            {
                "id": case.id,
                "title": case.title,
                "file": case.file,
                "source_mp": f"cases/{case.file}",
                "source_code": case_path.read_text(encoding="utf-8", errors="ignore"),
                "notes": case.notes,
                "source": case.source,
                "example": case.example,
                "ok": ok,
                "exit_code": code,
                "timed_out": timed_out,
                "stdout": stdout.strip(),
                "stderr": stderr.strip(),
                "current_svg": f"generated/current/{output_svg.name}"
                if output_svg.is_file()
                else None,
                "baseline_svg": f"generated/baseline/{output_svg.name}"
                if baseline_exists
                else None,
                "matches_baseline": matches_baseline,
            }
        )
        print(f"[{idx:03d}/{total:03d}] {'OK  ' if ok else 'FAIL'} {case.id}")

    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "blessed": bool(args.bless),
        "source": SOURCE_URL,
        "cases_total": len(cases),
        "failures": failures,
        "cases": summary,
    }
    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")

    print(f"\nReport: {report_path}")
    print(f"Cases: {len(summary)}, failures: {failures}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
