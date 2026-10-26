#!/usr/bin/env python3
"""Versioned Tisl evidence; Python standard library only.

Every external proof operation is explicit, serial, and logged.  No result is
substituted for a failed compiler, checker, assumptions query, or checksum.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shlex
import shutil
import statistics
import subprocess
import sys
import tarfile
import tempfile
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "e8f801d21cf09f0f4e247a51c9a7726cd6d7dfc5"
CTREE = "1eebf6de298fee6f151b3d62180e5f8e08149cde"
CTREE_URL = "https://github.com/vellvm/ctrees.git"
FORMAT = 1
COLUMNS = ["claim_id", "section", "module", "declaration", "category", "baseline"]
IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
QUALIFIED = re.compile(IDENT + r"(?:\." + IDENT + r")+\Z")
DECL = re.compile(r"^(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*(?:Lemma|Theorem|Corollary|Fact|Remark|Proposition|Example|Definition|Fixpoint|CoFixpoint|Instance|Inductive|CoInductive|Record|Class)\s+(" + IDENT + r")\b")
PRIVATE_DIRS = {".git", ".github", ".claude", ".vscode", ".idea", ".mcp.json", ".cursorrules", ".cursor", ".dir-locals.el", ".merlin", "AGENTS.md", "CLAUDE.md", "__pycache__", ".cache", "node_modules"}
LOCAL_PATH = re.compile(r"(?<![\w:/])/(?:home|Users|root|tmp|var/tmp|mnt/[a-zA-Z]/(?:Users))(?:/[^\s\"'<>\[\]{}()]*)?")
SOURCE_FILES = ["dune-project", "rocq-ticl.opam", "rocq-ticl.opam.template", "_CoqProject", "Makefile", "LICENSE", "INSTALL.md", "docs/main.html", "tools/artifact.py", "artifact/theorem-map.csv", "artifact/baseline.json"]
METHOD = {
    "physical_lines": "Nonblank physical lines. Specification and explicit Proof-to-Qed/Defined lines are counted once in their respective categories; a mixed specification/proof line may count in both. Comment lines count any nonblank comment material, including comment delimiters, and may overlap code. Blank lines count in none.",
    "lexer": "Nested Rocq comments and doubled-quote strings are scanned character by character, preserving positions and newlines. Command terminators are periods followed by whitespace/end, outside comments/strings. Proof and terminator commands are included in proof lines.",
    "incremental": "Baseline records only file hashes and line counts, not old declaration bytes. New Client blocks are exact new-file counts. Selected revision declarations in changed files are reported as their current complete blocks, NOT as a textual diff or a count of newly written lines. Other changed-file declarations are not asserted to have changed.",
    "footprint": "Support-module footprint, not a minimal transitive proof-term closure. Raw rocq wc -e is retained as an independent lexical cross-check and is not equated with these counts or human effort.",
    "limitations": "No human-hours, automation success rate, AI effectiveness, runtime performance, or cold-machine benchmark is inferred. Filesystem caches are not flushed. Manual client work includes finite helper normalization, representation/initialization reasoning and two-slot runner congruence; existing SharedInv, rank and recurrence certificates are reused.",
}


class EvidenceError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise EvidenceError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        h = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
        return h.hexdigest()


def put_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def clean(text: str, roots: tuple[Path, ...] = ()) -> str:
    for root in sorted((str(p.resolve()) for p in roots), key=len, reverse=True):
        text = text.replace(root, "<workspace>")
    home = str(Path.home())
    if home != "/":
        text = text.replace(home, "<home>")
    return LOCAL_PATH.sub("<local-path>", text)


class Runner:
    def __init__(self, root: Path, switch: str, results: Path):
        self.root, self.switch, self.results = root, switch, results
        results.mkdir(parents=True, exist_ok=True)
        self.records: list[dict[str, Any]] = []

    def opam(self, *args: str) -> list[str]:
        return ["opam", "exec", "--switch", self.switch, "--", *map(str, args)]

    def run(self, command: list[str], log: str, *, cwd: Path | None = None,
            stdin: str | None = None, prover: bool = False) -> subprocess.CompletedProcess[str]:
        cwd = cwd or self.root
        started = time.perf_counter()
        try:
            result = subprocess.run(command, cwd=cwd, input=stdin, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    encoding="utf-8", errors="replace")
        except OSError as exc:
            elapsed = time.perf_counter() - started
            record = {"command": command, "cwd": str(cwd), "exit_status": None,
                      "wall_seconds": elapsed, "error": str(exc)}
            self.records.append(record)
            (self.results / log).write_text(clean(json.dumps(record) + "\n", (self.root,)), encoding="utf-8")
            raise EvidenceError(f"Cannot execute {command[0]}: {exc}") from exc
        elapsed = time.perf_counter() - started
        record = {"command": command, "cwd": str(cwd), "exit_status": result.returncode,
                  "wall_seconds": elapsed, "log": log}
        self.records.append(record)
        transcript = ("COMMAND: " + shlex.join(command) + "\nCWD: " + str(cwd) +
                      f"\nEXIT STATUS: {result.returncode}\nWALL SECONDS: {elapsed:.9f}\n"
                      "--- STDOUT ---\n" + result.stdout + "\n--- STDERR ---\n" + result.stderr)
        (self.results / log).write_text(clean(transcript, (self.root, cwd)), encoding="utf-8")
        require(result.returncode == 0, f"Subprocess failed ({result.returncode}); see {self.results / log}")
        if prover:
            require(not re.search(r"\bError\s*:", result.stdout + result.stderr),
                    f"Prover returned Error: despite process status; see {self.results / log}")
        return result

    def records_json(self, name: str) -> None:
        put_json(self.results / name, json.loads(clean(json.dumps(self.records), (self.root,))))


def safe_relative(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    require(value and not path.is_absolute() and "\\" not in value and
            all(p not in {"", ".", ".."} for p in value.split("/")), f"Unsafe relative path: {value!r}")
    return path


def load_inputs(root: Path, map_path: Path | None) -> tuple[list[dict[str, str]], dict[str, Any]]:
    path = map_path or root / "artifact/theorem-map.csv"
    require(path.is_file(), f"Missing theorem map: {path}")
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        require(reader.fieldnames == COLUMNS, f"Unsupported theorem-map columns: {reader.fieldnames}")
        rows = list(reader)
    require(bool(rows), "Empty theorem map")
    seen: set[str] = set()
    for row in rows:
        require(None not in row and all(isinstance(v, str) and v.strip() == v and v for v in row.values()), "Malformed/blank theorem-map field")
        name, module = row["declaration"], row["module"]
        require(bool(QUALIFIED.fullmatch(name)) and bool(QUALIFIED.fullmatch(module)), f"Invalid qualified declaration/module: {row}")
        require(row["claim_id"] == name and name.startswith(module + "."), f"Unsupported declaration mapping: {row}")
        require(name not in seen, f"Duplicate declaration: {name}")
        seen.add(name)
        require(row["category"] in {"inherited", "ported", "extended", "new"}, f"Unknown category: {row}")
        require(row["baseline"] in {BASELINE, "not-applicable"}, f"Unsupported baseline: {row}")
        require(re.fullmatch(r"s:[A-Za-z0-9:_.-]+", row["section"]) is not None, f"Invalid manuscript section label: {row}")
        prefix, _, rest = module.partition(".")
        require(prefix in {"TICL", "examples"}, f"Unsupported logical source root: {module}")
        source = root / ("theories" if prefix == "TICL" else "examples") / (rest.replace(".", "/") + ".v")
        require(source.is_file(), f"Missing source module: {source}")
        code, _, _ = lex(source.read_text(encoding="utf-8"))
        # Qualified nested modules are accepted only if the declaration really appears.
        require(re.search(r"\b" + re.escape(name.rsplit(".", 1)[1]) + r"\b", code) is not None,
                f"Missing declaration in source: {name}")
    baseline_path = root / "artifact/baseline.json"
    require(baseline_path.is_file(), f"Missing baseline capture: {baseline_path}")
    baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
    require(baseline.get("format") == 1 and baseline.get("scope") == ["theories/**/*.v", "examples/**/*.v"] and isinstance(baseline.get("files"), dict) and bool(baseline["files"]), "Unsupported baseline format")
    for name, item in baseline["files"].items():
        safe_relative(name)
        require(name.endswith(".v") and name.split("/")[0] in {"theories", "examples"}, f"Invalid baseline source: {name}")
        require(isinstance(item, dict) and re.fullmatch(r"[0-9a-f]{64}", item.get("sha256", "")) is not None and isinstance(item.get("lines"), int) and item["lines"] >= 0, f"Invalid baseline entry: {name}")
        require((root / name).is_file(), f"Baseline source disappeared: {name}")
    return rows, baseline


def lex(text: str) -> tuple[str, str, list[bool]]:
    """Return comment-free source, comment/string-free source, comment positions."""
    code, commands, comments = list(text), list(text), [False] * len(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            n = 2 if text.startswith("(*", i) or text.startswith("*)", i) else 1
            if text.startswith("(*", i):
                depth += 1
            elif text.startswith("*)", i):
                depth -= 1
            for j in range(i, min(i + n, len(text))):
                comments[j] = True
                if text[j] != "\n":
                    code[j] = commands[j] = " "
            i += n
        elif quoted:
            if text.startswith('""', i):
                commands[i:i + 2] = [" ", " "]
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                if text[i] != "\n":
                    commands[i] = " "
                i += 1
        elif text.startswith("(*", i):
            depth = 1
            for j in (i, i + 1):
                comments[j] = True
                code[j] = commands[j] = " "
            i += 2
        elif text[i] == '"':
            commands[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    require(depth == 0 and not quoted, "Unterminated Rocq comment or string")
    return "".join(code), "".join(commands), comments


def commands(masked: str) -> list[tuple[int, int, str]]:
    result, start = [], 0
    for match in re.finditer(r"\.(?=\s|$)", masked):
        end = match.end()
        part = masked[start:end]
        leading = len(part) - len(part.lstrip())
        if part.strip():
            result.append((start + leading, end, part.strip()))
        start = end
    require(not masked[start:].strip(), "Source ends with an unterminated Rocq command")
    return result


def line_number(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def count_source(text: str, first: int = 0, last: int | None = None) -> dict[str, int]:
    last = len(text) if last is None else last
    code, masked, comment = lex(text)
    proof = [False] * len(text)
    in_proof = False
    for start, end, statement in commands(masked):
        begins = re.match(r"Proof\b", statement) is not None
        ends = re.match(r"(?:Qed|Defined|Admitted|Abort)\b", statement) is not None
        if in_proof or begins:
            proof[start:end] = [True] * (end - start)
        if begins:
            in_proof = True
        if ends:
            in_proof = False
    require(not in_proof, "Unterminated explicit proof")
    totals = {"nonblank": 0, "specification": 0, "proof": 0, "comment": 0}
    offset = 0
    for line in text.splitlines(keepends=True):
        lo, hi = max(first, offset), min(last, offset + len(line))
        offset += len(line)
        if hi <= lo:
            continue
        if text[lo:hi].strip():
            totals["nonblank"] += 1
        if any(not code[j].isspace() and not proof[j] for j in range(lo, hi)):
            totals["specification"] += 1
        if any(not code[j].isspace() and proof[j] for j in range(lo, hi)):
            totals["proof"] += 1
        if any(comment[j] and not text[j].isspace() for j in range(lo, hi)):
            totals["comment"] += 1
    return totals


def inventory(root: Path, baseline: dict[str, Any], results: Path) -> dict[str, Any]:
    sources = sorted([*root.glob("theories/**/*.v"), *root.glob("examples/**/*.v")])
    require(bool(sources), "No Rocq sources found")
    forbidden, parameters, scoped_declarations, file_rows, blocks = [], [], [], [], []
    patterns = [
        ("admitted", r"\bAdmitted\b"), ("proof-admit", r"\badmit\b"),
        ("axiom", r"\bAxioms?\b"), ("aborted-proof", r"\bAbort\b"),
        ("disabled-check", r"\bUnset\s+(?:Guard|Universe|Positivity)\s+Checking\b"),
        ("bypassed-check", r"\bSet\s+Bypass\s+Check\b"),
        ("unchecked-cast", r"\b(?:vm_cast_no_check|native_cast_no_check|exact_no_check|bypass_check)\b"),
    ]
    selected = {"write_ret", "write_ax_framed", "captured_before_yield_rr", "delayed_branch_permutation", "refine_rr_branch01_zero", "refine_rr_branch10_zero", "refine_rr_not_sbisim_congruent"}
    for source in sources:
        rel = source.relative_to(root).as_posix()
        data = source.read_bytes()
        text = data.decode("utf-8")
        _, masked, _ = lex(text)
        prior = baseline["files"].get(rel)
        status = "new" if prior is None else ("unchanged" if prior["sha256"] == digest(data) else "changed")
        counts = count_source(text)
        support = (rel.startswith("examples/CSL/Queue/") or rel.startswith("theories/CTree/Interp/Yield/") or rel in {"theories/CTree/Interp/CSL/Frame.v", "theories/Lang/CSL/Frame.v"})
        file_rows.append({"file": rel, "sha256": digest(data), "lines": len(text.splitlines()), "baseline_status": status, "worked_client_support": support, **counts})
        for kind, pattern in patterns:
            for match in re.finditer(pattern, masked):
                forbidden.append({"file": rel, "line": line_number(text, match.start()), "kind": kind, "token": match.group()})
        statements = commands(masked)
        scope: list[tuple[str, str]] = []
        module = ("TICL." if rel.startswith("theories/") else "examples.") + rel.split("/", 1)[1][:-2].replace("/", ".")
        for index, (start, end, statement) in enumerate(statements):
            opening = re.match(r"(Module(?:\s+Type)?|Section)\s+(" + IDENT + r")", statement)
            if opening and ":=" not in statement:
                scope.append((opening.group(1), opening.group(2)))
            ending = re.match(r"End\s+(" + IDENT + r")", statement)
            if ending:
                require(bool(scope) and scope[-1][1] == ending.group(1), f"Unbalanced module/section in {rel}")
                scope.pop()
            contextual = re.match(r"(?:(?:Local|Global)\s+)?(Parameters?|Variables?|Hypothes(?:is|es)|Context)\b", statement)
            if contextual:
                entry = {"file": rel, "module": module + "".join("." + name for kind, name in scope if kind.startswith("Module")), "line": line_number(text, start), "kind": contextual.group(1), "scope": [{"kind": kind, "name": name} for kind, name in scope], "scope_class": "section-local" if any(kind == "Section" for kind, _ in scope) else ("module-interface" if any(kind.startswith("Module") for kind, _ in scope) else "file-global"), "declaration": statement}
                scoped_declarations.append(entry)
                if contextual.group(1).startswith("Parameter"):
                    parameters.append(entry)
            declared = DECL.match(statement)
            if not declared:
                continue
            name = declared.group(1)
            block_end = end
            if index + 1 < len(statements) and re.match(r"Proof\b", statements[index + 1][2]):
                for _, candidate_end, candidate in statements[index + 1:]:
                    if re.match(r"(?:Qed|Defined|Admitted|Abort)\b", candidate):
                        block_end = candidate_end
                        break
                else:
                    raise EvidenceError(f"Missing proof terminator: {rel}:{name}")
            if (rel == "examples/CSL/Queue/Client.v" and status == "new") or (status == "changed" and name in selected):
                blocks.append({"file": rel, "declaration": module + "".join("." + n for k, n in scope if k.startswith("Module")) + "." + name, "start_line": line_number(text, start), "end_line": line_number(text, block_end - 1), "scope": "new-client-block" if status == "new" else "selected-revision-block-in-changed-file", **count_source(text, start, block_end)})
    report = {"format": FORMAT, "methodology": METHOD, "files": file_rows, "forbidden": forbidden, "interface_parameters": parameters, "scoped_context_declarations": scoped_declarations, "context_inventory_note": "Parameter, Variable, Hypothesis and Context commands are inventoried with lexical section/module scope; section-local binders may generalize into theorem hypotheses. This lexical inventory is not the global-assumption inventory: each theorem's fresh Print Assumptions output is authoritative.", "incremental_declaration_blocks": blocks, "unchanged_files": [f["file"] for f in file_rows if f["baseline_status"] == "unchanged"]}
    put_json(results / "source-inventory.json", report)
    fields = ["file", "baseline_status", "worked_client_support", "lines", "nonblank", "specification", "proof", "comment", "sha256"]
    with (results / "sizes.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows({key: row[key] for key in fields} for row in file_rows)
    with (results / "incremental-sizes.csv").open("w", newline="", encoding="utf-8") as stream:
        fields2 = ["file", "declaration", "start_line", "end_line", "scope", "nonblank", "specification", "proof", "comment"]
        writer = csv.DictWriter(stream, fieldnames=fields2)
        writer.writeheader()
        writer.writerows(blocks)
    sums = lambda rows: {key: sum(row[key] for row in rows) for key in ("nonblank", "specification", "proof", "comment")}
    summary = {"format": FORMAT, "methodology": METHOD, "all_modules": sums(file_rows), "worked_client_support_modules": sums([r for r in file_rows if r["worked_client_support"]]), "new_client_file": sums([r for r in file_rows if r["file"] == "examples/CSL/Queue/Client.v"]), "incremental_declaration_blocks": sums(blocks), "unchanged_files": report["unchanged_files"], "reused_named_lemmas": []}
    client = root / "examples/CSL/Queue/Client.v"
    if client.is_file():
        _, body, _ = lex(client.read_text(encoding="utf-8"))
        reused = ["iter_equ", "interp_schedule_rr_guard_equ", "guard_equ_equ", "run_rr_two_forks", "qheap_queue_nodes_rep", "new_queue_heap_disjoint", "new_queue_heap_agrees", "interp_rr_new_queue", "interp_rr_new_queue_first", "run_rr_framable", "ticll_csl_frame", "shared_rotate_agaf_pop_rr_fresh", "exact_worker_turn", "qstepN_agree", "frame_preserved"]
        summary["reused_named_lemmas"] = [name for name in reused if re.search(r"\b" + re.escape(name) + r"\b", body)]
    shared = root / "examples/CSL/Queue/Shared.v"
    if shared.is_file():
        _, shared_body, _ = lex(shared.read_text(encoding="utf-8"))
        shared_status = next(row["baseline_status"] for row in file_rows if row["file"] == "examples/CSL/Queue/Shared.v")
        summary["reused_support_declarations"] = [{"declaration": "examples.CSL.Queue.Shared." + name, "file": "examples/CSL/Queue/Shared.v", "file_sha256": sha(shared), "baseline_status": shared_status} for name in ("SharedInv", "shared_worker_turn", "shared_ranked", "shared_pool_agaf_rr") if re.search(r"\b" + name + r"\b", shared_body)]
    put_json(results / "sizes-summary.json", summary)
    require(not forbidden, f"Forbidden source commands found; see {results / 'source-inventory.json'}")
    return report


def mappings(build: str = "_build") -> list[str]:
    return ["-Q", f"{build}/default/theories", "TICL", "-Q", f"{build}/default/examples", "examples"]


def parse_assumptions(stdout: str, declaration: str) -> dict[str, Any]:
    sentinel = list(re.finditer(r"(?m)^unit\s*:\s*Set\s*$", stdout))
    require(len(sentinel) == 1 and not stdout[sentinel[0].end():].strip(),
            f"Missing final query-completion Check (truncated response): {declaration}")
    stdout = stdout[:sentinel[0].start()]
    closed = list(re.finditer(r"Closed under the global context\s*\.?", stdout))
    axioms = list(re.finditer(r"(?m)^\s*Axioms:\s*$", stdout))
    require(len(closed) + len(axioms) == 1, f"Missing, duplicated, or truncated assumptions block: {declaration}")
    boundary = closed[0].start() if closed else axioms[0].start()
    checked = stdout[:boundary]
    short = declaration.rsplit(".", 1)[1]
    require(re.search(r"\b" + re.escape(short) + r"(?:@\{[^}]*\})?\s*:", checked) is not None,
            f"Missing successful Check output: {declaration}")
    if closed:
        require(not stdout[closed[0].end():].strip(), f"Unexpected trailing assumptions output: {declaration}")
        return {"declaration": declaration, "closed": True, "assumptions": []}
    body = stdout[axioms[0].end():].strip()
    require(bool(body), f"Empty Axioms block: {declaration}")
    # Assumption names are unindented; types may continue on arbitrarily many lines.
    starts = list(re.finditer(r"(?m)^(" + IDENT + r"(?:\." + IDENT + r")*)(?:@\{[^}\n]*\})?\s*(?=[:\n])", body))
    require(bool(starts) and starts[0].start() == 0, f"Unparseable assumptions: {declaration}")
    assumptions = []
    for i, match in enumerate(starts):
        end = starts[i + 1].start() if i + 1 < len(starts) else len(body)
        entry = body[match.end():end].strip()
        require(entry.startswith(":"), f"Truncated assumption type: {declaration}: {match.group(1)}")
        type_text = entry[1:].strip()
        require(bool(type_text) and not type_text.endswith(("->", ":", ",")), f"Truncated assumption type: {declaration}")
        assumptions.append({"name": match.group(1), "type": " ".join(type_text.split())})
    require(len({a["name"] for a in assumptions}) == len(assumptions), f"Duplicate assumption names: {declaration}")
    return {"declaration": declaration, "closed": False, "assumptions": sorted(assumptions, key=lambda a: a["name"])}


def toolchain(runner: Runner, filename: str = "toolchain.json") -> dict[str, Any]:
    versions = {}
    for name, args in [("ocaml", ["ocamlc", "-version"]), ("dune", ["dune", "--version"]), ("rocq", ["rocq", "--version"]), ("rocqchk", ["rocqchk", "--version"]), ("opam", ["opam", "--version"])]:
        response = runner.run(runner.opam(*args), f"version-{name}.log")
        versions[name] = (response.stdout + response.stderr).strip()
    installed = runner.run(["opam", "list", "--switch", runner.switch, "--installed", "--columns=name,version", "--color=never"], "installed-packages.log")
    cpu = platform.processor()
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.is_file():
        match = re.search(r"(?m)^model name\s*:\s*(.+)", cpuinfo.read_text())
        if match:
            cpu = match.group(1)
    ram = None
    meminfo = Path("/proc/meminfo")
    if meminfo.is_file():
        match = re.search(r"(?m)^MemTotal:\s*(\d+)\s+kB", meminfo.read_text())
        if match:
            ram = int(match.group(1)) * 1024
    info = {"format": FORMAT, "switch": runner.switch, "versions": versions, "installed_packages": installed.stdout, "system": {"os": platform.platform(), "architecture": platform.machine(), "cpu": cpu, "logical_cpus": os.cpu_count(), "ram_bytes": ram}, "filesystem_cache_caveat": METHOD["limitations"]}
    put_json(runner.results / filename, json.loads(clean(json.dumps(info), (runner.root,))))
    return info


def audit(args: argparse.Namespace) -> None:
    rows, baseline = load_inputs(ROOT, args.theorem_map)
    results = ROOT / "artifact/results"
    runner = Runner(ROOT, args.switch, results)
    for name in ("audit.json", "assumptions.json"):
        (results / name).unlink(missing_ok=True)
    try:
        inv = inventory(ROOT, baseline, results)
        runner.run(runner.opam("dune", "build", "-j", "1", "examples/CSL/Evidence.vo"), "audit-build.log", prover=True)
        runner.run(runner.opam("rocqchk", "-o", *mappings(), "examples.CSL.Evidence"), "kernel-check.log", prover=True)
        checked = []
        combined = []
        for index, row in enumerate(rows, 1):
            name = row["declaration"]
            query = (f"Set Printing Width 1000000.\nRequire Import {row['module']}.\nCheck {name}.\nPrint Assumptions {name}.\nCheck Corelib.Init.Datatypes.unit.\nQuit.\n")
            log = f"assumption-query-{index:03d}.log"
            response = runner.run(runner.opam("rocq", "repl", "-quiet", *mappings()), log, stdin=query, prover=True)
            # These markers are emitted by Python, never submitted as Rocq commands.
            combined.append(f"BEGIN DECLARATION {name}\nCOMMANDS:\n{query}STDOUT:\n{response.stdout}\nSTDERR:\n{response.stderr}\nEND DECLARATION {name}\n")
            (results / "assumptions.log").write_text(clean("\n".join(combined), (ROOT,)), encoding="utf-8")
            checked.append({**row, **parse_assumptions(response.stdout, name)})
        assumptions = {"format": FORMAT, "switch": args.switch, "theorem_map_sha256": sha(args.theorem_map or ROOT / "artifact/theorem-map.csv"), "declarations": checked, "assumption_names": sorted({a["name"] for row in checked for a in row["assumptions"]})}
        put_json(results / "assumptions.json", assumptions)
        runner.run(runner.opam("rocq", "wc", "-e", *[r["file"] for r in inv["files"]]), "rocq-wc.log")
        toolchain(runner)
        put_json(results / "audit.json", {"format": FORMAT, "success": True, "declaration_count": len(checked), "declarations": [r["declaration"] for r in checked], "theorem_map_sha256": assumptions["theorem_map_sha256"], "assumption_names": assumptions["assumption_names"], "full_vo_build": True, "recursive_kernel_check": True, "source_inventory": "source-inventory.json", "sizes": "sizes.csv"})
    finally:
        runner.records_json("audit-commands.json")


def measure(args: argparse.Namespace) -> None:
    rows, baseline = load_inputs(ROOT, args.theorem_map)
    results = ROOT / "artifact/results"
    runner = Runner(ROOT, args.switch, results)
    (results / "measurements.json").unlink(missing_ok=True)
    try:
        inventory(ROOT, baseline, results)
        info = toolchain(runner)
        timings, builds = [], []
        suffix = 1
        for run in range(1, 4):
            while (ROOT / f"_build-evidence-{suffix}").exists():
                suffix += 1
            directory = f"_build-evidence-{suffix}"
            # Reserve the unused name without deleting or reusing any existing build.
            (ROOT / directory).mkdir(exist_ok=False)
            require(not any((ROOT / directory).iterdir()), f"Build directory already populated: {directory}")
            command = runner.opam("dune", "build", "--cache=disabled", "-j", "1", "--build-dir", directory, "--display", "verbose")
            runner.run(command, f"build-{run}.log", prover=True)
            record = runner.records[-1]
            timings.append(record["wall_seconds"])
            builds.append({"directory": directory, "command": command, "exit_status": record["exit_status"], "wall_seconds": record["wall_seconds"], "log": record["log"]})
            suffix += 1
        runner.run(runner.opam("rocqchk", "-o", *mappings(builds[-1]["directory"]), "examples.CSL.Evidence"), "measured-kernel-check.log", prover=True)
        recheck = runner.records[-1]
        runner.run(runner.opam("rocq", "wc", "-e", *[str(p.relative_to(ROOT)) for p in sorted([*ROOT.glob("theories/**/*.v"), *ROOT.glob("examples/**/*.v")])]), "rocq-wc.log")
        runner.run(["opam", "switch", "export", "--switch", args.switch, str(results / "environment.export"), "--freeze"], "environment-export.log")
        put_json(results / "measurements.json", {"format": FORMAT, "success": True, "switch": args.switch, "runs": builds, "compile_seconds": {"median": statistics.median(timings), "min": min(timings), "max": max(timings)}, "recursive_kernel_check": {"wall_seconds": recheck["wall_seconds"], "command": recheck["command"], "exit_status": recheck["exit_status"], "log": recheck["log"]}, "toolchain": info, "cache_disabled": True, "parallel_jobs": 1, "interpretation": "Full compilation includes elaboration and tactics; recursive checking is timed separately. Filesystem caches are not flushed. Neither is a runtime benchmark."})
    finally:
        runner.records_json("measure-commands.json")


def selected_sources(root: Path) -> list[Path]:
    paths = [root / rel for rel in SOURCE_FILES]
    for directory in ("theories", "examples"):
        for path in (root / directory).rglob("*"):
            if path.is_file() and (path.suffix == ".v" or path.name in {"dune", "dune.inc", "README", "README.md", "README.rst", "readme.md"}):
                require(not path.is_symlink(), f"Source symlink not supported: {path}")
                paths.append(path)
    for path in paths:
        require(path.is_file() and not path.is_symlink(), f"Missing/nonregular allowlisted source: {path}")
        require(not any(p in PRIVATE_DIRS or p.startswith("_build") for p in path.relative_to(root).parts), f"Private path in source allowlist: {path}")
    return sorted(set(paths))


def sanitize_dune(text: str) -> str:
    """Remove only project-identity fields, preserving every other byte."""
    spans, stack, quoted, comment, i = [], [], False, False, 0
    while i < len(text):
        char = text[i]
        if comment:
            if char == "\n":
                comment = False
        elif quoted:
            if char == "\\":
                i += 1
            elif char == '"':
                quoted = False
        elif char == ";":
            comment = True
        elif char == '"':
            quoted = True
        elif char == "(":
            stack.append(i)
        elif char == ")":
            require(bool(stack), "Malformed canonical Dune metadata")
            start = stack.pop()
            match = re.match(r"\(\s*([^\s()]+)", text[start:i + 1])
            if match and match.group(1) in {"authors", "maintainers", "source", "bug_reports"}:
                spans.append((start, i + 1))
        i += 1
    require(not stack and not quoted, "Malformed canonical Dune metadata")
    for start, end in sorted(spans, reverse=True):
        text = text[:start] + text[end:]
    return text


def sanitize_docs(text: str) -> str:
    # Navigation into generated modules is retained. Author project/social links
    # are removed only from href attributes, never from license/copyright text.
    def replace(match: re.Match[str]) -> str:
        url = match.group(2)
        project = re.search(r"(?:github\.com/vellvm/ticl|eioannidis|ioannidis|zakowski|paul[-_]?he)", url, re.I)
        return 'href="#"' if project else match.group(0)
    return clean(re.sub(r"href\s*=\s*([\"'])(.*?)\1", replace, text, flags=re.I))


def snapshot_dependency(destination: Path, runner: Runner, scratch: Path) -> None:
    checkout = scratch / "ctrees-checkout"
    runner.run(["git", "init", str(checkout)], "ctree-init.log")
    runner.run(["git", "-C", str(checkout), "remote", "add", "origin", CTREE_URL], "ctree-remote.log")
    runner.run(["git", "-C", str(checkout), "fetch", "--depth", "1", "origin", CTREE], "ctree-fetch.log")
    runner.run(["git", "-C", str(checkout), "checkout", "--detach", CTREE], "ctree-checkout.log")
    actual = runner.run(["git", "-C", str(checkout), "rev-parse", "HEAD"], "ctree-revision.log").stdout.strip()
    require(actual == CTREE, "Fetched CTree revision differs from pinned commit")
    files = runner.run(["git", "-C", str(checkout), "ls-files", "-z"], "ctree-files.log").stdout.split("\0")
    destination.mkdir(parents=True, exist_ok=False)
    licenses = []
    for value in files:
        if not value:
            continue
        rel = safe_relative(value)
        if any(p in PRIVATE_DIRS or p.startswith("_build") for p in rel.parts):
            continue
        source, target = checkout / value, destination / value
        require(source.is_file(), f"Unsupported dependency member: {value}")
        require(source.resolve().is_relative_to(checkout.resolve()), f"Escaping dependency link: {value}")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        if re.search(r"(?:license|copying|copyright)", source.name, re.I):
            licenses.append(value)
    require(bool(licenses), "Pinned CTree source contains no license/attribution file")


def artifact_readme() -> str:
    return f"""# Tisl-A1 formal evidence

This bundle snapshots the actual revised source bytes, not only a committed
revision. Its identity is Tisl-A1 plus SHA-256 of MANIFEST.sha256. The sorted
manifest covers every regular distributed file except itself. CTree source and
licenses are bundled at {CTREE}. The historical comparison is the initial 2025
artifact release {BASELINE}; this is not asserted to be the final OOPSLA artifact.

## Import and build

From this directory, with opam initialized and the Rocq released repository
available, choose an unused switch name and do not change the default switch:

```sh
SW=tisl-A1-local
opam switch create "$SW" --empty --no-switch -y
opam repository add rocq-released https://rocq-prover.org/opam/released --switch "$SW" -y
opam switch import --switch "$SW" environment.export -y
opam pin add --switch "$SW" -y rocq-ctree.2.0-dev ./dependencies/ctrees
cd source
opam exec --switch "$SW" -- dune build -j 1
python3 tools/artifact.py audit --switch "$SW"
opam exec --switch "$SW" -- make doc
```

The frozen export specifies the complete successful closure, including compiler,
compatibility packages, odoc 3.2.1 for documentation, and the exact CTree pin. Dependency downloads require
network access; this is not an offline image. Alternatively create a dedicated
OCaml 5.3.0 switch using --no-switch and install the exact versions recorded in
environment.export before pinning the bundled dependency. INSTALL.md gives the
explicit source-build recipe. Each opam operation must specify --switch.

To independently check the distributed archive (from an extracted source tree):

```sh
python3 tools/artifact.py verify-package --switch "$SW" --archive /path/to/tisl-A1.tar.gz
```

Verification checks every manifest entry before creating a new unused
check switch, imports the frozen closure, pins bundled CTree, builds all extracted
source, audits fresh assumptions and recursively rechecks Evidence. It compares
successful declarations and per-theorem assumptions, not timings.

## Results and interpretation

results/ retains raw compiler/checker/query logs and parsed JSON. Assumptions are
queried with Check and Print Assumptions in fresh noninteractive Rocq processes;
Python, not an unsupported prover command, supplies the BEGIN/END markers.
source-inventory.json separates interface Parameters from forbidden commands.
The recursive rocqchk check uses -o, with neither -admit nor -norec nor quick
compilation. smoke.log contains the separately observed concrete evaluations.

The 53 mapped roots use only Stdlib UIP (eq_rect_eq), dependent functional
extensionality, or no global assumptions; assumptions.json records each root.
The broader loaded dependency context additionally lists proof irrelevance,
Ensembles extensionality and the two ClassicalDedekindReals decision axioms.
dependency-context.json traces their imports through Program, ITree Basics and
RelationAlgebra's Psatz dependency. None of those additional constants occurs
in the mapped roots' Print Assumptions results. The full checker reports no
type-in-type, unsafe (co)fixpoints or assumed positivity.

sizes.csv counts physical nonblank specification, explicit Proof--Qed/Defined
proof and comment lines. Nested comments and strings are lexed, not regex-stripped.
A mixed line may count in multiple categories; no category counts a line twice.
Proof delimiters count as proof. Raw rocq wc -e is a separate lexical cross-check,
not the definition of these counts. sizes-summary.json states the exact module
footprint, including frame and scheduler support, not a minimal proof-term closure.
incremental-sizes.csv reports new Client blocks and selected current revision
blocks in changed files. Baseline hashes do not reconstruct historical declaration
bytes: these are not invented added-line counts. Unchanged file hashes record
reuse of representation/rank/certificate modules. Reused named lemmas and manual
finite normalization, representation and slotwise congruence are identified; no
automation success rate, human-hours or AI-effectiveness claim follows.

measurements.json reports three serial cache-disabled full compilation runs,
median and range, and separately timed recursive checking. Compilation includes
elaboration and tactics. Filesystem caches were not flushed; these are not
cold-machine or runtime benchmarks. Tool versions, hardware description, exact
commands, statuses and the frozen closure accompany the timings.

## Allocator design and implementation provenance

The design reference is Leijen, Zorn and de Moura, *Mimalloc: Free List Sharding
in Action*, Microsoft Research technical report MSR-TR-2019-18 (June 2019).
The inspected implementation is mimalloc v2.5.2, commit
2406cc5f3ab6d6e54fe560cdd66fa46eee775312 (September 12, 2026; accessed
October 25, 2026), not a moving branch. Correspondences are model boundaries,
not a C or weak-memory refinement:

* remote_attempt corresponds to the ordinary branch of mi_free_block_delayed_mt:
  https://github.com/microsoft/mimalloc/blob/2406cc5f3ab6d6e54fe560cdd66fa46eee775312/src/free.c#L250-L268
  links using mi_block_set_next and weak release CAS. The model uses strong
  deterministic CAS and omits production memory orders and delayed-free flags.
* detach_attempt corresponds to _mi_page_thread_free_collect:
  https://github.com/microsoft/mimalloc/blob/2406cc5f3ab6d6e54fe560cdd66fa46eee775312/src/page.c#L204-L212
  The production CAS preserves packed flags with mi_tf_set_block; the model
  uses an unpacked pointer.
* reclaim_step corresponds to the traversal/splice:
  https://github.com/microsoft/mimalloc/blob/2406cc5f3ab6d6e54fe560cdd66fa46eee775312/src/page.c#L217-L243
  Production splices the detached list into page->local_free; the model moves
  blocks individually with per-block logs. No order-preserving refinement is
  claimed.
* offer_block, new_page, mailboxes and the two clients are model-specific
  workload/layout. They are not exact mi_malloc, page-acquisition,
  abandoned-page or physical-free correspondences.

## Attribution and anonymity

Only nonlegal project-identity metadata in the packaged canonical Dune metadata,
regenerated opam file, author documentation links and local path provenance in
documentation and logs is sanitized. The development repository is unchanged.
All copyright/license notices
and required third-party attributions remain. These notices and public source
fingerprints limit anonymity; this artifact does not claim perfect blinding.
"""


def result_files(results: Path) -> list[Path]:
    # Package/verification reports cannot be embedded into the archive whose
    # digest they describe. Nor can an earlier archive or private provenance.
    return sorted(p for p in results.rglob("*") if p.is_file() and not p.is_symlink()
                  and not any(part.startswith(("package-", "verification-", "verify-", "ctree-")) for part in p.relative_to(results).parts)
                  and p.suffix in {".json", ".log", ".csv", ".export"}
                  and p.name != "private-provenance.json")


def require_successful_results(root: Path, rows: list[dict[str, str]]) -> None:
    results = root / "artifact/results"
    for name in ("audit.json", "assumptions.json", "source-inventory.json", "sizes.csv", "sizes-summary.json", "rocq-wc.log", "measurements.json", "kernel-check.log", "assumptions.log", "smoke.log"):
        require((results / name).is_file(), f"Missing required evidence: {name}")
    audit_data = json.loads((results / "audit.json").read_text())
    measurements = json.loads((results / "measurements.json").read_text())
    require(audit_data.get("success") is True and measurements.get("success") is True, "Audit/measurement did not succeed")
    require(set(audit_data.get("declarations", [])) == {r["declaration"] for r in rows}, "Audit declarations differ from theorem map")
    require(audit_data.get("theorem_map_sha256") == sha(root / "artifact/theorem-map.csv"), "Audit used a different theorem map")
    inv = json.loads((results / "source-inventory.json").read_text())
    expected = {p.relative_to(root).as_posix() for p in [*root.glob("theories/**/*.v"), *root.glob("examples/**/*.v")]}
    require({row["file"] for row in inv["files"]} == expected, "Evidence source inventory differs from current source set")
    for row in inv["files"]:
        require(sha(root / row["file"]) == row["sha256"], f"Source changed since evidence audit: {row['file']}")
    require(len(measurements.get("runs", [])) == 3 and all(r.get("exit_status") == 0 for r in measurements["runs"]), "Missing three successful measurements")
    require(measurements.get("recursive_kernel_check", {}).get("exit_status") == 0, "Missing measured recursive check")


def manifest_bytes(bundle: Path) -> bytes:
    paths = sorted((p for p in bundle.rglob("*") if p.is_file() and p != bundle / "MANIFEST.sha256"),
                   key=lambda p: p.relative_to(bundle).as_posix())
    return "".join(f"{sha(p)}  {p.relative_to(bundle).as_posix()}\n" for p in paths).encode("utf-8")


def check_private_content(bundle: Path) -> None:
    private_roots = [str(ROOT.resolve()), str(Path.home())]
    private_roots = [value for value in private_roots if value != "/" and len(value) > 3]
    for path in bundle.rglob("*"):
        require(not any(part in PRIVATE_DIRS or part.startswith("_build") for part in path.relative_to(bundle).parts), f"Private/build metadata leaked: {path.relative_to(bundle)}")
        require(not path.is_symlink(), f"Symlink in produced bundle: {path}")
        if not path.is_file():
            continue
        data = path.read_bytes()
        if b"\0" in data:
            continue
        text = data.decode("utf-8", errors="replace")
        require(not any(value in text for value in private_roots), f"Local workspace/home path leaked: {path.relative_to(bundle)}")
        require(LOCAL_PATH.search(text) is None, f"Absolute local path leaked: {path.relative_to(bundle)}")


def package(args: argparse.Namespace) -> None:
    require(args.theorem_map is None, "Packaging requires the canonical theorem map")
    rows, baseline = load_inputs(ROOT, None)
    require_successful_results(ROOT, rows)
    export = ROOT / "artifact/environment.export"
    require(export.is_file() and export.stat().st_size > 0, "Missing frozen artifact/environment.export")
    require(not args.output.is_symlink(), f"Refusing symlink output: {args.output}")
    output = args.output.resolve()
    require(not output.is_dir(), f"Output is an existing directory: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    runner = Runner(ROOT, args.switch, ROOT / "artifact/results")
    try:
        # Keep original revision and local working-byte provenance private.
        head = runner.run(["git", "rev-parse", "HEAD"], "package-private-revision.log").stdout.strip()
        provenance_path = ROOT / "artifact/private-provenance.json"
        provenance = json.loads(provenance_path.read_text()) if provenance_path.exists() else {"format": FORMAT}
        require(isinstance(provenance, dict), "Invalid existing private provenance")
        provenance.update({"packaged_development_revision": head, "packaged_baseline_capture_sha256": sha(ROOT / "artifact/baseline.json"), "packaged_working_files": {p.relative_to(ROOT).as_posix(): sha(p) for p in selected_sources(ROOT)}})
        put_json(provenance_path, provenance)
        with tempfile.TemporaryDirectory(prefix="tisl-package-") as temporary:
            scratch = Path(temporary)
            bundle, source = scratch / "tisl-A1", scratch / "tisl-A1/source"
            source.mkdir(parents=True)
            for path in selected_sources(ROOT):
                target = source / path.relative_to(ROOT)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, target)
                if path.name.lower().startswith("readme"):
                    # Local path provenance is metadata, not a copyright notice.
                    target.write_text(clean(target.read_text(encoding="utf-8"), (ROOT,)), encoding="utf-8")
            dune = source / "dune-project"
            dune.write_text(sanitize_dune(dune.read_text()), encoding="utf-8")
            docs = source / "docs/main.html"
            docs.write_text(sanitize_docs(docs.read_text()), encoding="utf-8")
            (source / "rocq-ticl.opam").unlink()
            runner.run(runner.opam("dune", "build", "--cache=disabled", "-j", "1", "rocq-ticl.opam.generated"), "package-opam-regeneration.log", cwd=source, prover=True)
            generated_path = source / "_build/default/rocq-ticl.opam.generated"
            require(generated_path.is_file(), "Dune did not generate packaged opam metadata")
            shutil.copyfile(generated_path, source / "rocq-ticl.opam")
            generated = (source / "rocq-ticl.opam").read_text()
            require(not re.search(r"(?m)^(?:authors|maintainer|homepage|bug-reports|dev-repo):", generated), "Identity fields remain in regenerated packaged opam")
            # Build products are never distributed; only the explicit source list.
            for path in list(source.iterdir()):
                if path.name.startswith("_build"):
                    shutil.rmtree(path)
            snapshot_dependency(bundle / "dependencies/ctrees", runner, scratch)
            shutil.copyfile(export, bundle / "environment.export")
            shutil.copyfile(ROOT / "artifact/theorem-map.csv", bundle / "theorem-map.csv")
            (bundle / "README.md").write_text(artifact_readme(), encoding="utf-8")
            for path in result_files(ROOT / "artifact/results"):
                target = bundle / "results" / path.relative_to(ROOT / "artifact/results")
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(clean(path.read_text(encoding="utf-8"), (ROOT,)), encoding="utf-8")
            # Frozen exports can carry local source pins. A local export is not
            # portable; require this recipe's original exact remote CTree pin.
            export_text = (bundle / "environment.export").read_text()
            require(CTREE in export_text and not LOCAL_PATH.search(export_text), "Frozen export lacks exact remote CTree pin or contains local paths")
            check_private_content(bundle)
            manifest = manifest_bytes(bundle)
            (bundle / "MANIFEST.sha256").write_bytes(manifest)
            identity = digest(manifest)
            candidate = scratch / "candidate.tar.gz"
            # Deterministic metadata makes same-byte reruns comparable, including gzip.
            import gzip
            with candidate.open("wb") as raw:
                with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped:
                    with tarfile.open(fileobj=zipped, mode="w", format=tarfile.PAX_FORMAT) as archive:
                        for path in sorted(bundle.rglob("*")):
                            if not path.is_file():
                                continue
                            rel = "tisl-A1/" + path.relative_to(bundle).as_posix()
                            info = tarfile.TarInfo(rel)
                            info.size = path.stat().st_size
                            info.mode = 0o755 if rel.endswith("/tools/artifact.py") else 0o644
                            info.mtime, info.uid, info.gid = 0, 0, 0
                            info.uname = info.gname = ""
                            with path.open("rb") as stream:
                                archive.addfile(info, stream)
            if output.exists():
                require(not output.is_symlink() and output.is_file() and sha(output) == sha(candidate), f"Refusing to replace different existing output: {output}")
            else:
                # Exclusive creation also handles a concurrently-created output.
                with output.open("xb") as target, candidate.open("rb") as stream:
                    shutil.copyfileobj(stream, target)
            report = {"format": FORMAT, "success": True, "artifact": "Tisl-A1", "manifest_sha256": identity, "artifact_identifier": "Tisl-A1:" + identity, "archive_sha256": sha(output), "archive": output.name, "ctree_revision": CTREE, "manifest_files": len(manifest.splitlines()), "package_verification": "Not established by packaging; run verify-package."}
            put_json(ROOT / "artifact/results/package-report.json", report)
            print(json.dumps(report, indent=2))
    finally:
        runner.records_json("package-commands.json")


def extract_verified(archive_path: Path, destination: Path) -> tuple[Path, str]:
    require(archive_path.is_file(), f"Missing archive: {archive_path}")
    with tarfile.open(archive_path, "r:gz") as archive:
        members = archive.getmembers()
        require(bool(members), "Empty archive")
        seen, regular = set(), {}
        for member in members:
            name = member.name.rstrip("/") if member.isdir() else member.name
            rel = safe_relative(name)
            require(rel.parts[0] == "tisl-A1", f"Unexpected archive root: {name}")
            require(name not in seen, f"Duplicate archive member: {name}")
            seen.add(name)
            require(member.isfile() or member.isdir(), f"Symlink/device/special archive member rejected: {name}")
            require(not any(part in PRIVATE_DIRS or part.startswith("_build") for part in rel.parts), f"Private metadata archive member: {name}")
            if member.isfile():
                regular[name] = member
        manifest_name = "tisl-A1/MANIFEST.sha256"
        require(manifest_name in regular, "Missing content manifest")
        stream = archive.extractfile(regular[manifest_name])
        require(stream is not None, "Unreadable content manifest")
        manifest = stream.read()
        entries: dict[str, str] = {}
        for line in manifest.decode("utf-8").splitlines():
            match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
            require(match is not None, f"Invalid manifest line: {line!r}")
            checksum, relative = match.groups()
            safe_relative(relative)
            require(relative != "MANIFEST.sha256" and relative not in entries, f"Duplicate/self manifest entry: {relative}")
            entries[relative] = checksum
        require(bool(entries) and list(entries) == sorted(entries), "Empty/unsorted manifest")
        require(set(regular) == {manifest_name} | {"tisl-A1/" + p for p in entries}, "Unmanifested or missing regular archive members")
        # Check ALL hashes before extraction and, crucially, before any opam work.
        for relative, checksum in entries.items():
            stream = archive.extractfile(regular["tisl-A1/" + relative])
            require(stream is not None, f"Unreadable member: {relative}")
            h = hashlib.sha256()
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                h.update(chunk)
            require(h.hexdigest() == checksum, f"Checksum mismatch: {relative}")
        for name, member in regular.items():
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            stream = archive.extractfile(member)
            require(stream is not None, f"Unreadable member: {name}")
            with target.open("xb") as output:
                shutil.copyfileobj(stream, output)
            target.chmod(0o755 if name.endswith("/tools/artifact.py") else 0o644)
    bundle = destination / "tisl-A1"
    check_private_content(bundle)
    for required in ["README.md", "environment.export", "theorem-map.csv", "source/tools/artifact.py", "source/dune-project", "source/artifact/baseline.json", "results/assumptions.json", "results/audit.json", "dependencies/ctrees/dune-project"]:
        require((bundle / required).is_file(), f"Missing required bundle file: {required}")
    require((bundle / "theorem-map.csv").read_bytes() == (bundle / "source/artifact/theorem-map.csv").read_bytes(), "Top-level/source theorem maps disagree")
    return bundle, digest(manifest)


def assumption_signature(data: dict[str, Any]) -> dict[str, Any]:
    require(data.get("format") == FORMAT and isinstance(data.get("declarations"), list), "Invalid assumptions JSON")
    result = {}
    for row in data["declarations"]:
        name = row["declaration"]
        require(name not in result and isinstance(row.get("assumptions"), list) and isinstance(row.get("closed"), bool), "Malformed/duplicate assumption entry")
        result[name] = {"closed": row["closed"], "assumptions": sorted((a["name"], " ".join(a["type"].split())) for a in row["assumptions"])}
    require(bool(result), "Empty assumptions comparison")
    return result


def verify_package(args: argparse.Namespace) -> None:
    require(args.theorem_map is None, "Package verification uses its own canonical theorem map")
    results = ROOT / "artifact/results"
    # No opam command or environment installation can precede this entire gate.
    with tempfile.TemporaryDirectory(prefix="tisl-verify-") as temporary:
        scratch = Path(temporary)
        bundle, identity = extract_verified(args.archive.resolve(), scratch)
        source = bundle / "source"
        rows, _ = load_inputs(source, None)
        expected = assumption_signature(json.loads((bundle / "results/assumptions.json").read_text()))
        declarations = {r["declaration"] for r in rows}
        require(set(expected) == declarations, "Reported assumptions omit/add theorem-map declarations")
        report_audit = json.loads((bundle / "results/audit.json").read_text())
        require(report_audit.get("success") is True and set(report_audit.get("declarations", [])) == declarations, "Reported audit did not check all declarations")
        require(report_audit.get("theorem_map_sha256") == sha(bundle / "theorem-map.csv"), "Reported audit theorem-map hash differs")
        reported_inventory = json.loads((bundle / "results/source-inventory.json").read_text())
        expected_hashes = {row["file"]: row["sha256"] for row in reported_inventory["files"]}
        actual_hashes = {path.relative_to(source).as_posix(): sha(path) for path in [*source.glob("theories/**/*.v"), *source.glob("examples/**/*.v")]}
        require(expected_hashes == actual_hashes, "Packaged Rocq source inventory differs from reported source bytes")
        attempt = 1
        while any(results.glob(f"verification-{identity[:16]}-{attempt}*")):
            attempt += 1
        prefix = f"verification-{identity[:16]}-{attempt}"
        runner = Runner(source, args.switch, results)
        try:
            response = runner.run(["opam", "switch", "list", "--switch", args.switch, "--short", "--color=never"], prefix + "-switch-list.log")
            switches = set(response.stdout.split())
            number = 1
            while f"tisl-A1-check-{number}" in switches:
                number += 1
            switch = f"tisl-A1-check-{number}"
            runner.run(["opam", "switch", "create", switch, "--empty", "--no-switch", "-y"], prefix + "-switch-create.log")
            runner.switch = switch
            runner.run(["opam", "repository", "add", "rocq-released", "https://rocq-prover.org/opam/released", "--switch", switch, "-y"], prefix + "-repository.log")
            runner.run(["opam", "switch", "import", "--switch", switch, str(bundle / "environment.export"), "-y"], prefix + "-switch-import.log")
            runner.run(["opam", "pin", "add", "--switch", switch, "-y", "rocq-ctree.2.0-dev", str(bundle / "dependencies/ctrees")], prefix + "-ctree-pin.log")
            runner.run(runner.opam("dune", "build", "--cache=disabled", "-j", "1", "--display", "verbose"), prefix + "-full-build.log", prover=True)
            runner.run([sys.executable, str(source / "tools/artifact.py"), "audit", "--switch", switch], prefix + "-audit.log", prover=True)
            rechecked_path = source / "artifact/results/assumptions.json"
            require(rechecked_path.is_file(), "Extracted audit produced no assumptions")
            actual = assumption_signature(json.loads(rechecked_path.read_text()))
            require(actual == expected, "Rechecked declarations/assumptions differ from reported results")
            rechecked_audit = json.loads((source / "artifact/results/audit.json").read_text())
            require(rechecked_audit.get("success") is True and set(rechecked_audit.get("declarations", [])) == declarations and rechecked_audit.get("recursive_kernel_check") is True, "Extracted audit did not complete full recursive checking")
            rechecked_inventory = json.loads((source / "artifact/results/source-inventory.json").read_text())
            require({row["file"]: row["sha256"] for row in rechecked_inventory["files"]} == expected_hashes, "Rebuilt Rocq source inventory differs from reported bytes")
            report = {"format": FORMAT, "success": True, "artifact_identifier": "Tisl-A1:" + identity, "manifest_sha256": identity, "archive_sha256": sha(args.archive), "verification_switch": switch, "declaration_count": len(actual), "declarations": sorted(actual), "assumptions_equal": True, "all_packaged_source_built": True, "recursive_kernel_check": True, "timings_compared": False, "note": "Fresh verification switch retained; original/default switch not changed."}
            put_json(results / (prefix + ".json"), report)
            print(json.dumps(report, indent=2))
        finally:
            runner.records_json(prefix + "-commands.json")
            # Retain raw fresh-audit evidence on failures as well as success.
            for path in (source / "artifact/results").rglob("*"):
                if path.is_file():
                    target = results / (prefix + "-evidence") / path.relative_to(source / "artifact/results")
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text(clean(path.read_text(encoding="utf-8"), (source, scratch)), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("audit", "measure", "package", "verify-package"):
        command = sub.add_parser(name)
        command.add_argument("--switch", required=True)
        command.add_argument("--theorem-map", type=Path, help="Alternate audit/measurement map (e.g. failure-path check)")
        if name == "package":
            command.add_argument("--output", type=Path, required=True)
        if name == "verify-package":
            command.add_argument("--archive", type=Path, required=True)
    args = parser.parse_args()
    try:
        require(bool(args.switch.strip()) and not args.switch.startswith("-"), "Invalid switch name")
        {"audit": audit, "measure": measure, "package": package, "verify-package": verify_package}[args.command](args)
        return 0
    except (EvidenceError, OSError, ValueError, KeyError, TypeError, tarfile.TarError, EOFError, UnicodeError) as exc:
        print(f"artifact: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
