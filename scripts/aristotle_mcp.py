#!/usr/bin/env python3
"""Zero-dep MCP stdio server wrapping the Aristotle CLI.

Exposes four tools:
  submit(prompt)        -> uploads lean/ via --project-dir, returns project id
  list()                -> lists recent Aristotle jobs
  result(project_id)    -> downloads tarball, extracts to /tmp/aristotle-<id>/
  cancel(project_id)    -> cancels an in-progress job

Reads ARISTOTLE_API_KEY from env if set, otherwise from
  <repo_root>/aristotle-key.sh (an `export ARISTOTLE_API_KEY=...` line).

Speaks JSON-RPC 2.0 over newline-delimited stdio (Claude Code MCP default).
"""

import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
KEY_FILE = REPO_ROOT / "aristotle-key.sh"
LEAN_DIR = REPO_ROOT / "lean"
STAGING_DIR = REPO_ROOT / "aristotle-staging"


def load_key() -> None:
    if os.environ.get("ARISTOTLE_API_KEY"):
        return
    if not KEY_FILE.exists():
        return
    match = re.search(r"ARISTOTLE_API_KEY\s*=\s*(\S+)", KEY_FILE.read_text())
    if match:
        os.environ["ARISTOTLE_API_KEY"] = match.group(1)


load_key()

TOOLS = [
    {
        "name": "submit",
        "description": (
            "Submit an Aristotle Lean job. Uploads the lean/ directory as --project-dir "
            "so the upload stays focused on the Lean project (no Rust/docs noise). "
            "Returns the project id printed by the Aristotle CLI."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "prompt": {
                    "type": "string",
                    "description": "Instructions for Aristotle (passed as the submit prompt).",
                }
            },
            "required": ["prompt"],
        },
    },
    {
        "name": "list",
        "description": "List recent Aristotle jobs with status, progress, and creation time.",
        "inputSchema": {"type": "object", "properties": {}},
    },
    {
        "name": "result",
        "description": (
            "Download and extract the result tarball for a completed Aristotle job. "
            "Extracts to /tmp/aristotle-<project_id>/ and returns the extraction path."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "project_id": {
                    "type": "string",
                    "description": "UUID returned by `submit` or shown in `list`.",
                }
            },
            "required": ["project_id"],
        },
    },
    {
        "name": "cancel",
        "description": "Cancel an in-progress or queued Aristotle job.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "project_id": {
                    "type": "string",
                    "description": "UUID of the job to cancel.",
                }
            },
            "required": ["project_id"],
        },
    },
    {
        "name": "diff_result",
        "description": (
            "Diff a file from an extracted Aristotle result against the current working tree. "
            "Path is relative to the lean/ project root (e.g. 'Turyn/Equivalence.lean'). "
            "Requires `result` to have been called first on the project_id. "
            "Auto-detects tarball layout (project_aristotle/<path> or project_aristotle/lean/<path>)."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "project_id": {
                    "type": "string",
                    "description": "UUID of the Aristotle job whose result has been extracted.",
                },
                "path": {
                    "type": "string",
                    "description": "File path relative to lean/ (e.g. 'Turyn/Equivalence.lean').",
                },
            },
            "required": ["project_id", "path"],
        },
    },
    {
        "name": "git_commit",
        "description": (
            "Stage the listed files and create a commit in the turyn repo root. "
            "File paths are relative to the repo root. Scoped to this repo only."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "files": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": "Relative paths to stage with `git add` before committing.",
                },
                "message": {
                    "type": "string",
                    "description": "Full commit message (heredoc, may include newlines and co-author trailers).",
                },
            },
            "required": ["files", "message"],
        },
    },
]


def run_cli(args: list, cwd=None, timeout: int = 300) -> str:
    try:
        r = subprocess.run(
            ["aristotle", *args],
            capture_output=True,
            text=True,
            cwd=cwd,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return f"ERROR: aristotle {' '.join(args[:2])} timed out after {timeout}s"
    except FileNotFoundError:
        return "ERROR: `aristotle` CLI not found on PATH"
    return (r.stdout or "") + (r.stderr or "")


def handle_submit(prompt: str) -> str:
    return run_cli(["submit", prompt, "--project-dir", "."], cwd=LEAN_DIR, timeout=180)


def handle_list() -> str:
    return run_cli(["list"], timeout=60)


def handle_result(project_id: str) -> str:
    STAGING_DIR.mkdir(exist_ok=True)
    dest = STAGING_DIR / f"{project_id}.tar.gz"
    out = run_cli(["result", project_id, "--destination", str(dest)], timeout=300)
    extract_dir = STAGING_DIR / project_id
    extract_dir.mkdir(exist_ok=True)
    try:
        with tarfile.open(dest, "r:gz") as tf:
            tf.extractall(extract_dir)
        out += f"\nExtracted to: {extract_dir}"
    except Exception as e:
        out += f"\nExtract failed: {e}"
    return out


def handle_cancel(project_id: str) -> str:
    return run_cli(["cancel", project_id], timeout=30)


def run_git(args: list, timeout: int = 60, input_text: str | None = None) -> str:
    try:
        r = subprocess.run(
            ["git", "-C", str(REPO_ROOT), *args],
            capture_output=True,
            text=True,
            timeout=timeout,
            input=input_text,
        )
    except subprocess.TimeoutExpired:
        return f"ERROR: git {' '.join(args[:2])} timed out after {timeout}s"
    except FileNotFoundError:
        return "ERROR: `git` not found on PATH"
    out = (r.stdout or "") + (r.stderr or "")
    if r.returncode != 0:
        out += f"\n(git exited {r.returncode})"
    return out


def handle_diff_result(project_id: str, path: str) -> str:
    extract_dir = STAGING_DIR / project_id
    if not extract_dir.exists():
        return f"ERROR: extracted directory not found: {extract_dir}\n(Call `result` first.)"
    # Auto-detect layout: new (lean/ at root of project_aristotle/) or old (project_aristotle/lean/...)
    candidates = [
        extract_dir / "project_aristotle" / path,
        extract_dir / "project_aristotle" / "lean" / path,
    ]
    tarball_file = next((c for c in candidates if c.exists()), None)
    if tarball_file is None:
        return f"ERROR: {path} not found in tarball for {project_id}. Tried: {[str(c) for c in candidates]}"
    working_file = LEAN_DIR / path
    if not working_file.exists():
        return f"ERROR: {path} not present in working tree at {working_file}"
    try:
        r = subprocess.run(
            ["diff", "-u", str(working_file), str(tarball_file)],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except FileNotFoundError:
        return "ERROR: `diff` not found on PATH"
    out = r.stdout or ""
    if r.returncode == 0:
        out = "(files are identical)"
    return out


def handle_git_commit(files: list, message: str) -> str:
    if not files:
        return "ERROR: no files to commit"
    for f in files:
        # reject absolute paths and paths escaping repo root
        p = (REPO_ROOT / f).resolve()
        try:
            p.relative_to(REPO_ROOT)
        except ValueError:
            return f"ERROR: refusing file outside repo root: {f}"
    add_out = run_git(["add", "--", *files])
    commit_out = run_git(["commit", "-F", "-"], input_text=message)
    return f"--- git add ---\n{add_out}\n--- git commit ---\n{commit_out}"


def respond(msg_id, result=None, error=None) -> None:
    resp = {"jsonrpc": "2.0", "id": msg_id}
    if error is not None:
        resp["error"] = error
    else:
        resp["result"] = result
    sys.stdout.write(json.dumps(resp) + "\n")
    sys.stdout.flush()


def process(msg: dict) -> None:
    method = msg.get("method")
    msg_id = msg.get("id")
    params = msg.get("params", {}) or {}

    if method == "initialize":
        respond(
            msg_id,
            {
                "protocolVersion": "2024-11-05",
                "capabilities": {"tools": {}},
                "serverInfo": {"name": "aristotle", "version": "0.1.0"},
            },
        )
        return

    if method in ("initialized", "notifications/initialized"):
        return  # client notification, no response needed

    if method == "tools/list":
        respond(msg_id, {"tools": TOOLS})
        return

    if method == "tools/call":
        name = params.get("name")
        args = params.get("arguments", {}) or {}
        try:
            if name == "submit":
                text = handle_submit(args["prompt"])
            elif name == "list":
                text = handle_list()
            elif name == "result":
                text = handle_result(args["project_id"])
            elif name == "cancel":
                text = handle_cancel(args["project_id"])
            elif name == "diff_result":
                text = handle_diff_result(args["project_id"], args["path"])
            elif name == "git_commit":
                text = handle_git_commit(args["files"], args["message"])
            else:
                respond(msg_id, error={"code": -32601, "message": f"Unknown tool: {name}"})
                return
            respond(msg_id, {"content": [{"type": "text", "text": text}]})
        except Exception as e:
            respond(msg_id, error={"code": -32603, "message": f"{type(e).__name__}: {e}"})
        return

    if msg_id is not None:
        respond(msg_id, error={"code": -32601, "message": f"Method not found: {method}"})


def main() -> None:
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        try:
            process(msg)
        except Exception as e:
            # last-ditch safety net; never crash the server
            sys.stderr.write(f"process error: {e}\n")
            sys.stderr.flush()


if __name__ == "__main__":
    main()
