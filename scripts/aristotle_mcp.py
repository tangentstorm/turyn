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
    dest = Path(tempfile.gettempdir()) / f"aristotle-{project_id}.tar.gz"
    out = run_cli(["result", project_id, "--destination", str(dest)], timeout=300)
    extract_dir = Path(tempfile.gettempdir()) / f"aristotle-{project_id}"
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
