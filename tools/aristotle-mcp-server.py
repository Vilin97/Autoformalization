#!/usr/bin/env python3.10
"""
MCP server for Aristotle automated theorem prover.

Exposes aristotlelib functionality as MCP tools so Claude Code can
submit jobs, check status, download results, and manage projects.
"""

import asyncio
import json
import os
import shutil
import tarfile
import tempfile
from datetime import datetime
from pathlib import Path

from mcp.server.fastmcp import FastMCP

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _ensure_api_key():
    """Load API key from environment or .env file."""
    if os.environ.get("ARISTOTLE_API_KEY"):
        return
    env_path = Path(__file__).resolve().parent.parent / ".env"
    if env_path.exists():
        for line in env_path.read_text().splitlines():
            line = line.strip()
            if line.startswith("export "):
                line = line[len("export "):]
            if line.startswith("ARISTOTLE_API_KEY="):
                val = line.split("=", 1)[1].strip().strip('"').strip("'")
                os.environ["ARISTOTLE_API_KEY"] = val
                return
    raise RuntimeError(
        "ARISTOTLE_API_KEY not found. Set it in the environment or in .env"
    )


def _project_to_dict(p) -> dict:
    """Serialize a Project to a JSON-friendly dict."""
    return {
        "project_id": p.project_id,
        "status": str(p.status.value) if p.status else "UNKNOWN",
        "created_at": p.created_at.isoformat() if p.created_at else None,
        "last_updated_at": p.last_updated_at.isoformat() if p.last_updated_at else None,
        "percent_complete": p.percent_complete,
        "input_prompt": p.input_prompt,
        "file_name": p.file_name,
        "description": p.description,
    }


# ---------------------------------------------------------------------------
# MCP Server
# ---------------------------------------------------------------------------

mcp = FastMCP(
    "aristotle",
    instructions=(
        "Aristotle MCP server — interact with the Aristotle automated theorem prover. "
        "Submit Lean projects or prompts, check job status, download results, "
        "list recent projects, and cancel jobs."
    ),
)


@mcp.tool()
async def submit_file(
    file_path: str,
    prompt: str = "Fill in the sorries",
) -> str:
    """Submit a single Lean file to Aristotle.

    The file is packaged as a tar.gz and submitted. Returns the project ID
    and status. Use this for standalone .lean files in aristotle-in/.

    Args:
        file_path: Absolute path to the .lean file to submit.
        prompt: Instructions for Aristotle (default: "Fill in the sorries").
    """
    _ensure_api_key()
    from aristotlelib import Project

    p = Path(file_path).resolve()
    if not p.exists():
        return json.dumps({"error": f"File not found: {p}"})

    with tempfile.TemporaryDirectory() as tmpdir:
        tar_path = Path(tmpdir) / "submission.tar.gz"
        with tarfile.open(tar_path, "w:gz") as tar:
            tar.add(str(p), arcname=p.name)
        project = await Project.create(
            prompt=prompt,
            tar_file_path=tar_path,
            public_file_path=str(p.name),
        )

    return json.dumps(_project_to_dict(project), indent=2)


@mcp.tool()
async def submit_directory(
    project_dir: str,
    prompt: str = "Fill in the sorries",
) -> str:
    """Submit a Lean project directory to Aristotle.

    Aristotle will package the directory (skipping build artifacts) and submit it.
    Use this for multi-file Lean projects with lakefile.toml, lean-toolchain, etc.

    Args:
        project_dir: Absolute path to the Lean project directory.
        prompt: Instructions for Aristotle (default: "Fill in the sorries").
    """
    _ensure_api_key()
    from aristotlelib import Project

    d = Path(project_dir).resolve()
    if not d.is_dir():
        return json.dumps({"error": f"Directory not found: {d}"})

    project = await Project.create_from_directory(
        prompt=prompt,
        project_dir=d,
    )
    return json.dumps(_project_to_dict(project), indent=2)


@mcp.tool()
async def submit_prompt(
    prompt: str,
) -> str:
    """Submit a plain-English prompt to Aristotle (no files).

    Aristotle will formalize and prove the statement. Use this for
    self-contained math problems or questions.

    Args:
        prompt: The theorem or question in natural language.
    """
    _ensure_api_key()
    from aristotlelib import Project

    project = await Project.create(prompt=prompt)
    return json.dumps(_project_to_dict(project), indent=2)


@mcp.tool()
async def get_status(
    project_id: str,
) -> str:
    """Check the status of an Aristotle project.

    Args:
        project_id: The project UUID.
    """
    _ensure_api_key()
    from aristotlelib import Project

    project = await Project.from_id(project_id)
    return json.dumps(_project_to_dict(project), indent=2)


@mcp.tool()
async def list_projects(
    limit: int = 10,
    status_filter: str = "",
) -> str:
    """List recent Aristotle projects.

    Args:
        limit: Max number of projects to return (1-100, default 10).
        status_filter: Comma-separated statuses to filter by
            (e.g. "IN_PROGRESS,QUEUED"). Empty = all statuses.
    """
    _ensure_api_key()
    from aristotlelib import Project, ProjectStatus

    statuses = None
    if status_filter.strip():
        statuses = []
        for s in status_filter.split(","):
            s = s.strip().upper()
            try:
                statuses.append(ProjectStatus(s))
            except ValueError:
                return json.dumps({"error": f"Unknown status: {s}"})

    projects, next_key = await Project.list_projects(
        limit=limit,
        status=statuses,
    )
    result = {
        "projects": [_project_to_dict(p) for p in projects],
        "count": len(projects),
        "next_pagination_key": next_key,
    }
    return json.dumps(result, indent=2)


@mcp.tool()
async def download_result(
    project_id: str,
    destination: str = "",
) -> str:
    """Download the result of a completed Aristotle project.

    If destination is empty, saves to a temp file and returns the path.
    For tar.gz results, also lists the archive contents.

    Args:
        project_id: The project UUID.
        destination: Where to save the result file (optional).
    """
    _ensure_api_key()
    from aristotlelib import Project

    project = await Project.from_id(project_id)
    status_str = str(project.status.value) if project.status else "UNKNOWN"

    if status_str not in ("COMPLETE", "COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET"):
        return json.dumps({
            "error": f"Project is not complete (status: {status_str})",
            "project": _project_to_dict(project),
        }, indent=2)

    dest = Path(destination) if destination else None
    result_path = await project.get_solution(destination=dest)

    info = {
        "downloaded_to": str(result_path),
        "project": _project_to_dict(project),
    }

    # If it's a tar.gz, list contents
    if str(result_path).endswith(".tar.gz") or str(result_path).endswith(".tgz"):
        try:
            with tarfile.open(result_path, "r:gz") as tar:
                info["archive_contents"] = tar.getnames()
        except Exception:
            pass

    return json.dumps(info, indent=2)


@mcp.tool()
async def extract_result(
    project_id: str,
    extract_to: str,
) -> str:
    """Download and extract the result of a completed Aristotle project.

    Downloads the tar.gz result and extracts it to the specified directory.

    Args:
        project_id: The project UUID.
        extract_to: Directory to extract the result into.
    """
    _ensure_api_key()
    from aristotlelib import Project

    project = await Project.from_id(project_id)
    status_str = str(project.status.value) if project.status else "UNKNOWN"

    if status_str not in ("COMPLETE", "COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET"):
        return json.dumps({
            "error": f"Project is not complete (status: {status_str})",
            "project": _project_to_dict(project),
        }, indent=2)

    with tempfile.TemporaryDirectory() as tmpdir:
        tar_path = Path(tmpdir) / "result.tar.gz"
        await project.get_solution(destination=tar_path)

        extract_dir = Path(extract_to).resolve()
        extract_dir.mkdir(parents=True, exist_ok=True)

        extracted_files = []
        with tarfile.open(tar_path, "r:gz") as tar:
            tar.extractall(path=extract_dir)
            extracted_files = tar.getnames()

    return json.dumps({
        "extracted_to": str(extract_dir),
        "files": extracted_files,
        "project": _project_to_dict(project),
    }, indent=2)


@mcp.tool()
async def cancel_project(
    project_id: str,
) -> str:
    """Cancel a queued or in-progress Aristotle project.

    Args:
        project_id: The project UUID.
    """
    _ensure_api_key()
    from aristotlelib import Project

    project = await Project.from_id(project_id)
    await project.cancel()
    await project.refresh()
    return json.dumps({
        "message": "Project canceled",
        "project": _project_to_dict(project),
    }, indent=2)


@mcp.tool()
async def refresh_status(
    project_id: str,
) -> str:
    """Refresh and return the latest status of an Aristotle project.

    Useful for polling a project that was previously in progress.

    Args:
        project_id: The project UUID.
    """
    _ensure_api_key()
    from aristotlelib import Project

    project = await Project.from_id(project_id)
    await project.refresh()
    return json.dumps(_project_to_dict(project), indent=2)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    mcp.run()
