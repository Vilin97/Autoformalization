#!/usr/bin/env python3
"""
Check status of pending Aristotle jobs and download solutions.

Usage:
  python check-aristotle.py          # check all jobs
  python check-aristotle.py submit   # submit a file and add it to jobs.json
"""

import asyncio
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).parent
JOBS_FILE = HERE / "aristotle-jobs.json"

def load_jobs():
    with open(JOBS_FILE) as f:
        return json.load(f)

def save_jobs(data):
    with open(JOBS_FILE, "w") as f:
        json.dump(data, f, indent=2)
    print(f"Updated {JOBS_FILE}")

async def check_all():
    from aristotlelib import Project

    data = load_jobs()
    jobs = data["jobs"]
    pending = [j for j in jobs if j.get("status") not in ("done", "expired", "failed")]

    if not pending:
        print("No pending jobs.")
        expired = [j for j in jobs if j.get("status") == "expired"]
        if expired:
            print(f"{len(expired)} expired job(s) need resubmission:")
            for j in expired:
                print(f"  [{j['id'][:8]}] {j.get('target','?')} — {j['submission']}")
        return

    for job in pending:
        jid = job["id"]
        short = jid[:8]
        target = job.get("target", "?")
        try:
            p = await Project.from_id(jid)
            status = getattr(p, "status", "unknown")
            print(f"\n[{short}] {target}: {status}")

            if status in ("complete", "success", "proved"):
                sol = await p.get_solution()
                out_path = HERE / job["output"]
                out_path.parent.mkdir(exist_ok=True)
                # sol is a PosixPath to the downloaded file; copy it
                import shutil
                shutil.copy(str(sol), str(out_path))
                job["status"] = "done"
                job["solution"] = str(out_path)
                print(f"  ✓ Solution saved to {out_path}")
            elif status in ("failed", "disproved"):
                job["status"] = "failed"
                print(f"  ✗ Failed — may need to fix the statement")
            else:
                print(f"  … Still running")
        except Exception as e:
            if "500" in str(e):
                print(f"[{short}] {target}: EXPIRED (500) — needs resubmit")
                job["status"] = "expired"
            else:
                print(f"[{short}] {target}: ERROR — {e}")

    save_jobs(data)

async def submit(file_path, output_path=None, note=""):
    """Submit a file and record the job."""
    import subprocess
    file_path = Path(file_path)
    if output_path is None:
        stem = file_path.stem
        output_path = HERE / "aristotle-out" / f"{stem}_aristotle.lean"

    cmd = [
        "aristotle", "prove-from-file", str(file_path),
        "--output-file", str(output_path),
        "--no-wait"
    ]
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr

    # Extract project ID
    import re
    m = re.search(r"Created project ([0-9a-f-]{36})", output)
    if not m:
        print("Could not find project ID in output:")
        print(output)
        return

    job_id = m.group(1)
    short_id = job_id.split("-")[0]
    print(f"Submitted: {file_path.name} → job {short_id}")

    data = load_jobs()
    # Remove old entry for same submission if present
    # Store paths relative to HERE; resolve first to handle both absolute and relative inputs
    file_path_abs = file_path.resolve()
    out_path_abs = Path(output_path).resolve()
    try:
        rel_submission = str(file_path_abs.relative_to(HERE.resolve()))
        rel_output = str(out_path_abs.relative_to(HERE.resolve()))
    except ValueError:
        rel_submission = str(file_path)
        rel_output = str(output_path)

    data["jobs"] = [j for j in data["jobs"] if j.get("submission") != rel_submission]
    data["jobs"].append({
        "id": job_id,
        "submission": rel_submission,
        "output": rel_output,
        "target": file_path.stem,
        "note": note
    })
    save_jobs(data)

if __name__ == "__main__":
    if len(sys.argv) >= 2 and sys.argv[1] == "submit":
        if len(sys.argv) < 3:
            print("Usage: check-aristotle.py submit <file> [note]")
            sys.exit(1)
        note = sys.argv[3] if len(sys.argv) > 3 else ""
        asyncio.run(submit(sys.argv[2], note=note))
    else:
        asyncio.run(check_all())
