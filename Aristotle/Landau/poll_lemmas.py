#!/usr/bin/env python3
"""Poll Aristotle for lemma proof status."""
import asyncio
from pathlib import Path
from aristotlelib import Project

PROJECTS = {
    "scalarFactor": "ceaeb1db-f112-4d52-b851-8d5b4ce8614a",
    "logDeriv": "6dcc521d-94ca-4363-8fe0-eb991d0d4e69",
    "fluxFactor": "9b75d723-a1b4-4fad-a613-4ee95bb48614",
    "vGradSmooth": "ace0d26e-669c-4d24-91fb-088cd988c7d2",
    "dotIntegral": "4b18b3b4-d305-4f06-ab5a-fcab1b2be764",
    "dblSub": "dff096bf-f6b7-472d-8b3e-9cddfcb1d08e",
    "gaussianIntegrability": "d82b2541-97f2-42dd-a5a0-ceb54be354bc",
    "nonnegDblZero": "2182c271-4707-433e-baa1-0fd25c907dc2",
    "vIBP": "da233eee-c578-471b-bf49-14e84e91b638",
    "fubiniAntisym": "bee8cb84-2f48-42fd-8182-48ba6b2e6e45",
    "transportVanishes": "0125e22c-7a2c-4387-b968-3bfa6ec819df",
    "nonposIntegralZero": "6d4fcf8b-058c-445c-a125-1d1a36f3a7e9",
    # v2 resubmissions with fixed hypotheses
    "gaussianIntegrability_v2": "29d34af7-8054-4767-afcd-6fa50edb7ccd",
    "nonnegDblZero_v2": "50853274-95bf-49f7-a8f1-bfac2fd02088",
    "nonposIntegralZero_v2": "b20790fb-0223-4a12-a51f-01f710500bb9",
    "dblSub_v2": "80468431-a720-403d-84e3-e30e0034702b",
    # v3 resubmissions
    "nonnegDblZero_v3": "d753343a-a37e-48f5-a368-c96714c40763",
    # polynomial extraction lemmas
    "poly_cubic": "ac65567c-ffb1-45fe-824c-28e342e718cd",
    "poly_killing": "9ecd146a-9c93-4914-9216-34f0348a73d9",
    "poly_linear": "f2cf4993-21c9-4125-9a36-fd160c779f04",
}

async def main():
    for name, pid in PROJECTS.items():
        try:
            p = await Project.from_id(pid)
            status = str(p.status)
            if 'COMPLETE' in status.upper():
                try:
                    sol_path = await p.get_solution()
                    if sol_path and sol_path.exists():
                        content = sol_path.read_text()
                        has_sorry = 'sorry' in content
                        negated = 'negated' in content.lower() or 'negate_state' in content
                        if negated:
                            label = 'NEGATED (false)'
                        elif has_sorry:
                            label = 'HAS_SORRY'
                        else:
                            label = 'PROVED'
                    else:
                        label = 'NO_FILE'
                except Exception as e2:
                    label = f'GET_SOL_ERROR: {e2}'
            else:
                label = status.replace('ProjectStatus.', '')
            print(f"{name:35s} {label}")
        except Exception as e:
            print(f"{name:35s} ERROR: {e}")

asyncio.run(main())
