#!/usr/bin/env python3
"""Poll Aristotle project statuses and download completed solutions."""
import os
import sys
import asyncio
sys.path.insert(0, '/Users/vasil/miniconda3/lib/python3.12/site-packages')

from aristotlelib import Project

# Round 1 (original) - still running
round1_running = {
    "aa30a82c-5146-454e-8ad5-b6d18d455e41": ("gap13", "Gap 13: killing_const_torus"),
    "e0985df9-e988-445e-ab66-d92581f98a54": ("gap01_02", "Gaps 1-2: IBP+Fubini"),
    "a3d7e4b4-bd17-43e3-9904-2e894c96aa91": ("gap03_04_05", "Gaps 3-5: score+PSD+quadform"),
}

# Round 1 - already proved
round1_proved = {
    "gap12": "Gap 12: cubic_coeff_zero",
    "gap19": "Gap 19: force_balance",
    "gap14": "Gap 14: div_scalar_linear",
    "gap06": "Gap 6: parallel->affine",
    "gap07": "Gap 7: affine->quadratic",
    "gap08": "Gap 8: maxwellian_flux_zero",
    "gap10": "Gap 10: nonpos_integral_zero",
}

# Round 2 (revised statements)
round2 = {
    "90367d75-12bb-414b-af95-d2a37a199bcc": ("gap09", "Gap 9v2: transport sub-lemmas"),
    "f9340f25-ce08-4489-b524-212499ceda99": ("gap11", "Gap 11v2: integrable->c0<0"),
    "4c2bb516-4f97-41a0-903e-3dd649a926f0": ("gap15", "Gap 15v2: max principle w/ axioms"),
    "747fe81d-73b4-454d-9b5f-30d508cb0bb9": ("gap16_17", "Gaps 16-17v2: Faraday+Stokes w/ axioms"),
    "47651d10-276e-4a62-aa31-0a8db592b05b": ("gap18", "Gap 18v2: decomposed energy"),
}

# Round 3+ (further decompositions)
round3 = {
    "21bfaccc-1d75-4f69-8938-668e38ebd2d6": ("gap04", "Gap 4: double integral nonneg"),
    "bbcd582d-23aa-482c-9be6-1774c6015f47": ("gap05", "Gap 5: nonneg integral zero"),
    "69c17a3b-c443-4664-98cc-159d1ccfcb6d": ("gap13", "Gap 13v2: killing algebraic"),
    "ef638419-bd8d-4f8a-98ea-86078afbe591": ("gap01", "Gap 1: IBP standalone"),
    "194375c4-263e-4b78-8da0-9f7e7932b054": ("gap02", "Gap 2: Fubini standalone"),
    "597112ce-0d9d-4403-b645-f87b6291c098": ("gap03", "Gap 3: score form standalone"),
}

async def poll():
    print("=== Round 1: Already Proved ===\n")
    for fname, desc in round1_proved.items():
        print(f"  + {desc}")

    for label, jobs in [("Round 1: Still Running", round1_running),
                        ("Round 2: Revised", round2),
                        ("Round 3+: Decomposed", round3)]:
        print(f"\n=== {label} ===\n")
        for pid, (fname, desc) in jobs.items():
            try:
                p = await Project.from_id(pid)
                status_str = str(p.status)
                pct = getattr(p, 'percent_complete', '?')
                if "COMPLETE" in status_str:
                    output = f"Aristotle/Landau/{fname}_aristotle.lean"
                    if not os.path.exists(output):
                        try:
                            await p.get_solution(output)
                            print(f"  + {desc}: DONE -> downloaded")
                        except Exception as e2:
                            print(f"  + {desc}: DONE (dl err: {e2})")
                    else:
                        print(f"  + {desc}: DONE (file exists)")
                elif "FAIL" in status_str:
                    print(f"  X {desc}: FAILED")
                else:
                    print(f"  . {desc}: {status_str} ({pct}%)")
            except Exception as e:
                print(f"  ? {desc}: error ({e})")

asyncio.run(poll())
