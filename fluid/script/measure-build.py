"""Time evaluation and materialisation per figure on given sites; median and minimum over given number of runs"""

import os
import pathlib
import re
import statistics
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
FLUID = ROOT / "fluid/dist/fluid/shared/fluid.mjs"
MAXRSS_PER_MB = 2**20 if sys.platform == "darwin" else 2**10


def measure(site, spec):
    """Times in milliseconds of evaluation and materialisation, and peak resident memory in megabytes"""
    with tempfile.TemporaryDirectory() as out:
        process = subprocess.Popen(["node", FLUID, "build", "--timing", "-o", out, f"spec/{spec.name}"],
                                   cwd=site, stdout=subprocess.PIPE, text=True)
        output = process.stdout.read()
        _, status, usage = os.wait4(process.pid, 0)
        process.returncode = os.waitstatus_to_exitcode(status)
    if process.returncode != 0:
        sys.exit(f"Build of {spec} failed: {output}")
    times = re.search(r"evaluate ([\d.]+) ms, materialise ([\d.]+) ms", output)
    return float(times[1]), float(times[2]), usage.ru_maxrss / MAXRSS_PER_MB


def summary(readings):
    return f"{statistics.median(readings):.0f} (min {min(readings):.0f})"


runs = int(sys.argv[1])
for site in (ROOT / "website" / name for name in sys.argv[2:]):
    for spec in sorted((site / "spec").glob("*.json")):
        evaluate, materialise, memory = zip(*(measure(site, spec) for _ in range(runs)))
        print(f"{site.name}/{spec.stem}: evaluate {summary(evaluate)} ms, materialise {summary(materialise)} ms, "
              f"memory {summary(memory)} MB")
