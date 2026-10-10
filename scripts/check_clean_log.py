#!/usr/bin/env python3
"""Reject diagnostics and holes; successful compiler exit is checked by the runner."""
from pathlib import Path
import re
import sys

def check(data):
    if re.search(r"warning:|\berror(?:\([^)]*\))?:|sorryAx|declaration uses\s+['`\"]?\s*sorry\b", data, re.I):
        raise ValueError("Compiler emitted a warning, error or proof-hole diagnostic")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: check_clean_log.py LOG")
    try:
        check(Path(sys.argv[1]).read_text())
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
