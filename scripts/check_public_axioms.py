#!/usr/bin/env python3
"""Validate fresh direct axiom reports from the current public source tree."""
from pathlib import Path
import sys
from check_public_inputs import check_reports

if __name__ == '__main__':
    try:
        count = check_reports(Path(__file__).resolve().parents[1], Path(sys.argv[1]).read_bytes())
        print(f'{count} actual direct reports accepted; Main uses only propext, Classical.choice and Quot.sound.')
    except (ValueError, KeyError, TypeError, OSError, IndexError) as error:
        raise SystemExit('Invalid actual axiom replay: ' + str(error)) from error
