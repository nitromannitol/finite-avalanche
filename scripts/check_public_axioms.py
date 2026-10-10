#!/usr/bin/env python3
"""Check fresh direct public reports, including primitive-only proved replacements."""
from pathlib import Path
import sys
from check_public_inputs import check_reports

if __name__ == '__main__':
    try:
        count=check_reports(Path(__file__).resolve().parents[1],Path(sys.argv[1]).read_bytes())
        print(f'All {count} fresh direct reports pass: exact26 standard inputs and six primitive-only replacement/provider/consumer exports. No historical receipt or comparator result asserted.')
    except (ValueError,KeyError,TypeError,OSError,IndexError) as error:
        raise SystemExit('Invalid public axiom boundary: '+str(error)) from error
