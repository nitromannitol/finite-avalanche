#!/usr/bin/env python3
"""Reject private filesystem/repository references in the public projection."""
import argparse
import os
from pathlib import Path
import re

# Assemble sensitive spellings so this lint source passes its own content rule.
PATTERN = re.compile('|'.join([
    re.escape('/' + 'home/'), re.escape('/' + 'Users/'), re.escape('/' + 'tmp/'),
    re.escape('finite-' + 'avalanche-workflow'), re.escape('finite-' + 'avalanches-lean'),
    re.escape('github-' + 'paper-watch'), re.escape('incoming-' + 'source'),
    r'(?:agents|haiku)/[^\s"\x27]+', r'job-\d{4}',
    re.escape('OWNED-' + 'OBJECTS.json'), re.escape('TEAM-' + 'HANDOFF.json'),
    re.escape('AUTHOR-STATEMENT-' + 'FREEZE.json'),
    re.escape('nitromannitol/' + 'finite-avalanches/'),
    re.escape('/dev/' + 'shm/'),
    re.escape('private-paper-' + 'update'), re.escape('statement-' + 'audit'),
    re.escape('references-' + 'txt'), re.escape('perc-' + 'upstream'),
    re.escape('percolation-after-' + 'anthropic'),
]), re.I)


def lint(root):
    findings = []
    paths = []
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in {'.git','.lake'})
        base = Path(directory)
        for d in list(dirs):
            if (base/d).is_symlink():
                paths.append(base/d)
                dirs.remove(d)
        paths.extend(base/f for f in sorted(files))
    for path in paths:
        relative = path.relative_to(root)
        if path.is_symlink():
            findings.append({'path': str(relative), 'reason': 'symlink'})
        elif path.is_file():
            try:
                text = path.read_text()
            except UnicodeDecodeError:
                findings.append({'path': str(relative), 'reason': 'nontext artifact'})
                continue
            for line, value in enumerate(text.splitlines(), 1):
                if PATTERN.search(value):
                    findings.append({'path': str(relative), 'line': line, 'reason': 'private reference'})
    return findings


if __name__ == '__main__':
    import json
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('root', type=Path)
    args = p.parse_args()
    findings = lint(args.root)
    print(json.dumps({'forbidden_reference_findings': findings, 'verdict': 'FAIL' if findings else 'PASS'}))
    raise SystemExit(bool(findings))
