#!/usr/bin/env python3
"""Bind actual tool binaries to the freshly produced pinned-tool receipt."""
import hashlib
import json
import os
from pathlib import Path
import sys

def regular_contained(root, relative):
    path=root
    for component in Path(relative).parts:
        path=path/component
        if path.is_symlink():
            raise ValueError('Symlink in comparator launcher path')
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError('Missing regular contained comparator launcher')
    return path

def check(root, tools):
    pins=json.loads((root/'audit/comparator-tool-pins.json').read_text())
    receipt=json.loads((tools/'tool-receipt.json').read_text())
    if receipt.get('build_complete') is not True or receipt.get('lean_toolchain')!=pins['lean_toolchain']:
        raise ValueError('Incomplete or incompatible comparator tool build')
    if receipt.get('sources')!=pins['tools']:
        raise ValueError('Comparator tool revisions differ from pinned sources')
    expected={'comparator':'comparator/.lake/build/bin/comparator',
              'lean4export':'lean4export/.lake/build/bin/lean4export',
              'landrun':'bin/landrun','nanoda':'nanoda/target/release/nanoda_bin'}
    if set(receipt.get('binaries',{}))!=set(expected):
        raise ValueError('Missing comparator tool binary record')
    for name, relative in expected.items():
        path=tools/relative
        entry=receipt['binaries'][name]
        if entry.get('path')!=str(path) or not path.is_file():
            raise ValueError('Unexpected comparator tool path: '+name)
        if hashlib.sha256(path.read_bytes()).hexdigest()!=entry.get('sha256'):
            raise ValueError('Comparator binary differs from build receipt: '+name)

    adapters=receipt.get('adapters')
    if not isinstance(adapters,dict) or set(adapters)!={'landrun_cli'}:
        raise ValueError('Missing exact reviewed Landrun CLI adapter receipt')
    entry=adapters['landrun_cli']
    if not isinstance(entry,dict) or set(entry)!={'source','source_sha256','path','sha256'}:
        raise ValueError('Invalid Landrun CLI adapter receipt')
    source=regular_contained(root,'scripts/comparator_landrun.py')
    adapter=regular_contained(tools,'bin/comparator-landrun')
    if entry['source']!='scripts/comparator_landrun.py' or entry['path']!=str(adapter):
        raise ValueError('Unexpected Landrun CLI adapter path')
    source_hash=hashlib.sha256(source.read_bytes()).hexdigest()
    adapter_hash=hashlib.sha256(adapter.read_bytes()).hexdigest()
    if source_hash!=entry['source_sha256'] or adapter_hash!=entry['sha256'] or source_hash!=adapter_hash:
        raise ValueError('Landrun CLI adapter differs from reviewed source or receipt')
    if not os.access(adapter,os.X_OK):
        raise ValueError('Landrun CLI adapter is not executable')

if __name__=='__main__':
    try:
        if len(sys.argv)!=2: raise ValueError('Usage: check_comparator_tools.py ABSOLUTE_TOOLS_DIRECTORY')
        tools=Path(sys.argv[1])
        if not tools.is_absolute() or '..' in tools.parts: raise ValueError('Tools path must be absolute without ..')
        check(Path(__file__).resolve().parents[1],tools)
        print('Pinned comparator tool sources, binaries and launcher receipts match.')
    except (ValueError,KeyError,TypeError,OSError) as error:
        raise SystemExit(str(error)) from error
