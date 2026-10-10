#!/usr/bin/env python3
"""Fail closed unless the required genuine main challenge/solution is present."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import re

# Public projection supplement; original private pair approval is a hash commitment only.
ROOT = Path(__file__).resolve().parents[1]
REQUIRED = {'MainOrigin'}
SEMANTIC_FILES = tuple('FiniteAvalanchesAudit/MainOrigin/semantic-data/' + name for name in (
    'SUMMARY.json', 'boundary.json', 'declarations.jsonl',
    'main-type-nodes.jsonl', 'main-type.json', 'nodes.jsonl'))


def regular_input(root, relative):
    if not isinstance(relative, str) or not relative or '\\' in relative:
        raise ValueError('Invalid comparator input path')
    path = Path(relative)
    if path.is_absolute() or '..' in path.parts or path.as_posix() != relative:
        raise ValueError('Comparator input must be a canonical in-repository path')
    current = root
    for component in path.parts:
        current = current / component
        if current.is_symlink():
            raise ValueError('Comparator input contains a symlink: ' + relative)
    if not current.is_file() or not current.resolve().is_relative_to(root.resolve()):
        raise ValueError('Missing regular contained comparator input: ' + relative)
    return current


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_semantic_files(root, review):
    entries = review.get('semantic_files')
    if not isinstance(entries, list) or len(entries) != len(SEMANTIC_FILES):
        raise ValueError('Independent review must pin all six semantic payload files')
    paths = []
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {'path', 'sha256', 'bytes'}:
            raise ValueError('Invalid semantic payload review entry')
        if type(entry['bytes']) is not int or entry['bytes'] < 0:
            raise ValueError('Invalid semantic payload byte count')
        paths.append(entry['path'])
        if entry['path'] not in SEMANTIC_FILES:
            raise ValueError('Unexpected semantic payload path')
        source = regular_input(root, entry['path'])
        if source.stat().st_size != entry['bytes'] or digest(source) != entry['sha256']:
            raise ValueError('Semantic payload differs from independent review: ' + entry['path'])
    if len(set(paths)) != len(SEMANTIC_FILES) or set(paths) != set(SEMANTIC_FILES):
        raise ValueError('Missing or duplicated semantic payload path')
    directory = root / 'FiniteAvalanchesAudit/MainOrigin/semantic-data'
    if {p.name for p in directory.iterdir()} != {Path(p).name for p in SEMANTIC_FILES}:
        raise ValueError('Semantic payload directory must contain exactly the reviewed six files')


def read(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result: raise ValueError('Duplicate configuration key: '+key)
            result[key] = value
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique)

def prepare(root, destination=None):
    audit = root/'FiniteAvalanchesAudit'
    paths = sorted(audit.rglob('comparator.json'))
    if len(paths)!=1 or REQUIRED != {p.parent.name for p in paths}:
        raise ValueError('Missing or unexpected comparator pairs; required: MainOrigin')
    reviews=read(regular_input(root, 'audit/public/comparator-supplement.json'))
    if reviews.get('schema_version')!=1 or reviews.get('version')!=1 or len(reviews.get('pairs',[]))!=1:
        raise ValueError('Missing independent full main comparator review')
    review=reviews['pairs'][0]
    if review.get('pair')!='MainOrigin' or review.get('pair_source_review')!='PROJECTED_EXISTING_INDEPENDENT_PASS' or review.get('new_independent_review') is not False:
        raise ValueError('Main comparator pair is not independently approved')
    spec=importlib.util.spec_from_file_location('release_trusted_checker',regular_input(root, 'scripts/check_public_inputs.py'))
    checker=importlib.util.module_from_spec(spec); spec.loader.exec_module(checker)
    trusted=set(checker.registered_inputs(root))
    if len(trusted)!=26: raise ValueError('Expected exact reviewed26-input registry')
    registry=regular_input(root, 'audit/trusted-inputs.json')
    if digest(registry)!=review.get('trusted_input_registry_sha256'):
        raise ValueError('Trusted-input registry differs from independent comparator review')
    projection=regular_input(root, 'audit/public/projection.json')
    if digest(projection)!=review.get('public_projection_sha256'):
        raise ValueError('Public registry view differs from its versioned comparator supplement')
    projected=read(projection)
    if projected['baseline_registry_sha256']!=review.get('baseline_trusted_input_registry_sha256'):
        raise ValueError('Comparator supplement baseline registry commitment differs')
    current_registry=read(registry)
    identity=[{'id':e['id'],'declaration':e['declaration'],'semantic_files':[{k:p[k] for k in ['path','sha256','complete_file']} for p in e['semantic_files']]} for e in current_registry['inputs']]
    current_identity=hashlib.sha256(json.dumps(identity,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
    if current_identity!=reviews.get('current_semantic_identity_sha256'):
        raise ValueError('Public registry current semantic identity differs from comparator supplement')
    check_semantic_files(root, review)
    allowed={'propext','Classical.choice','Quot.sound'} | trusted
    # The registry/inventory is independently pinned by the ordinary package gate.
    rows=[]
    for index, path in enumerate(paths):
        config=read(regular_input(root, str(path.relative_to(root))))
        if set(config)!={'challenge_module','solution_module','theorem_names','definition_names','permitted_axioms','enable_nanoda'}:
            raise ValueError('Unsupported or missing comparator configuration field')
        if config['definition_names'] != []: raise ValueError('No extra definition targets are approved')
        if config['enable_nanoda'] is not True: raise ValueError('NanoDa replay is mandatory')
        axioms=config['permitted_axioms']
        if not isinstance(axioms,list) or len(axioms)!=len(allowed) or set(axioms)!=allowed:
            raise ValueError('Comparator must disclose exactly primitives plus the26 registered inputs')
        if config['theorem_names'] != ['FiniteAvalanchesAudit.MainOrigin.finite_avalanches_origin']:
            raise ValueError('Comparator does not select the full main theorem')
        for key, expected in (('challenge_module','FiniteAvalanchesAudit.MainOrigin.Challenge'),
                              ('solution_module','FiniteAvalanchesAudit.MainOrigin.Solution')):
            module=config[key]
            if module!=expected:
                raise ValueError('Invalid comparator module')
            source=regular_input(root, '/'.join(module.split('.')) + '.lean')
            if digest(source)!=review.get(key+'_sha256'):
                raise ValueError('Comparator source differs from independent review: '+module)
            if key=='challenge_module':
                # A trusted independent reviewer still audits complete bodies and source fidelity.
                text=source.read_text()
                imported=re.findall(r'^\s*import\s+([^\n]+)',text,re.M)
                if imported != ['Mathlib']: raise ValueError('Challenge must import Mathlib only')
                if re.search(r'\bprivate\b',text): raise ValueError('Private challenge names break closure matching')
        for key, relative in (('target_sha256','FiniteAvalanchesFrozen/MainOriginV3.lean'),
                              ('configuration_sha256',str(path.relative_to(root)))):
            if digest(regular_input(root, relative))!=review.get(key):
                raise ValueError('Comparator target or configuration differs from independent review')
        # New public projection approval is required by registered_inputs above.
        # Private original report hashes are disclosed commitments, not readable evidence here.
        if destination:
            output=destination/f'{index:03d}.json'
            output.write_text(json.dumps(config,indent=2)+'\n')
            rows.append((str(path.relative_to(root)),str(output)))
    if destination:
        (destination/'pairs.tsv').write_text(''.join(a+'\t'+b+'\n' for a,b in rows))
    return len(paths)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    if args.check == bool(args.output): parser.error('Select --check or --output DIRECTORY')
    try:
        if args.output: args.output.mkdir(exist_ok=False)
        count=prepare(ROOT,args.output)
        print(f'Validated {count} required comparator pair, with explicit26-input boundary.')
    except (ValueError,KeyError,TypeError,OSError) as error:
        raise SystemExit(str(error)) from error
