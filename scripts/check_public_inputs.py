#!/usr/bin/env python3
"""Check this source projection and its disclosed external assumptions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

PRIMITIVES = {'propext', 'Classical.choice', 'Quot.sound'}
MAIN = 'FiniteAvalanchesCurrent.RegisteredPast.Main.finite_avalanches_origin'
# These two assertion types refer to the canonical UST probability law, whose
# definition uses the registered weak-limit existence theorem.
ASSERTION_TYPE_INPUTS = {
    'FiniteAvalanches.External.BarlowMasson2011.adjacent_ust_path_euclidean_tail': {
        'FiniteAvalanches.External.square_lattice_wired_ust_weak_limit'},
    'FiniteAvalanches.External.square_lattice_ray_seeded_wilson': {
        'FiniteAvalanches.External.square_lattice_wired_ust_weak_limit'},
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def regular(root, value):
    require(isinstance(value, str) and value and '\\' not in value, 'Invalid path')
    path = Path(value)
    require(not path.is_absolute() and '..' not in path.parts and path.as_posix() == value,
            'Expected canonical relative path')
    current = root
    for part in path.parts:
        current = current / part
        require(not current.is_symlink(), 'Symlink in source input: ' + value)
    require(current.is_file(), 'Missing source input: ' + value)
    return current


def read_json(path):
    def unique(pairs):
        result = {}
        for k, v in pairs:
            require(k not in result, 'Duplicate JSON key: ' + k)
            result[k] = v
        return result
    return json.loads(path.read_text(), object_pairs_hook=unique)


def checked(root, entry):
    raw = regular(root, entry['path']).read_bytes()
    require(digest(raw) == entry['sha256'], 'Source hash mismatch: ' + entry['path'])
    return raw


def inspect_contents(root, dependencies=False):
    root = root.resolve()
    inventory = read_json(regular(root, 'audit/source-inventory.json'))
    require(inventory['schema_version'] == 1 and inventory['main_export'] == MAIN, 'Wrong source inventory')
    entries = inventory['production_files']
    paths = {e['path'] for e in entries}
    require(len(paths) == len(entries) and all(p.endswith('.lean') for p in paths), 'Duplicate/invalid production file')
    # Comparator sources have a separate deliberate challenge hole and review gate.
    actual = set()
    for directory, dirs, files in os.walk(root,followlinks=False):
        dirs[:] = [d for d in dirs if d not in {'.git','.lake','FiniteAvalanchesAudit'}]
        for file in files:
            if file.endswith('.lean') and file != 'lakefile.lean':
                actual.add((Path(directory)/file).relative_to(root).as_posix())
    require(actual == paths, 'Uninventoried/missing production Lean file')
    for entry in entries:
        raw = checked(root, entry)
        require(digest(residue(raw.decode()).encode()) == entry['code_sha256'], 'Changed code residue')
        code = residue(raw.decode())
        require(not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|maxHeartbeats)\b', code),
                'Forbidden proof escape: ' + entry['path'])
    config_pins = inventory['verification_files']
    required_config = {'audit/trusted-inputs.json','audit/current-statements.json',
       'lakefile.lean','lake-manifest.json','lean-toolchain','scripts/check_public_inputs.py',
       'scripts/check_public_axioms.py','scripts/lean_text.py','scripts/ci_build.sh',
       'scripts/prepare_public_comparators.py','scripts/run_comparators.sh',
       'scripts/check_clean_log.py','scripts/lint_public.py','scripts/build_comparator_tools.sh',
       'scripts/check_comparator_tools.py','scripts/comparator_landrun.py',
       'audit/comparator-tool-pins.json','.github/workflows/build.yml','.github/workflows/comparator.yml'}
    require(len(config_pins) == len(required_config) and {e['path'] for e in config_pins} == required_config,
            'Verification/configuration pin coverage differs')
    for e in config_pins:
        checked(root,e)
    registry = read_json(regular(root, 'audit/trusted-inputs.json'))
    require(registry['schema_version'] == 3 and registry['kind'] == 'STANDARD_EXTERNAL_ASSUMPTIONS', 'Wrong registry schema')
    require(len(registry['inputs']) == 25, 'Expected exact25 registered declarations')
    names = set()
    owners = set()
    ids = set()
    used = set()
    for e in registry['inputs']:
        d = e['declaration']
        name = d['export']
        require(name not in names and d['path'] not in owners and e['id'] not in ids, 'Duplicate external ownership')
        require(e['state'] == 'EXTERNAL_ASSUMPTION' and e['kind'] == 'STANDARD', 'External input misclassified')
        raw = checked(root, d)
        require(raw == d['complete_file'].encode() and d['path'] in paths, 'Incomplete external source pin')
        require(digest(residue(raw.decode()).encode()) == d['code_sha256'], 'External code pin differs')
        leaf = name.rsplit('.', 1)[-1]
        commands = re.findall(r'^\s*(?:noncomputable\s+)?(axiom|constant|def|theorem|lemma|abbrev|structure|class)\s+(\S+)', residue(raw.decode()), re.M)
        require(commands == [('axiom', leaf)], 'Input must own its one exact registered axiom')
        namespaces = re.findall(r'^\s*namespace\s+(\S+)\s*$',residue(raw.decode()),re.M)
        require(len(namespaces) == 1 and namespaces[0]+'.'+leaf == name, 'External fully qualified identity differs')
        require(e['sources'] and e['semantic_files'], 'Missing source citations or meaning pins')
        if e['used_by_main'] is True:
            used.add(name)
        else:
            require(e['used_by_main'] is False, 'Main-use flag must be boolean')
        for s in e['semantic_files']:
            if s['path'].startswith('.lake/packages/'):
                if dependencies:
                    # Lake package roots may be checkout links; inner source links may not.
                    parts = Path(s['path']).parts
                    package = root.joinpath(*parts[:3]).resolve(strict=True)
                    raw_semantic = regular(package, Path(*parts[3:]).as_posix()).read_bytes()
                    require(digest(raw_semantic) == s['sha256'], 'Dependency meaning hash mismatch: ' + s['path'])
            else:
                require(s['path'] in paths or (s.get('role') == 'dependency_configuration' and
                        s['path'] in {'lakefile.lean', 'lake-manifest.json', 'lean-toolchain'}),
                        'Meaning source outside production closure')
                checked(root, s)
        names.add(name)
        owners.add(d['path'])
        ids.add(e['id'])
    require(names == set(inventory['registered_external_inputs']), 'Registered identity set differs')
    require(len(used) == 22 and used == set(inventory['main_external_inputs']), 'Expected exact22 Main inputs')
    # Count actual declarations, not strings in doc comments or registry summaries.
    actual_axiom_owners = {e['path'] for e in entries if re.search(r'^\s*(?:axiom|constant)\s+', residue(regular(root,e['path']).read_text()), re.M)}
    require(actual_axiom_owners == owners, 'Unlisted production axiom/constant')
    request = checked(root, {'path': inventory['axiom_query'], 'sha256': next(e['sha256'] for e in entries if e['path'] == inventory['axiom_query'])}).decode()
    queries = re.findall(r'^#print axioms (.+)$', request, re.M)
    require(len(queries) == len(set(queries)) and set(queries) == set(inventory['axiom_requests']), 'Axiom request set differs')
    statements = read_json(regular(root, 'audit/current-statements.json'))
    require(len(statements['statements']) == 17 and len({e['label'] for e in statements['statements']}) == 17, 'Expected exact17 source labels')
    require(all(e['export'] in queries and e['declaration_path'] in paths for e in statements['statements']), 'Statement omitted from replay')
    require(MAIN in queries and names <= set(queries), 'Main or external declaration omitted from replay')
    primitive_only = set(inventory['primitive_only_exports'])
    require(len(primitive_only) == 7 and primitive_only <= set(queries) and not primitive_only & names,
            'Proved replacements/providers/consumers must be separate from assumptions')
    manifest = read_json(regular(root, 'lake-manifest.json'))
    packages = {p['name'].strip('«»'): p['rev'] for p in manifest['packages']}
    require(packages['lattice-probability'] == '8557b91360e23d51d779a05d8313974b403658b2' and
            packages['mathlib'] == '81a5d257c8e410db227a6665ed08f64fea08e997', 'Dependency revision differs')
    require(regular(root,'lean-toolchain').read_bytes() == b'leanprover/lean4:v4.32.0\n', 'Toolchain differs')
    require('8557b91360e23d51d779a05d8313974b403658b2' in regular(root,'lakefile.lean').read_text(), 'Lakefile dependency differs')
    if dependencies:
        for name, rev in packages.items():
            directory = root / '.lake/packages' / name
            actual_head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
            require(actual_head == rev, 'Dependency HEAD differs: ' + name)
    return {'registered': names, 'main_inputs': used, 'requests': set(queries), 'inventory': inventory,
            'primitive_only':primitive_only}


def residue(text):
    # Kept in the payload as a standalone scanner; no development imports.
    from lean_text import residue as scan
    return scan(text)


def require_reviewed(root):
    record = read_json(regular(root, 'audit/release-eligibility.json'))
    require(record['schema_version'] == 1 and record['status'] == 'REVIEWED_SOURCE_ELIGIBLE', 'Final current-source release eligibility is PENDING')
    require(record['candidate_source_inventory_sha256'] == digest(regular(root,'audit/source-inventory.json').read_bytes()), 'Review binds another source inventory')
    required = {'final_statement_and_proof_review', 'final_source_meaning_and_input_review', 'projection_independent_review'}
    for key in required:
        r = record[key]
        require(isinstance(r,dict) and r.get('verdict') == 'PASS' and r.get('independent') is True and
                isinstance(r.get('reviewer'), str) and r['reviewer'] and
                re.fullmatch(r'[0-9a-f]{64}', r.get('evidence_sha256','')),
                'Missing independent exact-subject review: ' + key)
    require(record['final_source_meaning_and_input_review'].get('registered_inputs') == 25 and
            record['final_source_meaning_and_input_review'].get('main_inputs') == 22,
            'Review does not cover current25/22 boundary')


def registered_inputs(root):
    contents = inspect_contents(root, dependencies=True)
    require_reviewed(root)
    return contents['registered']


def check_reports(root, raw):
    contents = inspect_contents(root, dependencies=True)
    require_reviewed(root)
    return parse_reports(contents,raw)


def parse_reports(contents, raw):
    """Parse actual direct reports; caller supplies an already checked inventory."""
    text = raw.decode()
    require(not re.search(r'warning(?:\([^)]*\))?:|\berror(?:\([^)]*\))?:|sorryAx', text, re.I), 'Axiom replay contains diagnostic/hole')
    seen = set()
    allowed = PRIMITIVES | contents['registered']
    for match in re.finditer(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$", text, re.M):
        name, body = match.group(1), match.group(2) or ''
        # Lean may print universe parameters after the exact declaration name.
        name = re.sub(r'\.\{[^}]*\}$', '', name)
        require(name in contents['requests'] and name not in seen, 'Unexpected/duplicate axiom report: ' + name)
        axioms = {x.strip() for x in body.split(',') if x.strip()}
        require(axioms <= allowed, 'Unlisted axiom: ' + name)
        if name in contents['primitive_only']:
            require(axioms <= PRIMITIVES, 'Former input proof depends on a nonprimitive axiom: ' + name)
        if name == MAIN:
            require(axioms - PRIMITIVES == contents['main_inputs'], 'Main does not use exact22 named assumptions')
        if name in contents['registered']:
            expected = {name} | ASSERTION_TYPE_INPUTS.get(name, set())
            require(axioms - PRIMITIVES == expected,
                    'Registered assertion/type dependency closure differs: ' + name)
        seen.add(name)
    require(seen == contents['requests'], 'Missing direct axiom reports')
    return len(seen)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--static', action='store_true', help='Inventory only; does not approve source or claim a build')
    args = p.parse_args()
    try:
        contents = inspect_contents(args.root, dependencies=not args.static)
        if not args.static:
            require_reviewed(args.root)
        print('STATIC INVENTORY ONLY' if args.static else 'REVIEWED SOURCE INVENTORY')
        print('25 registered external ASSUMPTIONS; exact22 selected Main inputs. No build/comparator result asserted.')
    except (ValueError, KeyError, TypeError, OSError, StopIteration, subprocess.CalledProcessError) as error:
        raise SystemExit('Invalid current release disclosure: ' + str(error)) from error
