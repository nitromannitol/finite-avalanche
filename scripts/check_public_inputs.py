#!/usr/bin/env python3
"""Validate current disclosure; historical private evidence is not re-executed here."""
import argparse
import hashlib
import json
from pathlib import Path
import re

PRIMITIVES = {'propext', 'Classical.choice', 'Quot.sound'}
CAPSULE = 'audit/public/'
REGISTRY = 'audit/trusted-inputs.json'
PROJECTION = CAPSULE + 'projection.json'
APPROVAL = CAPSULE + 'release-review.json'
RETIRED = {
    'FiniteAvalanches.External.polya_square_lattice_hits_every_site',
    'FiniteAvalanches.External.wired_srw_firstHit_voltage',
}
ROLES = ('replacement', 'provider', 'consumer')
STATIC_INPUTS = {
    CAPSULE+'README.md', PROJECTION, REGISTRY, CAPSULE+'proved-inputs.json', CAPSULE+'current-statements.json',
    CAPSULE+'source-files.json', CAPSULE+'comparator-supplement.json',
    'scripts/check_public_inputs.py', 'scripts/check_public_axioms.py',
    'scripts/prepare_public_comparators.py', 'scripts/ci_build.sh', 'scripts/run_comparators.sh',
    'scripts/check_clean_log.py', 'scripts/build_comparator_tools.sh',
    'scripts/check_comparator_tools.py', 'scripts/comparator_landrun.py',
    'audit/comparator-tool-pins.json', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain',
    'FiniteAvalanchesAudit/MainOrigin/comparator.json',
    *('FiniteAvalanchesAudit/MainOrigin/'+name+'.lean' for name in ['Challenge','Solution','VerifyChallenge','VerifySolution']),
    *('FiniteAvalanchesAudit/MainOrigin/semantic-data/'+name for name in ['SUMMARY.json','boundary.json',
      'declarations.jsonl','main-type-nodes.jsonl','main-type.json','nodes.jsonl']),
    '.github/workflows/build.yml', '.github/workflows/comparator.yml',
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw): return hashlib.sha256(raw).hexdigest()

def object_digest(value):
    return digest(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode())


def read_json(raw):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique)


def relative_path(value):
    require(isinstance(value, str) and value and '\\' not in value, 'Invalid input path')
    path = Path(value)
    require(not path.is_absolute() and '..' not in path.parts and path.as_posix() == value,
            'Input must be a canonical relative path')
    return path


def regular_input(root, value):
    path = relative_path(value); current = root
    for component in path.parts:
        current = current / component
        require(not current.is_symlink(), 'Input contains a symlink: ' + value)
    require(current.is_file() and current.resolve().is_relative_to(root.resolve()),
            'Missing regular contained input: ' + value)
    return current


def dependency_head(directory):
    gitdir = directory / '.git'
    require(gitdir.is_dir() and not gitdir.is_symlink(), 'Unsupported dependency Git metadata')
    head = regular_input(gitdir, 'HEAD').read_text().strip()
    if head.startswith('ref: '):
        ref = head[5:]
        require(re.fullmatch(r'refs/(heads|tags)/[A-Za-z0-9_./-]+', ref) is not None,
                'Invalid dependency HEAD ref')
        relative_path(ref)
        if (gitdir / ref).exists():
            head = regular_input(gitdir, ref).read_text().strip()
        else:
            rows = [line.split()[0] for line in regular_input(gitdir, 'packed-refs').read_text().splitlines()
                    if re.fullmatch(r'[0-9a-f]{40} ' + re.escape(ref), line)]
            require(len(rows) == 1, 'Missing/ambiguous dependency HEAD ref')
            head = rows[0]
    require(re.fullmatch(r'[0-9a-f]{40}', head) is not None, 'Invalid dependency HEAD')
    return head


def checked_file(root, item, packages=None):
    require(isinstance(item, dict) and {'path', 'sha256'} <= set(item), 'Invalid file pin')
    path = relative_path(item['path'])
    if path.parts[:2] == ('.lake', 'packages'):
        require(packages is not None and len(path.parts) >= 4, 'Unapproved dependency input')
        name = path.parts[2]
        require(name in packages, 'Unapproved dependency package')
        # Only the package root may be a Lake checkout symlink. Inner symlinks are rejected.
        require(not (root/'.lake').is_symlink() and not (root/'.lake/packages').is_symlink(),
                'Dependency parent contains a symlink')
        directory = (root/'.lake/packages'/name).resolve(strict=True)
        require(directory.is_dir() and dependency_head(directory) == packages[name],
                'Dependency HEAD differs from pinned manifest: ' + name)
        source = regular_input(directory, Path(*path.parts[3:]).as_posix())
    else:
        source = regular_input(root, item['path'])
    raw = source.read_bytes()
    require(digest(raw) == item['sha256'], 'File pin mismatch: ' + item['path'])
    if 'complete_file' in item:
        require(isinstance(item['complete_file'], str) and raw == item['complete_file'].encode(),
                'Complete source literal mismatch: ' + item['path'])
    return raw


def load(root, path): return read_json(regular_input(root, path).read_bytes())


def inspect_contents(root):
    """Candidate integrity only. Does not approve a release or historical evidence."""
    root = Path(root)
    projection = load(root, PROJECTION)
    require(projection['schema_version'] == 1 and projection['new_compilation_claim'] is False and
            projection['new_independent_review'] is False and projection['historical_originals_included'] is False,
            'Projection misstates verification scope')
    for key in ['registry', 'proved_inputs', 'current_statements', 'production_sources',
                'dependency_manifest', 'lakefile', 'toolchain', 'axiom_report_source']:
        checked_file(root, projection[key])
    require(projection['registry']['path'] == REGISTRY and
            projection['proved_inputs']['path'] == CAPSULE+'proved-inputs.json' and
            projection['current_statements']['path'] == CAPSULE+'current-statements.json' and
            projection['production_sources']['path'] == CAPSULE+'source-files.json', 'Wrong capsule input role')
    lake = read_json(checked_file(root, projection['dependency_manifest']))
    packages = {p['name'].strip('«»'): p['rev'] for p in lake['packages']}
    require(len(packages) == len(lake['packages']) == 10 and
            projection['packages'] == [{'name':p['name'].strip('«»'), 'rev':p['rev'], 'url':p['url']}
                                      for p in lake['packages']], 'Dependency pin set differs')
    for name, commit in packages.items():
        directory=(root/'.lake/packages'/name).resolve(strict=True)
        require(dependency_head(directory)==commit, 'Dependency HEAD differs: '+name)
    require(packages['lattice-probability'] == '30752e06f26692a2a44bcbf629db9d8d187c5e68' and
            packages['mathlib'] == '81a5d257c8e410db227a6665ed08f64fea08e997', 'Wrong mathematical dependency version')
    require(checked_file(root, projection['toolchain']) == b'leanprover/lean4:v4.32.0\n', 'Wrong Lean version')
    sources = load(root, CAPSULE+'source-files.json')
    require(sources['schema_version'] == 1 and len(sources['production_files']) == 841, 'Wrong production source inventory')
    inventory = {p['path'] for p in sources['production_files']}
    actual = {'FiniteAvalanches.lean'}
    for directory in ['FiniteAvalanches', 'FiniteAvalanchesFrozen', 'FiniteAvalanchesProofs']:
        actual |= {p.relative_to(root).as_posix() for p in (root/directory).rglob('*.lean')}
    require(len(inventory) == 841 and actual == inventory, 'Extra/missing/duplicate production source')
    for item in sources['production_files']: checked_file(root, item)
    registry = load(root, REGISTRY)
    require(registry['schema_version'] == 2 and registry['kind'] == 'CURRENT_STANDARD_INPUT_DISCLOSURE' and
            registry['baseline_registry_sha256'] == projection['baseline_registry_sha256'], 'Wrong disclosure registry')
    require(len(registry['inputs']) == 26, 'Expected exactly 26 registered inputs')
    revision = projection['approved_semantic_revision']
    require(revision['from_lp'] == '2cad808c821285cb20f217717e2ad3ecc16c09fb' and
            revision['to_lp'] == packages['lattice-probability'], 'Wrong recorded semantic transition')
    changes = {(p['owner_id'], p['path']):(p['before'], p['after']) for p in revision['owner_changes']}
    require(len(changes) == len(revision['owner_changes']) == 21 and
            len({owner for owner, _ in changes}) == 20, 'Wrong/duplicate semantic revision mapping')
    for review in revision['projected_independent_reviews']:
        require(review['recorded_independent'] is True and review['recorded_verdict'] == 'PASS' and
                all(review[k] == 'PASS' for k in ['unchanged_frozen_type_body_verdict',
                    'current_semantics_verdict', 'exact_lp_commit_verdict']), 'Invalid projected semantic approval')
    require(revision['projected_independent_reviews'], 'Missing recorded semantic review commitment')
    exports = set(); owners = set(); ids = set(); seen_changes = set(); public_files = set(STATIC_INPUTS)
    for entry in registry['inputs']:
        require(entry['state'] == 'FROZEN_EXTERNAL' and entry['kind'] == 'STANDARD', 'Nonstandard input entry')
        declaration = entry['declaration']; name = declaration['export']; eid = entry['id']
        require(name not in exports and declaration['path'] not in owners and eid not in ids,
                'Duplicate registered export/file/ID')
        require(name not in RETIRED, 'Proved input is in the axiom allowlist')
        code = checked_file(root, declaration).decode()
        require('complete_file' in declaration and declaration['path'] in inventory, 'Incomplete external source pin')
        commands = re.findall(r'^(?:noncomputable\s+)?(?:axiom|def|theorem|lemma|abbrev|instance|structure|class)\s+(\S+)', code, re.M)
        require(commands == [name.rsplit('.',1)[-1]] and
                re.search(r'^axiom '+re.escape(commands[0])+r'\b', code, re.M), 'External file must own its exact one axiom')
        require(entry['sources'] and entry['semantic_files'], 'Missing primary citations or semantic closure')
        def has_locator(value):
            if isinstance(value,dict):
                return any(isinstance(value.get(k),str) and value[k].startswith(('https://','http://'))
                           for k in ['url','doi_url','primary_content_url']) or bool(value.get('doi')) or any(has_locator(v) for v in value.values())
            return isinstance(value,list) and any(has_locator(v) for v in value)
        require(all(has_locator(c) for c in entry['sources']), 'Primary citation lacks a locator')
        require(entry['baseline_semantic_files'] == [{'path':p['path'],'sha256':p['baseline_sha256']} for p in entry['semantic_files']],
                'Current semantic list drops/reorders/adds a baseline dependency')
        paths = set()
        for item in entry['semantic_files']:
            require(item['path'] not in paths and 'complete_file' in item, 'Duplicate/incomplete semantic source')
            paths.add(item['path']); checked_file(root, item, packages)
            if not item['path'].startswith('.lake/packages/') and item['path'] not in inventory:
                public_files.add(item['path'])
            key = (eid,item['path'])
            if item['revision'] == 1:
                require(key in changes and changes[key] == (item['baseline_sha256'],item['sha256']),
                        'Unapproved current semantic pin substitution'); seen_changes.add(key)
            else:
                require(item['revision'] == 0 and item['baseline_sha256'] == item['sha256'] and key not in changes,
                        'Silent semantic revision')
        att = read_json(checked_file(root, entry['review_attestation']))
        public_files.add(entry['review_attestation']['path'])
        require(att['kind'] == 'PROJECTION_OF_EXISTING_INDEPENDENT_REVIEW_METADATA' and
                att['new_independent_review'] is False and att['original_reports_included'] is False and
                att['subject_id'] == eid and att['baseline_row_sha256'] == entry['baseline_row_sha256'] and
                att['declaration_sha256'] == declaration['sha256'] and
                att['current_semantics_sha256'] == object_digest(entry['semantic_files']), 'Review projection subject differs')
        require(att['original_reviews'] and all(r['recorded_verdict'] == 'PASS' and
                r['recorded_independent'] is True and re.fullmatch('[0-9a-f]{64}',r['original_sha256'])
                for r in att['original_reviews']), 'Missing independent original-review commitment')
        exports.add(name); owners.add(declaration['path']); ids.add(eid)
    require(seen_changes == set(changes), 'Lost semantic dependency revision')
    proved = load(root, CAPSULE+'proved-inputs.json'); primitive_only = set()
    require(proved['schema_version'] == 1 and len(proved['successors']) == 2, 'Wrong proved-input set')
    replacements = set()
    for entry in proved['successors']:
        replacement = entry['replacement']; replacements.add(replacement['export'])
        require(entry['state'] == 'PROVED_CURRENT_THEOREM' and replacement['export'] == entry['predecessor_export'],
                'Wrong proved current identity')
        code = checked_file(root, replacement); exact = checked_file(root, entry['exact_type'])
        public_files.add(entry['exact_type']['path']); begin,end = entry['replacement_signature_span']
        leaf = replacement['export'].rsplit('.',1)[-1]
        require(type(begin) is int and type(end) is int and 0 <= begin < end <= len(code) and
                re.search(rb'(?m)^theorem '+re.escape(leaf.encode())+rb'\Z', code[:begin]) and
                code[begin:end] == exact and code[end:].lstrip().startswith(b':='), 'Proved complete signature changed')
        for role in ROLES:
            checked_file(root, entry[role]); primitive_only.add(entry[role]['export'])
        for item in entry['semantic_files']: checked_file(root, item, packages)
        require(entry['projected_independent_reviews'] and all(r['recorded_independent'] is True and
                r['recorded_verdict'] == 'PASS' and all(r[k] == 'PASS' for k in [
                    'literal_type_verdict','definition_closure_verdict','term_consumption_verdict',
                    'provider_no_predecessor_verdict']) for r in entry['projected_independent_reviews']),
                'Missing projected proved-input review')
    require(replacements == RETIRED and len(primitive_only) == 6 and not (primitive_only & exports),
            'Proved inputs added to trust boundary or omitted')
    correspondence = load(root, CAPSULE+'current-statements.json')
    paper = checked_file(root, correspondence['paper']).decode(); public_files.add(correspondence['paper']['path'])
    lines = paper.splitlines(keepends=True); labels=set(); anchors=set()
    require(len(correspondence['statements']) == 16, 'Wrong current statement count')
    for statement in correspondence['statements']:
        require(statement['label'] not in labels, 'Duplicate source label'); labels.add(statement['label'])
        a,b = statement['first_line'],statement['last_line']; require(0 < a <= b <= len(lines), 'Invalid source range')
        exact=''.join(lines[a-1:b]).rstrip('\n')
        require(exact == statement['exact_statement'] and digest(exact.encode()) == statement['statement_sha256'],
                'Current manuscript statement changed')
        checked_file(root,statement['anchor']); anchors.add(statement['anchor']['export'])
    require(len(anchors) == 15, 'Wrong current anchor count')
    request_raw=checked_file(root, projection['axiom_report_source']).decode()
    requests=re.findall(r'^#print axioms (.+)$',request_raw,re.M)
    require(len(requests) == len(set(requests)) == projection['expected_direct_reports'] == 4737 and
            primitive_only <= set(requests) and anchors <= set(requests), 'Direct audit source omits required exports')
    return {'registered':exports, 'primitive_only':primitive_only, 'requests':set(requests),
            'approval_files':public_files, 'projection':projection}


def require_approval(root, contents):
    approval = load(root, APPROVAL)
    require(approval.get('schema_version') == 1 and approval.get('verdict') == 'PASS' and
            approval.get('independent') is True and
            approval.get('approval_scope') == 'PUBLIC_PROJECTION_AND_GATE_IMPLEMENTATION' and
            approval.get('new_proof_or_compilation_claim') is False, 'Public projection is not independently approved')
    entries = approval.get('bindings',[])
    require(len(entries) == len(contents['approval_files']) and
            {p['path'] for p in entries} == contents['approval_files'], 'Public review omits/adds/repeats a required binding')
    for item in entries: checked_file(root,item)
    report = approval['report']
    require(report['path'].startswith(CAPSULE) and checked_file(root,report).strip(), 'Missing public independent review report')
    return contents


def registered_inputs(root: Path) -> set[str]:
    """Public runtime API: exact current26, only after separate projection approval."""
    return require_approval(root, inspect_contents(root))['registered']


def check_reports(root, raw):
    contents = require_approval(root,inspect_contents(root))
    text=raw.decode()
    require(not re.search(r"warning:|\berror(?:\([^)]*\))?:|sorryAx|declaration uses\s+['`\"]?\s*sorry\b",text,re.I),
            'Audit contains an error, warning, or proof hole')
    seen=set(); allowed=PRIMITIVES | contents['registered']
    for match in re.finditer(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",text,re.M):
        name,body=match.group(1),match.group(2) or ''
        require(name in contents['requests'] and name not in seen, 'Unexpected/duplicate direct report: '+name)
        axioms={a.strip() for a in body.split(',') if a.strip()}
        require(axioms <= (PRIMITIVES if name in contents['primitive_only'] else allowed),
                'Unauthorized axiom or nonprimitive proved successor: '+name)
        seen.add(name)
    require(seen == contents['requests'], 'Missing direct axiom reports')
    return len(seen)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    args=parser.parse_args()
    try:
        names=registered_inputs(args.root)
        print(f'Current disclosure verified: {len(names)} registered external inputs; private history not re-executed. No build or comparator result asserted.')
    except (ValueError,KeyError,TypeError,OSError) as error:
        raise SystemExit('Invalid public disclosure: '+str(error)) from error
