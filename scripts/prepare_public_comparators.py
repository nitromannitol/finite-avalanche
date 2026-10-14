#!/usr/bin/env python3
"""Require an independently reviewed current all-integer Main comparator pair."""
import argparse
import hashlib
import json
from pathlib import Path
import re
from check_public_inputs import PRIMITIVES, MAIN, inspect_contents, require_reviewed, regular, read_json

ROOT = Path(__file__).resolve().parents[1]
SEMANTIC_FILES = {'FiniteAvalanchesAudit/MainOrigin/semantic-data/' + n for n in
    ['SUMMARY.json','boundary.json','declarations.jsonl','main-type-nodes.jsonl','main-type.json','nodes.jsonl']}


def name(value):
    if value == ['anonymous']:
        return ''
    require(isinstance(value,list) and len(value) == 3 and value[0] in {'str','num'}, 'Invalid literal Lean Name')
    parent = name(value[1])
    return (parent+'.' if parent else '')+str(value[2])


def require(ok, message):
    if not ok:
        raise ValueError(message)


def command_tokens(code):
    """Mask ordinary quoted data while preserving code and line boundaries.

    The reviewed literal decoder uses JSON kind/field strings such as
    "axiom" and "constant". These are data, not Lean trust declarations.
    Keep the existing conservative bans on every unquoted shortcut token.
    """
    result = list(code)
    i = 0
    while i < len(code):
        if code[i] != '"':
            i += 1
            continue
        first = i
        i += 1
        while i < len(code):
            if code[i] == '\\':
                i += 2
            elif code[i] == '"':
                i += 1
                break
            else:
                i += 1
        else:
            raise ValueError('Unterminated quoted data in comparator source')
        for j in range(first, min(i, len(code))):
            result[j] = '\n' if code[j] == '\n' else ' '
    return ''.join(result)


def source_tokens(text):
    # The inherited comment scanner does not classify these quote forms.
    # Refuse them before scanning; do not hide executable interpolation holes.
    require(not re.search(r"'\\?\"'|\br#*\"|«", text),
            'Unsupported quote literal in reviewed comparator source')
    require(not re.search(r'!\s*(?:/-|--)', text),
            'Unsupported comment between interpolation prefix and quote')
    # Only identifier/field interpolations occur in the reviewed pair. Check
    # them before comment scanning; nested quote expressions can desynchronize
    # the inherited scanner and conceal executable tokens on the same line.
    for match in re.finditer(r'!\s*"', text):
        i = match.end()
        while i < len(text) and text[i] != '"':
            if text[i] == '\\':
                i += 2
            elif text[i] == '{':
                end = text.find('}', i + 1)
                require(end >= 0 and re.fullmatch(r'[A-Za-z0-9_.]*', text[i+1:end]) is not None,
                        'Unsupported executable interpolation in reviewed comparator source')
                i = end + 1
            else:
                i += 1
        require(i < len(text), 'Unterminated interpolated data')
    from lean_text import residue
    code = residue(text)
    return code, command_tokens(code)


def prepare(root, destination=None):
    contents = inspect_contents(root, dependencies=True)
    require_reviewed(root)
    pair = root / 'FiniteAvalanchesAudit/MainOrigin'
    review = read_json(regular(root, 'audit/comparator-review.json'))
    require(review.get('status') == 'REVIEWED_CURRENT_PAIR' and review.get('independent') is True and
            review.get('target_export') == MAIN, 'Current comparator pair review is PENDING')
    require(review.get('producer_role') == 'finite-wilson' and isinstance(review.get('reviewer_role'),str) and
            review['reviewer_role'] and review['reviewer_role'] != review['producer_role'],
            'Missing producer-independent comparator review')
    require(all(review.get(k) is True for k in ['whole_integer_carrier','joint_constants_before_all_real_scales',
             'source_characterizations_checked','exact_type_and_bodies_checked']), 'Incomplete exact statement/definition review')
    require(review.get('source_inventory_sha256') == hashlib.sha256(regular(root,'audit/source-inventory.json').read_bytes()).hexdigest(),
            'Comparator review binds another source tree')
    bindings = review['bindings']
    names = {e['path'] for e in bindings}
    required = {'FiniteAvalanchesAudit/MainOrigin/' + n for n in
                ['Challenge.lean','Solution.lean','VerifyChallenge.lean','VerifySolution.lean','comparator.json']} | SEMANTIC_FILES
    require(required <= names and len(names) == len(bindings), 'Incomplete/duplicate pair binding')
    # Every shipped comparator artifact needs a binding, including semantic data.
    actual = {p.relative_to(root).as_posix() for p in (root/'FiniteAvalanchesAudit').rglob('*') if p.is_file()}
    require(actual == names, 'Extra/missing comparator artifact')
    for entry in bindings:
        require(hashlib.sha256(regular(root,entry['path']).read_bytes()).hexdigest() == entry['sha256'],
                'Comparator artifact hash differs: ' + entry['path'])
    summary = read_json(regular(root,'FiniteAvalanchesAudit/MainOrigin/semantic-data/SUMMARY.json'))
    require(summary.get('schema') == 'main-comparator-full-constantinfo-dag-v1' and
            name(summary['main_name']) == MAIN and summary.get('main_levels') == [] and
            summary.get('main_proof_serialized') is False, 'Wrong current complete constant-info capture')
    require(summary.get('owned_constants') == 957 and summary.get('whole_types_roundtripped') == 957,
            'Captured constant-info/type count differs from the reviewed 957')
    require(summary.get('retained_count') == 22 and len(summary['retained_targets']) == 22 and
            {e['display_name'] for e in summary['retained_targets']} == contents['main_inputs'] and
            set(summary['owned_axioms']) == contents['main_inputs'], 'Retained assumptions differ from exact22')
    require(len(summary['actual_main_axioms']) == 25 and set(summary['actual_main_axioms']) == PRIMITIVES | contents['main_inputs'],
            'Captured Main closure differs from exact22 and logical primitives')
    config = read_json(regular(root, 'FiniteAvalanchesAudit/MainOrigin/comparator.json'))
    require(set(config) == {'challenge_module','solution_module','theorem_names','definition_names','permitted_axioms','enable_nanoda'},
            'Unsupported comparator configuration')
    require(config['challenge_module'] == 'FiniteAvalanchesAudit.MainOrigin.Challenge' and
            config['solution_module'] == 'FiniteAvalanchesAudit.MainOrigin.Solution' and
            config['theorem_names'] == ['FiniteAvalanchesAudit.MainOrigin.finite_avalanches_origin'] and
            config['definition_names'] == [] and config['enable_nanoda'] is True,
            'Comparator must target complete Main with actual NanoDa replay')
    # Exact Main closure, rather than unused additional registered axioms.
    permitted = config['permitted_axioms']
    require(isinstance(permitted,list) and len(permitted) == len(set(permitted)) and
            set(permitted) == PRIMITIVES | contents['main_inputs'], 'Comparator must use exact22 Main assumptions')
    challenge = regular(root,'FiniteAvalanchesAudit/MainOrigin/Challenge.lean').read_text()
    code, tokens = source_tokens(challenge)
    require(re.findall(r'^\s*import\s+([^\n]+)', code, re.M) == ['Mathlib'], 'Challenge must import Mathlib only')
    require(not re.search(r'\bprivate\b', code), 'Private challenge names are not accepted')
    require(len(re.findall(r'\bsorry\b', code)) == 1 and len(re.findall(r'\bsorry\b', tokens)) == 1 and
            not re.search(r'\b(?:admit|sorryAx|native_decide|maxHeartbeats)\b',code) and
            not re.search(r'\b(?:axiom|constant)\b',tokens),
            'Challenge must have exactly its one declared theorem hole')
    solution = regular(root,'FiniteAvalanchesAudit/MainOrigin/Solution.lean').read_text()
    solution_code, solution_tokens = source_tokens(solution)
    require(not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|maxHeartbeats)\b',solution_code) and
            not re.search(r'\b(?:axiom|constant)\b',solution_tokens),
            'Solution contains an unapproved trust shortcut')
    if destination:
        destination.mkdir(exist_ok=False)
        (destination/'000.json').write_text(json.dumps(config,indent=2)+'\n')
        (destination/'pairs.tsv').write_text('FiniteAvalanchesAudit/MainOrigin/comparator.json\t'+str(destination/'000.json')+'\n')
    return 1


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    if args.check == bool(args.output):
        p.error('Select --check or --output DIRECTORY')
    try:
        count = prepare(ROOT,args.output)
        print(f'{count} reviewed current Main pair; actual matching and Lean/NanoDa replay still required.')
    except (ValueError, KeyError, TypeError, OSError) as error:
        raise SystemExit('Current comparator preflight rejected: '+str(error)) from error
