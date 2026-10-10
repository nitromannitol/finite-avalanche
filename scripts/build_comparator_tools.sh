#!/usr/bin/env bash
# Run only in a fresh owned tools directory, never in an established checkout.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
test "$#" -eq 1
destination=$1
case "$destination" in /*) ;; *) echo 'Tools destination must be absolute' >&2; exit 1 ;; esac
test ! -e "$destination"
mkdir -p "$destination"
python3 -B - "$root" "$destination" <<'PY'
import json, pathlib, re, subprocess, sys
root, target = map(pathlib.Path, sys.argv[1:])
pins = json.loads((root/'audit/comparator-tool-pins.json').read_text())
assert pins['lean_toolchain'] == (root/'lean-toolchain').read_text().strip()
resolved = {}
for name, entry in pins['tools'].items():
    rev = entry['commit']
    if not re.fullmatch('[0-9a-f]{40}', rev):
        raise SystemExit('Tool needs a full immutable commit: '+name)
    path = target/name
    subprocess.run(['git','clone','--no-checkout',entry['url'],str(path)],check=True)
    subprocess.run(['git','-C',str(path),'checkout','--detach',rev],check=True)
    actual = subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
    if actual != rev: raise SystemExit('Tool source revision differs: '+name)
    resolved[name] = {'url':entry['url'],'commit':actual}
for name in ('comparator','lean4export'):
    if (target/name/'lean-toolchain').read_text().strip() != pins['lean_toolchain']:
        raise SystemExit('Toolchain mismatch: '+name)
(target/'tool-receipt.json').write_text(json.dumps({'sources':resolved,'lean_toolchain':pins['lean_toolchain'],'build_complete':False},indent=2)+'\n')
PY
(cd "$destination/comparator" && lake build) 2>&1 | tee "$destination/comparator-build.log"
(cd "$destination/lean4export" && lake build) 2>&1 | tee "$destination/exporter-build.log"
mkdir -p "$destination/bin"
(cd "$destination/landrun" && CGO_ENABLED=0 go build -trimpath -o "$destination/bin/landrun" ./cmd/landrun) \
  2>&1 | tee "$destination/landrun-build.log"
rustup toolchain install 1.90.0 --profile minimal
(cd "$destination/nanoda" && cargo +1.90.0 build --locked --release) \
  2>&1 | tee "$destination/nanoda-build.log"
install -m 755 "$root/scripts/comparator_landrun.py" "$destination/bin/comparator-landrun"
python3 -B - "$root" "$destination" <<'PY'
import hashlib, json, pathlib, sys
root,p=map(pathlib.Path,sys.argv[1:]); receipt=json.loads((p/'tool-receipt.json').read_text())
bins={'comparator':'comparator/.lake/build/bin/comparator','lean4export':'lean4export/.lake/build/bin/lean4export',
      'landrun':'bin/landrun','nanoda':'nanoda/target/release/nanoda_bin'}
receipt['binaries']={name:{'path':str(p/file),'sha256':hashlib.sha256((p/file).read_bytes()).hexdigest()} for name,file in bins.items()}
source=root/'scripts/comparator_landrun.py'; adapter=p/'bin/comparator-landrun'
if source.is_symlink() or adapter.is_symlink() or source.read_bytes()!=adapter.read_bytes():
    raise SystemExit('Landrun launcher differs from reviewed project source')
receipt['adapters']={'landrun_cli':{
    'source':'scripts/comparator_landrun.py',
    'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'path':str(adapter),'sha256':hashlib.sha256(adapter.read_bytes()).hexdigest()}}
receipt['build_complete']=True
(p/'tool-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
PY
