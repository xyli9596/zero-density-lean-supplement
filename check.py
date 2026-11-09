#!/usr/bin/env python3
"""Offline, kernel-checked build of the consolidated v10 project.

Usage: python3 check.py [V10.Module ...] [-j 3] [--force]
Set V10_DEPENDENCY_CACHE to a Lake project containing the pinned packages.
The default is the already installed local cache. No downloads or mutations
of the dependency project are performed. All manuscript/support sources are
built here; no old project proof .olean is used.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import sys
import time

PINNED_MATHLIB = 'db584cd6d46c92f209a44c0f1c829460d327499d'

ROOT = Path(__file__).resolve().parent
DEFAULT_CACHE = str(ROOT)
CACHE = Path(os.environ.get('V10_DEPENDENCY_CACHE',
    str(ROOT) if (ROOT / '.lake/packages/mathlib').exists() else DEFAULT_CACHE))
LEAN = Path(os.environ.get('V10_LEAN', str(Path.home() / '.elan/toolchains/leanprover--lean4---v4.33.0/bin/lean')))
OUT = ROOT / '.lake/build/lib/lean'
LOG = ROOT / 'verification'
OUT.mkdir(parents=True, exist_ok=True)
LOG.mkdir(exist_ok=True)
paths = [str(OUT)]
paths += [str(p / '.lake/build/lib/lean') for p in sorted((CACHE / '.lake/packages').iterdir())
          if (p / '.lake/build/lib/lean').is_dir()]
ENV = dict(os.environ, LEAN_PATH=os.pathsep.join(paths))

def sources():
    result = {}
    for folder in ['ZeroDensity', 'V10', 'Ray']:
        for p in (ROOT / folder).rglob('*.lean'):
            result['.'.join(p.relative_to(ROOT).with_suffix('').parts)] = (p, ROOT)
    for p in (ROOT / 'support').glob('*.lean'):
        result[p.stem] = (p, ROOT / 'support')
    return result

def imports(p):
    result = []
    for line in p.read_text().splitlines():
        match = re.match(r'^(?:public\s+)?import\s+(.+)', line)
        if match:
            body = re.sub(r'^all\s+', '', match.group(1).split('--', 1)[0])
            result.extend(re.findall(r'[A-Za-z_]\w*(?:\.\w+)*',
                                     body))
    return result

def check_source(p):
    # Also audited transitively by Lean's collectAxioms, not only this scan.
    text = re.sub(r'/\-.*?\-/|--[^\n]*', '', p.read_text(), flags=re.S)
    bad = re.findall(r'^\s*(?:axiom|opaque|unsafe)\b|\b(?:sorry|admit|native_decide)\b', text, re.M)
    if bad:
        raise RuntimeError(f'{p}: disallowed proof placeholders/declarations: {bad}')

def build(name, entry, force):
    p, source_root = entry
    check_source(p)
    out = OUT.joinpath(*name.split('.')).with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    log = LOG / (name + '.log')
    manifest = LOG / (name + '.json')
    sha = hashlib.sha256(p.read_bytes()).hexdigest()
    # Rebuild if any local dependency was compiled more recently.
    fresh = out.exists() and manifest.exists() and log.exists()
    if fresh:
        old = json.loads(manifest.read_text())
        fresh = old.get('source_sha256') == sha and old.get('returncode') == 0
        fresh = fresh and all(not (d := OUT.joinpath(*m.split('.')).with_suffix('.olean')).exists()
                              or d.stat().st_mtime <= out.stat().st_mtime for m in imports(p))
    if fresh and not force:
        return dict(json.loads(manifest.read_text()), cached=True)
    start = time.monotonic()
    proc = subprocess.run([str(LEAN), '--root=' + str(source_root), '-o', str(out), str(p)],
                          cwd=ROOT, env=ENV, text=True, capture_output=True)
    log.write_text(proc.stdout + proc.stderr)
    record = {'module': name, 'returncode': proc.returncode,
              'source': str(p.relative_to(ROOT)), 'source_sha256': sha,
              'seconds': round(time.monotonic() - start, 3),
              'log': str(log.relative_to(ROOT)), 'cached': False}
    manifest.write_text(json.dumps(record, indent=2) + '\n')
    return record

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='*')
    parser.add_argument('-j', type=int, default=3)
    parser.add_argument('--force', action='store_true')
    args = parser.parse_args()
    version = subprocess.run([str(LEAN), '--version'], capture_output=True, text=True, check=True).stdout.strip()
    if 'version 4.33.0' not in version:
        raise RuntimeError('Expected pinned Lean 4.33.0; found: ' + version)
    mathlib = CACHE / '.lake/packages/mathlib'
    revision = subprocess.run(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'],
                              capture_output=True, text=True, check=True).stdout.strip()
    if revision != PINNED_MATHLIB:
        raise RuntimeError('Mathlib revision differs from the audited pin: ' + revision)
    src = sources()
    requested = args.modules or sorted(src)
    selected = set()
    def include(name):
        if name in selected:
            return
        if name not in src:
            raise RuntimeError('Missing local module: ' + name)
        selected.add(name)
        for dep in imports(src[name][0]):
            if dep in src:
                include(dep)
            elif not dep.startswith(('Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Aesop')):
                raise RuntimeError(f'Unresolved source import {dep} in {name}')
    for name in requested:
        include(name)
    pending = set(selected)
    done = set()
    records = []
    running = {}
    failed = False
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.j) as pool:
        while pending or running:
            for name in sorted(pending):
                deps = set(imports(src[name][0])) & selected
                if deps <= done and len(running) < args.j and not failed:
                    running[pool.submit(build, name, src[name], args.force)] = name
                    pending.remove(name)
            if not running:
                if pending and not failed:
                    raise RuntimeError('Cyclic import dependencies: ' + ', '.join(sorted(pending)))
                break
            completed, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in completed:
                name = running.pop(future)
                record = future.result()
                records.append(record)
                print(f'{name}: ' + ('cached' if record['cached'] else 'checked')
                      if record['returncode'] == 0 else f'{name}: FAILED', flush=True)
                if record['returncode']:
                    print((ROOT / record['log']).read_text(), flush=True)
                    failed = True
                else:
                    done.add(name)
    result = {'lean': str(LEAN), 'lean_version': version,
              'mathlib_commit': revision, 'dependency_cache': str(CACHE),
              'requested': requested, 'modules': records,
              'all_selected_modules_checked': selected <= done,
              'unbuilt': sorted(selected - done),
              'note': 'A successful build certifies the Lean declarations, not all manuscript results.'}
    filename = 'last-full-run.json' if not args.modules else 'last-selected-run.json'
    (LOG / filename).write_text(json.dumps(result, indent=2) + '\n')
    return 0 if selected <= done else 1

if __name__ == '__main__':
    sys.exit(main())
