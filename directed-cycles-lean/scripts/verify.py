#!/usr/bin/env python3
"""Fail-closed source build, exact-target audit and fresh kernel certification."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from build_blueprint import build as build_blueprint

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MATHLIB_REV = '5ed2965256430c3649e86755f9576b54eca72435'
LEAN_COMMIT = '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, name):
    print('Checking ' + name, flush=True)
    path = ROOT / 'verification' / (name + '.log')
    with path.open('w') as stream:
        result = subprocess.run(args, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    output = path.read_text()
    if result.returncode:
        raise RuntimeError(f'{name} failed (exit {result.returncode}); see {path}')
    if name in {'build', 'axioms', 'kernel-replay'} and re.search(r'\bwarning:', output):
        raise RuntimeError(f'{name} produced warnings; see {path}')
    return output


def strip_comments(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1; i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1; i += 2; out.append(' ')
        elif depth:
            i += 1
        elif source.startswith('--', i):
            j = source.find('\n', i); i = len(source) if j < 0 else j
        else:
            out.append(source[i]); i += 1
    if depth:
        raise RuntimeError('Unclosed Lean comment')
    return ''.join(out)


def validate_graph(graph):
    nodes = {n['id']: n for n in graph['nodes']}
    if len(nodes) != len(graph['nodes']):
        raise RuntimeError('Duplicate blueprint node')
    active, done = set(), set()
    def walk(key):
        if key not in nodes: raise RuntimeError(f'Unknown dependency {key}')
        if key in active: raise RuntimeError(f'Cyclic import dependency {key}')
        if key in done: return
        active.add(key)
        for child in nodes[key]['dependencies']: walk(child)
        active.remove(key); done.add(key)
    walk(graph['target'])
    if done != set(nodes): raise RuntimeError('Nodes outside target import closure')
    if any(not n['dependencies_complete'] for n in nodes.values()):
        raise RuntimeError('Unexpanded blueprint dependencies')
    return nodes


def validate_closure(closure):
    rows = {r['name']: r for r in closure['declarations']}
    if not closure['complete'] or len(rows) != len(closure['declarations']):
        raise RuntimeError('Incomplete or duplicate constant inventory')
    seen, pending = set(), [closure['root']]
    if closure['root'] != 'DirectedCycles.theorem_1_5':
        raise RuntimeError('Wrong constant-closure root')
    while pending:
        name = pending.pop()
        if name in seen: continue
        if name not in rows: raise RuntimeError(f'Missing dependency {name}')
        seen.add(name); pending.extend(rows[name]['dependencies'])
    if seen != set(rows): raise RuntimeError('Unreachable constants in closure inventory')
    axioms = {n for n,r in rows.items() if r['kind'] == 'axiom'}
    if axioms != set(closure['axioms']) or axioms - ALLOWED:
        raise RuntimeError(f'Unexpected closure axioms: {sorted(axioms)}')
    if any(r['module'] == '[current audit]' for r in rows.values()):
        raise RuntimeError('Main theorem depends on audit code')
    return rows


def source_files():
    files = [p for p in ROOT.rglob('*') if p.is_file() and p.name != '.DS_Store' and
             not {'.lake','.git','verification','blueprint','__pycache__'}.intersection(p.relative_to(ROOT).parts)]
    # Historic plans and source annotations are inputs, while the active graph is generated.
    files.extend(ROOT/'blueprint'/n for n in ['historical-planned-dependencies.json'])
    return sorted(files)


def hashes(paths):
    return {str(p.relative_to(ROOT)): sha(p) for p in paths}


def package_state():
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    packages = []
    for pkg in manifest['packages']:
        path = ROOT/'.lake/packages'/pkg['name']
        rev = subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
        if rev != pkg['rev']: raise RuntimeError(f'Wrong revision for {pkg["name"]}')
        dirty = subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True)
        if dirty: raise RuntimeError(f'Tracked dependency changes in {pkg["name"]}')
        packages.append({'name':pkg['name'],'revision':rev})
    if next(p['revision'] for p in packages if p['name']=='mathlib') != MATHLIB_REV:
        raise RuntimeError('Unexpected mathlib revision')
    return packages


def save_graph(graph):
    (ROOT/'blueprint/dependencies.json').write_text(json.dumps(graph,indent=2,ensure_ascii=False)+'\n')
    subprocess.run([sys.executable,'scripts/render_blueprint.py'],cwd=ROOT,check=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--partial',action='store_true')
    modes.add_argument('--certify',action='store_true')
    args=parser.parse_args(); os.chdir(ROOT)
    verification=ROOT/'verification'; verification.mkdir(exist_ok=True)
    for filename in ['certificate.json','partial-report.json']:
        old=verification/filename
        if old.exists(): old.replace(old.with_name('previous-'+filename))
    # The UI must never retain a certificate claim while a new run is pending.
    gp=ROOT/'blueprint/dependencies.json'
    if gp.exists():
        g=json.loads(gp.read_text());g['main_theorem_verified']=False;g['certificate_eligible']=False
        for n in g['nodes']: n['status']='pending_verification'
        save_graph(g)
    if not shutil.which('lake') or not shutil.which('lean'):
        raise RuntimeError('Install the pinned toolchain and put it on PATH')
    protected=source_files(); start=hashes(protected)
    for path in [ROOT/'DirectedCycles.lean']+sorted((ROOT/'DirectedCycles').glob('*.lean')):
        hit=re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe)\b',strip_comments(path.read_text()))
        if hit: raise RuntimeError(f'Forbidden proof escape in {path.name}: {hit.group()}')
    provenance=json.loads((ROOT/'manuscript/provenance.json').read_text())
    if sha(ROOT/'manuscript/source.tex') != provenance['sha256']:
        raise RuntimeError('Changed manuscript snapshot')
    lean_version=run(['lean','--version'],'lean-version').strip()
    if '4.34.0' not in lean_version or LEAN_COMMIT not in lean_version:
        raise RuntimeError('Wrong Lean version or compiler commit')
    packages=package_state()
    run(['lake','build'],'build')
    closure_path=verification/'main-constant-closure.json'
    if closure_path.exists(): closure_path.unlink()
    output=run(['lake','env','lean','Audit.lean'],'axioms')
    declarations, target = {}, None
    for line in output.splitlines():
        if 'DECLARATION_JSON ' in line:
            row=json.loads(line.split('DECLARATION_JSON ',1)[1])
            if set(row['axioms'])-ALLOWED: raise RuntimeError(f'Unexpected axioms: {row["name"]}')
            declarations[row['name']]=row
        if 'MAIN_JSON ' in line: target=json.loads(line.split('MAIN_JSON ',1)[1])
    if not declarations or not target or not target['theorem_present'] or not target['exact_target_type']:
        raise RuntimeError('No unconditional theorem of the exact requested type')
    if set(target['axioms'])-ALLOWED: raise RuntimeError('Unexpected main theorem axiom')
    closure=json.loads(closure_path.read_text()); closure_rows=validate_closure(closure)
    if set(closure['axioms']) != set(target['axioms']):
        raise RuntimeError('Cached axiom audit disagrees with direct closure traversal')
    graph=build_blueprint(declarations,closure);nodes=validate_graph(graph)
    for n in nodes.values():
        if any(d not in declarations for d in n['lean_declarations']):
            raise RuntimeError(f'Unknown blueprint theorem in {n["id"]}')
    save_graph(graph)
    expected={'DirectedCycles','Mathlib.Combinatorics.Hall.Finite'}
    expected.update('DirectedCycles.'+p.stem for p in (ROOT/'DirectedCycles').glob('*.lean'))
    root_imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',(ROOT/'DirectedCycles.lean').read_text(),re.M)
    project_modules=expected-{'DirectedCycles','Mathlib.Combinatorics.Hall.Finite'}
    if set(root_imports)!=project_modules or len(root_imports)!=len(project_modules):
        raise RuntimeError('Root does not import every project module exactly once')
    replayed=[]
    if args.partial:
        replay=run(['lake','env','lean','scripts/Replay.lean'],'kernel-replay')
        replayed=re.findall(r'^passed ([A-Za-z0-9_.]+)$',replay,re.M)
        if set(replayed)!=expected or len(replayed)!=len(expected):
            raise RuntimeError('Replay omitted or duplicated modules')
        for n in nodes.values():
            if n['kind']!='imported_libraries': n['status']='kernel_checked_module_replay'
        save_graph(graph)
    report=dict(status='MAIN_ELABORATED_FRESH_CLOSURE_PENDING',checked_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        source_sha256=provenance['sha256'],lean_version=lean_version,packages=packages,
        main_theorem=target,allowed_foundational_axioms=sorted(ALLOWED),
        project_theorems_audited=sum(n.startswith('DirectedCycles.') for n in declarations),
        exact_constant_closure_count=len(closure_rows),exact_constant_closure_sha256=sha(closure_path),
        exact_constant_closure='verification/main-constant-closure.json',
        dependency_inventory_complete=True,sequential_module_replay_passed=args.partial,
        replayed_modules=sorted(replayed),project_modules_imported_by_root=sorted(project_modules),
        fresh_dependency_closure_replay_passed=False,independent_kernel=False,
        declarations=list(declarations.values()),certificate_refusal_reasons=['Fresh imported-closure kernel replay has not completed'])
    if args.certify:
        run(['lake','env','leanchecker','--fresh','--verbose','DirectedCycles'],'kernel-fresh-closure')
        # Recheck all proof and verification sources and dependency revisions after the long replay.
        if protected != source_files() or start != hashes(protected):
            raise RuntimeError('Sources changed during verification')
        if packages != package_state(): raise RuntimeError('Dependencies changed during verification')
        if sha(closure_path)!=report['exact_constant_closure_sha256']:
            raise RuntimeError('Closure inventory changed during verification')
        for n in nodes.values(): n['status']='kernel_checked_fresh_closure'
        graph['main_theorem_verified']=True;graph['certificate_eligible']=True;save_graph(graph)
        report.update(status='MAIN_THEOREM_AND_CLOSURE_KERNEL_VERIFIED',
            checked_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
            fresh_dependency_closure_replay_passed=True,certificate_refusal_reasons=[])
        filename='certificate.json'
    else:
        if protected != source_files() or start != hashes(protected): raise RuntimeError('Sources changed during verification')
        filename='partial-report.json'
    report['files']=hashes(sorted(p for p in ROOT.rglob('*') if p.is_file() and p.name != '.DS_Store' and
        not {'.lake','.git','verification','__pycache__'}.intersection(p.relative_to(ROOT).parts)))
    report['evidence_files']=hashes([verification/n for n in ['lean-version.log','build.log','axioms.log','main-constant-closure.json']+(['kernel-replay.log'] if args.partial else [])]+([verification/'kernel-fresh-closure.log'] if args.certify else []))
    report['checker_binary_sha256']=sha(Path(shutil.which('lean')).resolve().parent/'leanchecker')
    temporary=verification/(filename+'.tmp');temporary.write_text(json.dumps(report,indent=2)+'\n');temporary.replace(verification/filename)
    print('Main theorem and imported dependency closure passed fresh kernel replay.' if args.certify else 'Partial replay passed; no certificate issued.',flush=True)
    return 0


if __name__=='__main__':
    try: sys.exit(main())
    except Exception as error:
        # A failure must not leave the active blueprint claiming certification.
        gp=ROOT/'blueprint/dependencies.json'
        if gp.exists():
            graph=json.loads(gp.read_text());graph['main_theorem_verified']=False;graph['certificate_eligible']=False
            save_graph(graph)
        print(f'VERIFICATION FAILED: {error}',file=sys.stderr);sys.exit(1)
