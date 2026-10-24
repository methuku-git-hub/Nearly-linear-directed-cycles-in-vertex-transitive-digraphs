#!/usr/bin/env python3
"""Generate the project import DAG; keep exact kernel-constant edges separately."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def build(declarations, closure):
    historical = json.loads((ROOT / 'blueprint/historical-planned-dependencies.json').read_text())
    source_hash = json.loads((ROOT / 'manuscript/provenance.json').read_text())['sha256']
    by_module = {}
    for row in declarations.values():
        by_module.setdefault(row['module'], []).append(row['name'])
    sources = {'DirectedCycles.' + p.stem: p for p in (ROOT / 'DirectedCycles').glob('*.lean')}
    imports = {}
    for mod, path in sources.items():
        deps = []
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                match = re.fullmatch(r'import ([A-Za-z0-9_.]+)\s*', line)
                if not match:
                    raise RuntimeError(f'Unparsed import: {path}: {line}')
                deps.append(match[1])
        imports[mod] = sorted(set(deps))
    selected, visiting = set(), set()
    def walk(mod):
        if mod in visiting:
            raise RuntimeError(f'Cyclic source imports: {mod}')
        if mod in selected:
            return
        if mod not in sources:
            raise RuntimeError(f'Missing project source {mod}')
        visiting.add(mod)
        for dep in imports[mod]:
            if dep.startswith('DirectedCycles.'):
                walk(dep)
        visiting.remove(mod)
        selected.add(mod)
    walk('DirectedCycles.Theorem15')
    exact_modules = {r['module'] for r in closure['declarations'] if r['module'].startswith('DirectedCycles.')}
    if not exact_modules <= selected:
        raise RuntimeError(f'Kernel closure outside import graph: {exact_modules - selected}')
    mappings = []
    for old in historical['nodes']:
        if old['kind'] != 'manuscript':
            continue
        used = [n for n in old.get('lean_declarations', []) if n in declarations]
        mapping = {k: old[k] for k in ('id', 'title', 'number', 'source_lines', 'statement_tex', 'note') if k in old}
        mapping['lean_declarations'] = used
        mapping['modules'] = sorted({declarations[n]['module'] for n in used})
        mapping['scope'] = 'Source correspondence annotation. Consult the actual Lean type; a conditional reduction is not the unconditional source statement.'
        if old['id'] == 'thm:main':
            mapping.update(lean_declarations=['DirectedCycles.theorem_1_5'], modules=['DirectedCycles.Theorem15'],
                           scope='Exact main target, including manuscript looplessness convention; independently restated in Audit.lean.')
        if old['id'] == 'thm:structure':
            mapping.update(lean_declarations=['DirectedCycles.finite_structural_input'], modules=['DirectedCycles.FiniteStructuralTheorems'],
                           scope='The proved finite consequence needed for Theorem 1.5, for the full automorphism group and its actual induced quotient group; not an assertion of every formulation of the cited literature theorem.')
        mappings.append(mapping)
    (ROOT / 'blueprint/manuscript-map.json').write_text(json.dumps(mappings, indent=2, ensure_ascii=False)+'\n')
    annotations = {}
    for m in mappings:
        for mod in m['modules']:
            annotations.setdefault(mod, []).append(m)
    library_imports = sorted({d for m in selected for d in imports[m] if not d.startswith('DirectedCycles.')})
    counts = {}
    for row in closure['declarations']:
        counts[row['module']] = counts.get(row['module'], 0) + 1
    nodes = [dict(id='thm:main', title='Nearly linear directed cycle bound', number='1.5', kind='main',
        status='elaborated_pending_kernel_replay', dependencies=['DirectedCycles.Theorem15'], dependencies_complete=True,
        lean_declarations=['DirectedCycles.theorem_1_5'], source_lines=[97,99],
        statement_tex=next(m['statement_tex'] for m in mappings if m['id']=='thm:main'),
        note='The exact main theorem has no structural premise. Certification requires fresh kernel replay of the entire imported environment.')]
    for mod in sorted(selected):
        external = [d for d in imports[mod] if not d.startswith('DirectedCycles.')]
        deps = [d for d in imports[mod] if d.startswith('DirectedCycles.')]
        if external:
            deps.append('libraries')
        nodes.append(dict(id=mod, title=re.sub(r'(?<!^)(?=[A-Z])', ' ', mod.split('.')[-1]), kind='project_module',
            module=mod, source_file=str(sources[mod].relative_to(ROOT)), status='elaborated_pending_kernel_replay',
            dependencies=deps, dependencies_complete=True, lean_declarations=sorted(by_module.get(mod, [])),
            external_imports=external, constant_closure_count=counts.get(mod, 0),
            manuscript_annotations=annotations.get(mod, []),
            note='Edges are source imports, so this graph intentionally includes helpers not used by the main proof term. The separate kernel-constant graph records the transitive proof dependencies exactly, including definitions and recursor metadata.'))
    nodes.append(dict(id='libraries', title='Pinned Lean and library dependency closure', kind='imported_libraries',
        status='pending_fresh_kernel_replay', dependencies=[], dependencies_complete=True, lean_declarations=[],
        external_imports=library_imports,
        note='Grouped library imports. Every constant reached by the main theorem is recorded in main-constant-closure.json. Fresh replay checks all declarations in the imported environment, including library proofs, with Lean\'s kernel.'))
    graph = dict(schema_version=2, target='thm:main', source_sha256=source_hash,
        main_theorem_verified=False, certificate_eligible=False, dependency_inventory_complete=True,
        graph_kind='Project source-import DAG with grouped external imports; over-approximation of the actual theorem dependency closure',
        exact_constant_graph='../verification/main-constant-closure.json',
        manuscript_map='manuscript-map.json', archived_planned_graph='historical-planned-dependencies.json',
        scope_note='The finite structural theorem and local Lie dimension induction supply the formerly open inputs. General local-group globalization and Lie third-theorem alternatives are not used or claimed proved. Historic planned dependencies are retained separately with their original status. Theorem 1.3 and Section 8 are outside this task.',
        proof_replacements=historical['proof_replacements'] + [dict(source='BGT local dimension induction', replacement='Complete induction on the dimension of the actual smooth local target, including its zero-dimensional base; no local-to-global Lie identification is assumed.')],
        nodes=nodes)
    (ROOT / 'blueprint/dependencies.json').write_text(json.dumps(graph,indent=2,ensure_ascii=False)+'\n')
    return graph
