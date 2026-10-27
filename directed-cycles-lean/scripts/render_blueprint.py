#!/usr/bin/env python3
"""Render the explicit dependency frontier without requiring web services."""
import html
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
graph = json.loads((root / "blueprint/dependencies.json").read_text())
nodes = {n["id"]: n for n in graph["nodes"]}
checked = {"kernel_checked_module_replay", "kernel_checked_fresh_closure"}
lines = ["digraph blueprint {", 'rankdir=LR;', 'node [shape=box,style="rounded,filled"];']
for n in nodes.values():
    title = (n.get("number", "") + " " + n["title"]).strip()
    color = "#c6ead8" if n["status"] in checked else "#f3dedb"
    lines.append(f'{json.dumps(n["id"])} [label={json.dumps(title)},fillcolor="{color}"];')
    for d in n["dependencies"]:
        lines.append(f'{json.dumps(n["id"])} -> {json.dumps(d)};')
lines.append("}")
(root / "blueprint/graph.dot").write_text("\n".join(lines) + "\n")
data = json.dumps(graph, ensure_ascii=False).replace("<", "\\u003c")
template = r'''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Nearly linear directed cycles in vertex-transitive digraphs · Lean dependency blueprint</title>
<style>
body{font:16px/1.5 system-ui,sans-serif;margin:0;background:#f8fafb;color:#18252e}main{max-width:1350px;margin:auto;padding:32px}h1{margin:0;font-size:30px}h2{font-size:19px}p{max-width:1000px}.banner{border-left:5px solid #a83232;background:#fff0ed;padding:18px 24px;margin:20px 0}.muted{color:#5b6970}button,input,select{font:inherit}input,select{padding:8px;border:1px solid #b8c8ce;border-radius:5px}.layout{display:grid;grid-template-columns:280px 1fr;gap:24px}.list{max-height:74vh;overflow:auto;padding:2px}.node{display:block;width:100%;text-align:left;margin:7px 0;padding:10px;border:1px solid #c5d3d9;border-radius:7px;background:#fff;cursor:pointer}.node:hover,.node.selected{border-color:#1c5d7c;box-shadow:0 0 0 1px #1c5d7c}.tag{font-size:12px;border-radius:4px;padding:2px 6px;background:#f4dedb;display:inline-block;margin-top:5px}.tag.checked{background:#c6ead8}.columns{display:grid;grid-template-columns:1fr 1.1fr 1fr;gap:16px}.focus{background:white;padding:18px;border:2px solid #1c5d7c;border-radius:8px;height:fit-content}.source{white-space:pre-wrap;font:13px/1.6 ui-monospace,monospace;overflow-wrap:anywhere;background:#f0f3f5;padding:15px}code{overflow-wrap:anywhere;font-size:13px}a{color:#165c7d}.small{font-size:13px}#counts{font-weight:600}@media(max-width:900px){.layout{grid-template-columns:1fr}.list{max-height:220px}.columns{grid-template-columns:1fr}}
</style><main><h1>Nearly linear directed cycles in vertex-transitive digraphs</h1>
<p class="muted">Theorem 1.5 · Lean dependency blueprint · Bowen Li and Abhishek Methuku</p>
<div class="banner" id="banner"><strong id="statusTitle">Verification pending</strong><br><span id="statusText"></span></div>
<p id="counts"></p><p class="small">Select a node to inspect its prerequisites (right) and the results using it (left). Arrows mean “requires”. This is the project import graph, with library imports grouped into one node. It includes helper declarations beyond the main proof term. <a id="constantGraphLink" href="../verification/main-constant-closure.json">Exact transitive constant graph</a> · <a href="manuscript-map.json">Manuscript correspondence</a> · <a href="dependencies.json">Import graph data</a> · <a href="graph.dot">Graphviz source</a> · <a href="historical-planned-dependencies.json">Historical planned graph</a> · <a id="reportLink" href="../verification/axioms.log">Verification evidence</a></p>
<div class="layout"><aside><input id="search" placeholder="Find a lemma or dependency" style="width:90%"><p><label><input id="openOnly" type="checkbox"> Show unresolved only</label></p><div id="list" class="list"></div></aside>
<section><div class="columns"><div><h2>Used by →</h2><div id="parents"></div></div><div><h2>Selected result</h2><div id="focus" class="focus"></div></div><div><h2>→ Requires</h2><div id="children"></div></div></div><div id="detail"></div></section></div>
<p class="small muted">Source SHA-256: <code id="hash"></code>. The perimeter-gap construction (Theorem 1.3 and Section 8) is outside this target’s dependency closure. A source citation is not a formal proof.</p></main>
<script>const graph=DATA;const nodes=new Map(graph.nodes.map(n=>[n.id,n]));let current=graph.target;
const checked=n=>['kernel_checked_module_replay','kernel_checked_fresh_closure'].includes(n.status);
const title=n=>(n.number?n.number+' · ':'')+n.title;
const el=(tag,text,cls)=>{const e=document.createElement(tag);if(text)e.textContent=text;if(cls)e.className=cls;return e};
function badge(n){return el('span',n.status==='kernel_checked_fresh_closure'?'Fresh kernel replay passed':(checked(n)?'Module kernel replay passed':n.status.replaceAll('_',' ')),'tag'+(checked(n)?' checked':''))}
function button(n){const e=el('button',null,'node'+(n.id===current?' selected':''));e.append(el('div',title(n)),badge(n));e.onclick=()=>{current=n.id;render()};return e}
function render(){let list=document.getElementById('list');list.replaceChildren();const q=document.getElementById('search').value.toLowerCase();graph.nodes.filter(n=>(title(n)+' '+n.id).toLowerCase().includes(q)&&(!document.getElementById('openOnly').checked||!checked(n))).forEach(n=>list.append(button(n)));
const n=nodes.get(current);const focus=document.getElementById('focus');focus.replaceChildren(el('strong',title(n)),el('p',n.id,'small'),badge(n));
const parents=graph.nodes.filter(m=>m.dependencies.includes(current));document.getElementById('parents').replaceChildren(...parents.map(button));document.getElementById('children').replaceChildren(...n.dependencies.map(d=>button(nodes.get(d))));
const detail=document.getElementById('detail');detail.replaceChildren();if(n.note)detail.append(el('p',n.note));if(n.lean_declarations.length){detail.append(el('h2','Lean declarations'));n.lean_declarations.forEach(x=>detail.append(el('p',x,'source')))}if(n.source_file){const a=el('a','Open Lean source');a.href='../'+n.source_file;detail.append(a)}if(n.constant_closure_count!==undefined)detail.append(el('p',n.constant_closure_count+' constants from this module occur in the main dependency closure.','small'));if(n.external_imports?.length){const d=el('details');d.append(el('summary','External imports'),el('pre',n.external_imports.join('\n'),'source'));detail.append(d)}if(n.manuscript_annotations?.length){const d=el('details');d.append(el('summary','Manuscript correspondence'),el('pre',JSON.stringify(n.manuscript_annotations,null,2),'source'));detail.append(d)}if(n.source_lines)detail.append(el('p','Manuscript source lines '+n.source_lines.join('–'),'small'));if(n.statement_tex){const d=el('details');d.append(el('summary','Exact manuscript statement'),el('pre',n.statement_tex,'source'));detail.append(d)}if(n.source_url){const a=el('a','Literature source');a.href=n.source_url;detail.append(a)}detail.append(el('p',n.dependencies_complete?'Dependencies are recorded; the status above reports the completed verification stage.':'Further dependency expansion is required.','small muted'))}
document.getElementById('constantGraphLink').href=graph.exact_constant_graph;if(graph.constant_graph_status)document.getElementById('constantGraphLink').textContent=graph.constant_graph_status;const certified=graph.main_theorem_verified&&graph.certificate_eligible;document.getElementById('statusTitle').textContent=certified?'Theorem 1.5 and its dependency closure: kernel verified':'Verification in progress — no current certificate';document.getElementById('statusText').textContent=certified?'The exact main theorem and entire imported environment passed fresh replay in Lean’s kernel. The main proof uses only propext, Classical.choice and Quot.sound. No added mathematical axiom or admitted proof is used.':'The displayed status distinguishes elaboration, module replay and fresh closure replay. A certificate is issued only after every required check succeeds.';if(certified){document.getElementById('banner').style.borderColor='#267452';document.getElementById('banner').style.background='#e5f4ec';document.getElementById('reportLink').href='../verification/certificate.json';document.getElementById('reportLink').textContent='Reproducible certificate'}document.getElementById('hash').textContent=graph.source_sha256;document.getElementById('counts').textContent=graph.nodes.filter(checked).length+' checked nodes · '+graph.nodes.filter(n=>!checked(n)).length+' nodes awaiting replay · import edges over-approximate proof dependencies.';document.getElementById('search').oninput=render;document.getElementById('openOnly').onchange=render;render();</script></html>'''
(root / "blueprint/index.html").write_text(template.replace("DATA", data))
print(f"Rendered {len(nodes)} blueprint nodes")
