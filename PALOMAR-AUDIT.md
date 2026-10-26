# Submission audit — 26 October 2026

This is an automated preparation audit by OpenAI Codex at Abhishek Methuku's
request. It is not independent human mathematical review, Palomar editorial
approval, or a registry certificate.

## Exact snapshot and policy

The existing submission, `9pdru5dwljmt`, uses commit
`16f43c7731a2d973e989c5e9006b62088dd3068d`, project `directed-cycles-lean`,
comparator `directed-cycles-lean/comparator.json`, and metadata
`directed-cycles-lean/formalization.yaml`.

The audit used the live policy at
[`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md)
and official validation code at
[`c02bbeaed888df45c4e28c4e99dba540ad21552a`](https://github.com/PalomarRegistry/PalomarSubmission/tree/c02bbeaed888df45c4e28c4e99dba540ad21552a).
Requirements can change; recheck the live policy before a later submission.

## Results for the existing submission

Twenty-five static compliance and evidence-consistency checks passed. These
checks were additional to the previously completed proof verification.

| Area | Evidence and conclusion |
| --- | --- |
| Complete repository | All 1,227 regular Lean files passed the current module-header and 10,000-line rules; no symlinks or compiled artifacts were found. The repository is below 500 MiB. |
| Statement | Challenge has 52 lines and three Mathlib imports. Its explicit statement agrees with Solution and with the archived Theorem 1.5 conventions and quantifier order. |
| Proof isolation | The only deliberate `sorry` is the independent Challenge placeholder. The proof-source import closure excludes Challenge; proof sources contain no admissions or extra-axiom declarations. |
| Axioms and closure | The recorded 64,512-constant main-theorem graph is complete, has no missing edge targets, and contains only `propext`, `Classical.choice`, and `Quot.sound` as axioms. |
| Certificate integrity | Every source and evidence hash recorded in the submitted certificate matched the downloaded exact snapshot. This hash audit is not itself a new kernel replay. |
| Blueprint | The 1,053-node import graph has no dangling edges, links to the actual constant graph, and identifies its over-approximation and historical routes. Every mapped manuscript excerpt matches the archived source. |
| Toolchain | Lean 4.35.0 satisfies the recorded minimum of 4.35.0-rc2. The nine dependency revisions are pinned; the earlier full preflight authenticated the matching Mathlib toolchain. |
| Metadata | Current official metadata and comparator validation passed. `project.authors` and `project.responsible_maintainers` already contain only Abhishek Methuku. Codex is disclosed in `automation`, not human authorship. |
| Licence | One root Apache-2.0 licence matches the identifier accepted by the full preflight; manuscript and external rights are distinguished in NOTICE. |
| Mechanical verification | Both the exact-commit full preflight and Palomar's submission verification succeeded. The preflight report contains no errors or warnings and records independent checker acceptance. |

Public evidence:

- [Full preflight for the submitted commit](https://github.com/methuku-git-hub/Nearly-linear-directed-cycles-in-vertex-transitive-digraphs/actions/runs/40160159378)
- [Palomar mechanical verification for submission 9pdru5dwljmt](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/40162833371)

## Corrections prepared after the audit

The submitted human-author fields needed no correction. The following
provenance and documentation improvements were made:

- Add explicit BGT and Tointon references for arguments already identified in
  the Lean sources and blueprint, stating the limited consequences actually
  formalized.
- Replace outdated preparation wording with commit-specific evidence and
  distinguish mechanical verification, editorial approval, and registration.
- Correct the project README's constant-graph path to its compressed `.json.gz`
  file and clarify that historical open-status comments are not current proof
  status.
- Clarify that the bundled local Comparator helper is supplemental: it does
  not reproduce all of the full registry pipeline's authentication, controls,
  and checker selection.

All Lean files, Challenge and Solution statements, the manuscript, comparator
configuration, and dependency pins are unchanged. Because the project
certificate also hashes documentation and metadata, a fresh kernel replay is
required before issuing a replacement certificate for these changed inputs.
The generated current certificate records the actual successful replay time.

## Before a retry

A new public commit requires its own passing full preflight; the reports above
must not be described as checks of that new commit. Use the exact 40-character
commit from the new passing run with the same project, comparator, and metadata
paths. The existing submission remains distinct and is not changed by commits
to this branch.

As of this audit, the existing submission's page reports successful mechanical
verification and a queued automated review, with no requested correction. This
audit found no evidence that the queue delay was caused by an authorship-field
error or by the Zulip suspension. The cause of the delay remains unknown.
Full Palomar acceptance still depends on its editorial review and registration.
