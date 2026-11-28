#!/usr/bin/env python3
"""Merge trap-report shard JSONs from a Mathlib scan; write noise.json, review-sample.md; print a summary.

usage: noise_aggregate.py <shards-dir> <out-dir> [--sample 100] [--seed 0]
"""
import json, pathlib, random, sys, collections

def main():
    args = sys.argv[1:]
    src, out = pathlib.Path(args[0]), pathlib.Path(args[1])
    n_sample = int(args[args.index('--sample') + 1]) if '--sample' in args else 100
    seed = int(args[args.index('--seed') + 1]) if '--seed' in args else 0
    out.mkdir(parents=True, exist_ok=True)
    decls = 0; findings = []; unknown = []; benign = 0; shards = 0
    for p in sorted(src.rglob('report.json')):
        r = json.loads(p.read_text()); shards += 1
        decls += r['summary']['decls_checked']
        findings += r.get('findings', []); unknown += r.get('unknown', []); benign += len(r.get('benign', []))
    def kind(f): return f.get('kind') or f.get('finding', {}).get('kind')
    def sev(f): return f.get('severity') or f.get('finding', {}).get('severity')
    by = collections.Counter((kind(f), sev(f)) for f in findings)
    flagged_decls = len({(f.get('file'), f.get('decl')) for f in findings})
    summ = {'shards': shards, 'declsChecked': decls, 'findings': len(findings), 'flaggedDecls': flagged_decls,
            'unknown': len(unknown), 'benign': benign,
            'byKind': {f'{k}/{s}': c for (k, s), c in sorted(by.items(), key=lambda x: -x[1])}}
    (out / 'noise.json').write_text(json.dumps({'summary': summ, 'findings': findings}, indent=1, ensure_ascii=False))
    rnd = random.Random(seed)
    sample = rnd.sample(findings, min(n_sample, len(findings)))
    lines = ['# Review sample (Mathlib statements are proved: each item is TP-in-spirit or FP)', '',
             '| # | kind | sev | decl | expr | cond | label (TP/FP/benign) |', '|---|---|---|---|---|---|---|']
    for i, f in enumerate(sample, 1):
        g = {**f.get('finding', {}), **f}
        esc = lambda s: str(s or '').replace('|', '\\|').replace('\n', ' ')[:120]
        lines.append(f"| {i} | {kind(f)} | {sev(f)} | `{esc(g.get('decl'))}` | `{esc(g.get('expr_pp'))}` | `{esc(g.get('condition_pp'))}` | |")
    (out / 'review-sample.md').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    print('## Mathlib noise\n')
    rate = 100 * flagged_decls / decls if decls else 0
    print(f"- shards: {shards}, declarations checked: {decls}")
    print(f"- findings (error+warning): {len(findings)} on {flagged_decls} declarations ({rate:.2f}% of checked)")
    print(f"- unknown (CI info): {len(unknown)}, benign (hidden): {benign}\n")
    print('| kind/severity | count |\n|---|---|')
    for k, c in summ['byKind'].items(): print(f'| {k} | {c} |')

if __name__ == '__main__':
    main()
