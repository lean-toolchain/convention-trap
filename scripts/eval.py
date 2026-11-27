#!/usr/bin/env python3
"""Precision / recall of a trap report against the corpus naming convention.

usage: scripts/eval.py trap-report/report.json [--include-unknown]

* decl `...pos_<kind>_<x>` must be flagged (error|warning) with <kind>
* decl `...neg_<x>` must not be flagged
"""
import json, re, sys
from collections import defaultdict

path = sys.argv[1]
include_unknown = "--include-unknown" in sys.argv
r = json.load(open(path))
flagged = list(r["findings"]) + (list(r["unknown"]) if include_unknown else [])

by_decl = defaultdict(set)
for f in flagged:
    by_decl[f["decl"]].add(f["kind"])

tp = defaultdict(int); fp = defaultdict(int)
pos_total = 0; pos_hit = 0; misses = []
decls = set()
for f in flagged:
    short = f["decl"].split(".")[-1]
    decls.add(short)
    m = re.match(r"pos_([A-Za-z]+)_", short)
    if short.startswith("neg_"):
        fp[f["kind"]] += 1
    elif m:
        if f["kind"] == m.group(1):
            tp[f["kind"]] += 1
        # other kinds on a positive item are not counted either way (unlabelled)

corpus = open("test/ConventionTrapTest/Corpus.lean").read()
positives = re.findall(r"theorem (pos_([A-Za-z]+)_\w+)", corpus)
for name, kind in positives:
    pos_total += 1
    hit = any(d.split(".")[-1] == name and kind in ks for d, ks in by_decl.items())
    pos_hit += hit
    if not hit:
        misses.append(f"{name} ({kind})")
negatives = re.findall(r"theorem (neg_\w+)", corpus)
neg_flagged = sorted({d.split(".")[-1] for d in by_decl if d.split(".")[-1].startswith("neg_")})

print(f"mode={r['inputs']['mode']} include_unknown={include_unknown}")
print(f"recall: {pos_hit}/{pos_total} = {pos_hit/pos_total:.0%}")
if misses: print("  missed:", ", ".join(misses))
print(f"negatives flagged: {len(neg_flagged)}/{len(negatives)} {neg_flagged}")
print("per-kind precision (labelled flags only):")
for k in sorted(set(tp) | set(fp)):
    tot = tp[k] + fp[k]
    print(f"  {k:15s} tp={tp[k]:3d} fp={fp[k]:3d} false-positive rate={fp[k]/tot:.0%}")
