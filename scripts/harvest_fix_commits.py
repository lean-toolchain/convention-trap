import subprocess, re, json, sys
repos = sys.argv[1:]
MSG = re.compile(r'fix|misformal|wrong|incorrect|correct|statement|counterexample|junk|bug', re.I)
GUARD = [
 ("pos_guard", re.compile(r'\b0\s*<\s*[a-zA-Zα-ω]\w*|[a-zA-Zα-ω]\w*\s*>\s*0\b|≠\s*0\b|0\s*≠|1\s*≤\s*[a-zA-Z]\w*')),
 ("pnat", re.compile(r'ℕ\+|PNat')),
 ("int_cast", re.compile(r'\(\s*[^()]*:\s*(ℤ|ℝ|ℚ)\s*\)')),
 ("sub", re.compile(r'\w\s-\s\w')),
 ("div", re.compile(r'\w\s/\s\w|%')),
 ("domain", re.compile(r'Real\.sqrt|√|Real\.log|toNat|sInf|sSup|Nat\.find')),
]
out=[]
for repo in repos:
    log = subprocess.run(["git","-C",repo,"log","--no-merges","--format=%H%x09%s"],capture_output=True,text=True).stdout
    for line in log.splitlines():
        h,msg=line.split("\t",1)
        if not MSG.search(msg): continue
        diff = subprocess.run(["git","-C",repo,"show","--format=","-U0",h,"--","*.lean"],capture_output=True,text=True).stdout
        if not diff or len(diff) > 60000: continue
        minus=[l[1:] for l in diff.splitlines() if l.startswith("-") and not l.startswith("---")]
        plus=[l[1:] for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++")]
        tags=[]
        for name,rx in GUARD:
            a=sum(bool(rx.search(l)) for l in plus); b=sum(bool(rx.search(l)) for l in minus)
            if a!=b: tags.append(f"{name}{'+' if a>b else '-'}")
        if tags and len(plus)+len(minus) < 400:
            out.append({"repo":repo,"commit":h[:9],"msg":msg,"tags":tags,"size":len(plus)+len(minus)})
json.dump(out,open("/private/tmp/claude-501/realtools/candidates.json","w"),indent=1,ensure_ascii=False)
print(len(out))
for o in out: print(o["repo"][:12], o["commit"], o["size"], ",".join(o["tags"]), "|", o["msg"][:90])
