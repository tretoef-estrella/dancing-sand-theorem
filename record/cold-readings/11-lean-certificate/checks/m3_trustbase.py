# M3: search every .lean of project/RequestProject and project/checks for constructs that touch the trust base.
# Each hit is classified as in code or inside a comment/docstring (block comments /- -/ nested, line comments --).
import os, re
R = 'material/project'
def files(sub):
    out = []
    for d, _, fs in os.walk(os.path.join(R, sub)):
        for f in fs:
            if f.endswith('.lean'): out.append(os.path.join(d, f))
    return sorted(out)
def code_mask(src):
    # returns a list of booleans: True if character is code (not comment, not string)
    mask = [True]*len(src); i = 0; depth = 0; n = len(src)
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            for k in range(i, j): mask[k] = False
            i = j; continue
        if src.startswith('/-', i):
            depth += 1; mask[i] = mask[i+1] = False; i += 2; continue
        if depth > 0 and src.startswith('-/', i):
            depth -= 1; mask[i] = mask[i+1] = False; i += 2; continue
        if depth > 0: mask[i] = False; i += 1; continue
        if src[i] == '"':
            j = i+1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            for k in range(i, min(j+1, n)): mask[k] = False
            i = j+1; continue
        i += 1
    return mask
PATS = {
 'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'axiom': r'\baxiom\b', 'native_decide': r'\bnative_decide\b',
 'implemented_by': r'implemented_by', 'extern': r'\bextern\b', 'unsafe': r'\bunsafe\b', 'opaque': r'\bopaque\b',
 'partial': r'\bpartial\b', 'csimp': r'csimp', 'skipKernelTC': r'skipKernelTC', 'debug.': r'\bdebug\.',
 'set_option': r'\bset_option\b', 'elab': r'\belab\b|\belab_rules\b', 'macro': r'\bmacro\b|\bmacro_rules\b',
 'syntax': r'\bsyntax\b', 'notation': r'\bnotation\b|\binfix[lr]?\b|\bprefix\b|\bpostfix\b',
 'instance': r'\binstance\b', 'local instance': r'\blocal instance\b|attribute \[local instance\]|attribute \[instance\]',
 'decide': r'\bdecide\b', 'Lean.Elab/meta': r'\bLean\.Elab\b|\bMetaM\b|\bTacticM\b|\bCommandElabM\b|\binitialize\b|\brun_cmd\b|\brun_tac\b|#eval',
 'privateAxiom': r'ofReduceBool|Lean\.ofReduceBool|trustCompiler|reduceBool',
}
if __name__ == "__main__":
  for sub in ['RequestProject', 'checks']:
      fl = files(sub)
      print(f'===== {sub}: {len(fl)} files')
      hits = {k: [] for k in PATS}
      for f in fl:
          src = open(f, encoding='utf-8').read(); m = code_mask(src)
          for k, p in PATS.items():
              for mo in re.finditer(p, src):
                  line = src.count('\n', 0, mo.start()) + 1
                  incode = m[mo.start()]
                  lt = src.splitlines()[line-1].strip()
                  hits[k].append((os.path.relpath(f, R), line, incode, lt))
      for k, h in hits.items():
          code = [x for x in h if x[2]]; com = [x for x in h if not x[2]]
          nf = len({x[0] for x in code})
          print(f'--- {k}: {len(code)} in code ({nf} files), {len(com)} in comments/strings')
          show = code if k not in ('decide',) else []
          for x in show[:80]: print('   CODE', x[0], x[1], '|', x[3][:150])
          if k in ('axiom', 'sorry', 'native_decide', 'unsafe', 'opaque', 'partial'):
              for x in com[:20]: print('   COMMENT', x[0], x[1], '|', x[3][:150])
          if k == 'decide':
              for f_ in sorted({x[0] for x in code}): print('   decide-file', f_, sum(1 for x in code if x[0]==f_))
