"""Writes the twelve Newton certificates WYDCurvature/C6*_*_*.lean (node lists only; the checks are run by the kernel).
usage: python gencert.py OUTDIR   (needs python-flint).  Each certificate after the first also imports the previous one,
so that `lake build` checks them one at a time; the import adds nothing to the proofs."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
OUT = sys.argv[1] if len(sys.argv) > 1 else '.' 
from expo import nums
from fractions import Fraction as Fr
S=nums()
REG={1:Fr(501,1000),2:Fr(2001,1000)}
HEAD='''/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import WYDCurvature.Newton%s

/-!
# Newton certificate for %s, %s

The exponents of the numerator, in increasing order. The kernel computes the Newton coefficients and
checks that they are polynomials in `t` with nonnegative coefficients. The check is cut into stages,
one theorem each, to keep the kernel's memory small.
-/

namespace WYD.Newton

%send WYD.Newton
'''
def lst(l):
    out='['; line=0; parts=[f"({a}, {b})" for a,b in l]; cur='['
    rows=[]; cur=''
    for i,x in enumerate(parts):
        y=x+(', ' if i<len(parts)-1 else '')
        if len(cur)+len(y)>92: rows.append(cur.rstrip()); cur='    '
        cur+=y
    rows.append(cur); return '['+'\n'.join(rows)+']'
names=[]
for (w,c),f in S.items():
    for reg in (1,2):
        d0=REG[reg]; us=sorted({k[:2] for k in f.t},key=lambda e:e[0]+e[1]*d0); vs=sorted({k[2:] for k in f.t},key=lambda e:e[0]+e[1]*d0)
        if (w,c)==(64,2): vs=[(a+2,b) for a,b in vs]      # Lean anchors this numerator at sigma_2, expo.py at sigma_1
        o=[t for t in range(3) if t!=c]; s=1 if reg==1 else -1
        num=f"num65 par{reg} {'1' if s==1 else '(-1)'} {c} {o[0]} {o[1]}" if w==65 else f"num64 par{reg} {o[0]} {o[1]}"
        nm=f"cert{w}_{c}_{reg}"; names.append(f"C{w}_{c}_{reg}"); ns=f"c{w}_{c}_{reg}"; P=f"par{reg}"
        B=f"namespace {ns}\n\ndef rows : List (Node × List (Node × PP)) := group ({num})\n\ndef vs : List Node :=\n  {lst(vs)}\n\n"
        CH=10; ch=[us[i:i+CH] for i in range(0,len(us),CH)]; n=len(ch)
        for i,x in enumerate(ch): B+=f"def u{i} : List Node :=\n  {lst(x)}\n\n"
        pre=lambda i: "rows" if i==0 else f"(after {P} u{i-1} {pre(i-1)})"
        for i in range(n):
            f_="part" if i<n-1 else "check2"
            B+=f"theorem h{i} : {f_} {P} u{i} vs\n    {pre(i)} = true := by\n  decide +kernel\n\n"
        ap="h%d"%(n-1)
        for i in range(n-2,-1,-1): ap=f"check2_append _ _ _ h{i}\n    ({ap})"
        B+=f"end {ns}\n\ntheorem {nm} : ∃ us vs, check2 {P} us vs (group ({num})) = true :=\n  ⟨_, _, {ap.replace('h', ns+'.h')if False else ap}⟩\n\n"
        import re
        B=B[:B.index(f"end {ns}")]+re.sub(r'\bh(\d+)\b',ns+r'.h\1',B[B.index(f"end {ns}"):])
        prev='' if len(names)==1 else f"\nimport WYDCurvature.{names[-2]}  -- build order only: one certificate check at a time"
        open(os.path.join(OUT,f"C{w}_{c}_{reg}.lean"),"w").write(HEAD%(prev,f"({w})",f"position {c}, "+("`d < 1`" if reg==1 else "`1 < d ≤ 3`"),B))
print(' '.join(names))
