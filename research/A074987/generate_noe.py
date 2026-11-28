"""Compile a complete positive divisibility DAG into pinned-kernel Lean proof source."""
from pathlib import Path
import argparse,json,math,re
from functools import cache
import sympy

parser=argparse.ArgumentParser()
parser.add_argument('data',type=Path)
parser.add_argument('module',help='Lean module and namespace, e.g. Noe18')
args=parser.parse_args()
assert re.fullmatch('[A-Z][A-Za-z0-9_]*',args.module)
data=json.loads(args.data.read_text())
assert not data['unresolved']
bound=data['bound']; root=3261636
nodes={int(a):(list(ps),b) for a,(ps,b) in data['nodes'].items()}
@cache
def fac(a):return {int(p):int(e) for p,e in sympy.factorint(a).items()}
def factors(a):return sorted(p for p,e in fac(a).items() for _ in range(e))
def normal(a,b,ps):
    assert 0<a and 0<b<=2*a and a!=b
    assert set(ps)==set(fac(a))^set(fac(b))
    q=math.prod(p**(min(e,fac(b)[p])-(e!=fac(b)[p])) for p,e in fac(a).items() if p in fac(b))
    assert all(math.gcd(p,q)==1 for p in ps)
    return a//q,b//q,tuple(ps)
moves={a:normal(a,b,ps) for a,(ps,b) in nodes.items()}
seen=set();ends=set()
def reach(a):
    if a in seen:return
    if a>=bound:ends.add(a);return
    assert a in nodes and a>0
    seen.add(a)
    for p in nodes[a][0]:assert p>1;reach(a*p)
reach(root)
assert seen==set(nodes)
leaves=sorted(ends); low=min(leaves)
rows=sorted(set(moves.values()))
ix={r:i for i,r in enumerate(rows)}
primes=sorted(set(p for a,b,_ in rows for m in [a,b] for p in fac(m)))
prefix=['import NoeMoves','import Mathlib.Tactic.NormNum.Prime','',f'namespace {args.module}',
'open Noe', '',f'def terminalDivisors : List ℕ := {leaves}\n',
'private theorem cons {α : Type} {P : α → Prop} {x : α} {xs : List α} (h : P x) (t : ∀ y ∈ xs, P y) : ∀ y ∈ x::xs, P y := List.forall_mem_cons.mpr ⟨h,t⟩',
'private theorem nil {α : Type} {P : α → Prop} : ∀ y ∈ ([] : List α), P y := List.forall_mem_nil _','']
def plist(xs):
    h='nil'
    for p in reversed(xs):h=f'(cons {p} {h})'
    return h
for p in primes:
    prefix+=[f'private theorem pr{p} : Nat.Prime {p} := by norm_num1']
for j,(a,b,ps) in enumerate(rows):
    A=factors(a);B=factors(b)
    prefix += [f'private theorem move{j} {{c : ℕ}} (hx : Exceptional ({a}*c)) : ∃ p ∈ ({list(ps)} : List ℕ), p ∣ c :=',
    f'  checked_guard {a} {b} {list(ps)} {A} {B} (by decide +kernel) (by decide +kernel)',
    '    '+plist([f'pr{p}' for p in A+B])+' (by decide +kernel) hx','']
for j,g in enumerate(leaves):
    prefix+=[f'private theorem node{g} : Covered terminalDivisors {g} := terminal (by decide +kernel)']
for a,(ps,b) in sorted(nodes.items(),reverse=True):
    r=moves[a];q=a//r[0]
    hs=plist([f'⟨by decide +kernel, node{a*p}⟩' for p in ps])
    prefix+=[f'private theorem node{a} : Covered terminalDivisors {a} :=',
             f'  ascend (q:={q}) (@move{ix[r]}) (by decide +kernel) {hs}']
prefix += ['', '''theorem covered {n : ℕ} (h : Exceptional n) : ∃ d ∈ terminalDivisors, d ∣ n :=
  node3261636 h (sylvester_divisor h)''',
f'theorem terminal_floor : ∀ d ∈ terminalDivisors, {low} ≤ d := by decide +kernel',
f'theorem exceptional_lower {{n : ℕ}} (h : Exceptional n) : {low} ≤ n := by',
'  obtain ⟨d,mem,div⟩ := covered h','  exact (terminal_floor d mem).trans (Nat.le_of_dvd h.1 div)',
f'theorem bounded {{n : ℕ}} (h : 0 < n) (limit : n < {low}) :',
'    ∃ m, m ≠ n ∧ m ≤ 2*n ∧ m.totient = n.totient := witness_below h limit exceptional_lower',
'',f'end {args.module}','']
out=args.data.parent/(args.module+'.lean');out.write_text('\n'.join(prefix))
print('module',args.module,'nodes',len(nodes),'normalized moves',len(rows),'terminal divisors',len(leaves),'actual minimum',low)
