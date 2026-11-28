from pathlib import Path
from collections import defaultdict
from functools import cache
import argparse,json,math,time
from sympy import factorint

p=argparse.ArgumentParser();p.add_argument('bound',type=int);p.add_argument('cap',type=int);p.add_argument('out',type=Path);args=p.parse_args()
bound,cap=args.bound,args.cap
spf=list(range(cap+1)); phi=list(range(cap+1))
for d in range(2,cap+1):
 if spf[d]==d:
  for z in range(d,cap+1,d):
   spf[z]=min(spf[z],d);phi[z]-=phi[z]//d
groups=defaultdict(list)
for i in range(1,cap+1):groups[phi[i]].append(i)
@cache
def factor(n):
 if n<=cap:
  out=[]
  while n>1:
   p=spf[n];v=0
   while n%p==0:n//=p;v+=1
   out.append((p,v))
  return tuple(out)
 return tuple(sorted((int(p),int(v)) for p,v in factorint(n).items()))
def normalize(a,b):
 A=dict(factor(a));B=dict(factor(b));S=tuple(sorted(A.keys()^B.keys()))
 if not S:return None
 q=math.prod(p**(min(v,B[p])-(v!=B[p])) for p,v in A.items() if p in B)
 return (a//q,b//q,S)
@cache
def divisors(f):
 ds=[1]
 for p,e in f:
  ds=[d*p**i for d in ds for i in range(e+1) if d*p**i<=cap]
 return ds
@cache
def local(a):
 return list(dict.fromkeys(v for b in groups[phi[a]] if b!=a and b<=2*a and (v:=normalize(a,b)) and v[0]==a))
seed={normalize(int(a),b) for a,(s,b) in json.loads(Path('noe18.json').read_text())['nodes'].items()}
def candidates(n):
 rows=set(seed)
 for d in divisors(factor(n)):rows.update(local(d))
 offers=[]
 for a,b,S in rows:
  if n%a:continue
  q=n//a
  if any(q%p==0 for p in S):continue
  child=tuple(p for p in S if n*p<bound)
  score=(sum(1/p**1.30 for p in child),len(S),len(child),a,b)
  offers.append((score,S,q*b))
 return sorted(offers)
tree={};dead=set();nodes_done=0
def solve(n):
 global nodes_done
 if n>=bound or n in tree:return True
 if n in dead:return False
 opts=candidates(n)
 for _,S,b in opts:
  if all(solve(n*p) for p in S):
   tree[n]=[S,b];return True
 dead.add(n)
 if len(dead) in [1,100,1000,10000]: print('dead factors',len(dead),n,factor(n),len(tree),flush=True)
 return False
root=3261636
ok=solve(root)
def slim(a,seen):
 if a>=bound or a in seen:return
 seen.add(a)
 for p in tree[a][0]:slim(a*p,seen)
use=set()
if ok:slim(root,use)
print('success',ok,'nodes',len(use),'search',len(tree),'blocked',len(dead),'lowest missing',min(dead) if dead else None,flush=True)
args.out.write_text(json.dumps({'bound':bound,'cap':cap,'nodes':{a:tree[a] for a in sorted(use)},'unresolved':[] if ok else sorted(dead),'seed':sorted(seed)}))
