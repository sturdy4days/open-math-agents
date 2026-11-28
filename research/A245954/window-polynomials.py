"""Compute both counting polynomials by inclusion-exclusion on position pairs."""
from itertools import combinations
from math import comb
from pathlib import Path
import json

def coefficients(length,width):
    edges=[(i,j) for i,j in combinations(range(length),2) if j-i<width]
    windows=[]
    for start in range(length-width+1):
        windows.append(sum(1<<b for b,(i,j) in enumerate(edges) if start<=i<j<start+width))
    size=1<<len(edges)
    mobius=[int(all(mask & window for window in windows)) for mask in range(size)]
    for b in range(len(edges)):
        for mask in range(size):
            if mask>>b&1:
                mobius[mask]-=mobius[mask^(1<<b)]
    even=[0]*(length+1)
    odd=[0]*(length+1)
    for mask,c in enumerate(mobius):
        if not c:
            continue
        adj=[[] for _ in range(length)]
        for b,(i,j) in enumerate(edges):
            if mask>>b&1:
                adj[i].append(j)
                adj[j].append(i)
        colors=[None]*length
        bip=0
        nonbip=0
        for root in range(length):
            if colors[root] is not None:
                continue
            colors[root]=0
            queue=[root]
            consistent=True
            for i in queue:
                for j in adj[i]:
                    if colors[j] is None:
                        colors[j]=1-colors[i]
                        queue.append(j)
                    elif colors[i]==colors[j]:
                        consistent=False
            bip+=consistent
            nonbip+=not consistent
        even[bip]+=c
        if not nonbip:
            odd[bip]+=c
    def ordinary(coeffs):
        return [sum(coeffs[r]*comb(r,j) for r in range(j,len(coeffs))) for j in range(len(coeffs))]
    return {'length':length,'window':width,'edgeSets':size,
            'nonzeroWeights':sum(c!=0 for c in mobius),'coefficientsEven':ordinary(even),'coefficientsOdd':ordinary(odd)}

def verify():
    a=coefficients(7,4)
    assert a['coefficientsEven']==[1,34,6,-16,66,15,0,0]
    assert a['coefficientsOdd']==[58,57,-80,-28,66,15,0,0]
    b=coefficients(5,5)
    assert b['coefficientsEven']==[1,-5,30,-5,10,0]
    assert b['coefficientsOdd']==[-15,20,20,-5,10,0]
    data={'A245954':a,'A246893':b}
    Path(__file__).with_name('window-polynomials.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data))

if __name__=='__main__':
    verify()
