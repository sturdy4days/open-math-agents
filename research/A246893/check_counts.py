"""Check the all-length formula by direct enumeration on small alphabets."""
from functools import cache
from itertools import product
from math import perm
from pathlib import Path
import json

@cache
def stirling(k, r):
    if not k or not r:
        return int(k == r)
    return stirling(k-1,r-1) + r*stirling(k-1,r)

def paired(m,k):
    return sum(perm(m,r)*2**r*stirling(k,r) for r in range(m+1))

def complement_free(n,word):
    seen=set()
    for x in word:
        if n-x in seen:
            return False
        seen.add(x)
    return True

rows=[]
word_count=0
for n in range(7):
    counts=[]
    for k in range(7):
        m=(n+1)//2
        expected=paired(m,k) + (k*paired(m,max(0,k-1)) if n%2==0 else 0)
        actual=sum(complement_free(n,w) for w in product(range(n+1),repeat=k))
        assert actual==expected, (n,k,actual,expected)
        word_count+=(n+1)**k
        counts.append(actual)
    rows.append(counts)
data={'n':list(range(7)),'k':list(range(7)),'wordsExamined':word_count,'complementFree':rows}
(Path(__file__).with_name('brute-counts.json')).write_text(json.dumps(data,indent=2)+'\n')
print('Counts matched on',word_count,'words in 49 length/alphabet combinations.')
