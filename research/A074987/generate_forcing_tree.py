"""Reproduce prime-tree-1000.json with Python 3 and SymPy."""

from itertools import combinations
import json
from math import prod
from pathlib import Path

from sympy import isprime


def candidates(primes, multiplier):
    """List the first factorization found for each new admissible prime."""
    found = {}
    for count in range(len(primes) + 1):
        for factors in combinations(primes, count):
            product = prod(factors)
            for coefficient in (6, multiplier):
                prime = coefficient * product + 1
                if prime not in primes and prime not in found and isprime(prime):
                    found[prime] = (coefficient, product, list(factors))
    return found


def make_branch(multiplier):
    nodes = {7: None, 43: None}
    seed_count = 12
    while len(nodes) < seed_count:
        available = candidates(sorted(nodes), multiplier)
        if not available:
            raise ValueError("No admissible primes left while building the seed set")
        for prime in sorted(available)[:seed_count - len(nodes)]:
            nodes[prime] = available[prime]

    leaves = candidates(sorted(nodes), multiplier)
    divisor = 36 * prod(prime**2 for prime in nodes)
    for prime in sorted(leaves, reverse=True):
        if divisor > 10**1000:
            break
        nodes[prime] = leaves[prime]
        divisor *= prime**2
    if divisor <= 10**1000:
        raise ValueError("The product of the certified prime squares is too small")
    return {"nodes": list(nodes.items()), "divisor": str(divisor)}


if __name__ == "__main__":
    branches = {str(coefficient): make_branch(coefficient) for coefficient in (12, 18)}
    Path("prime-tree-1000.json").write_text(json.dumps(branches))
