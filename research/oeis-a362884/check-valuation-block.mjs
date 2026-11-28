// Run with: node check-valuation-block.mjs
// Independently checks the finite modular arithmetic in TheSil's A276175
// 44-step return calculation and the resulting A362884 valuation bounds.
// Source: https://github.com/TheSil/mse_1905063/blob/2e5b1c397ae89af800c4aee585a9d0eac982d962/proof.tex#L235-L360
// A362884Reduction.lean proves the block iteration and dyadic denominator results.
// Turning these finite calculations into a Lean proof of blockReturn remains open.

import assert from 'node:assert/strict';
import { performance } from 'node:perf_hooks';

const period = 44;
const sequenceValuations = [
  0, 0, 0, 0, 3, 2, 1, 0, 2, 3, 4,
  0, 0, 0, 0, 3, 2, 1, 0, 2, 3, 4,
  0, 0, 0, 0, 4, 3, 2, 0, 1, 2, 3,
  0, 0, 0, 0, 4, 3, 2, 0, 1, 2, 3,
];
const successorValuations = [
  1, 1, 1, 1, 0, 0, 0, 5, 0, 0, 0,
  2, 1, 1, 1, 0, 0, 0, 5, 0, 0, 0,
  2, 1, 1, 2, 0, 0, 0, 5, 0, 0, 0,
  1, 1, 1, 2, 0, 0, 0, 5, 0, 0, 0,
];
assert.equal(sequenceValuations.length, period);
assert.equal(successorValuations.length, period);

const variableCount = 4;
const radix = 128;
const exponents = Array.from({ length: variableCount }, (_, index) => radix ** index);
const constant = 0;
const one = new Map([[constant, 1n]]);
const two = new Map([[constant, 2n]]);

// Monomial keys encode the four exponents in base radix. Each product checks
// that adding the exponent vectors cannot carry across those digits.
function degreeIn(polynomial, variable) {
  let degree = 0;
  for (const key of polynomial.keys()) {
    degree = Math.max(degree, Math.floor(key / exponents[variable]) % radix);
  }
  return degree;
}

function powerOfTwo(bits) {
  assert(Number.isSafeInteger(bits) && bits >= 0, `invalid precision ${bits}`);
  return 1n << BigInt(bits);
}

function add(precision, left, right, rightSign = 1n) {
  const mask = powerOfTwo(precision) - 1n;
  const result = new Map();
  for (const [key, coefficient] of left) {
    const reduced = coefficient & mask;
    if (reduced !== 0n) result.set(key, reduced);
  }
  for (const [key, coefficient] of right) {
    const reduced = ((result.get(key) ?? 0n) + rightSign * coefficient) & mask;
    if (reduced === 0n) result.delete(key);
    else result.set(key, reduced);
  }
  return result;
}

let pairProducts = 0;

function multiply(precision, left, right) {
  for (let variable = 0; variable < variableCount; variable++) {
    assert(degreeIn(left, variable) + degreeIn(right, variable) < radix,
      'monomial exponent exceeds the encoding radix');
  }
  const mask = powerOfTwo(precision) - 1n;
  const result = new Map();
  pairProducts += left.size * right.size;
  for (const [leftKey, leftCoefficient] of left) {
    for (const [rightKey, rightCoefficient] of right) {
      const product = (leftCoefficient * rightCoefficient) & mask;
      if (product === 0n) continue;
      const key = leftKey + rightKey;
      const reduced = ((result.get(key) ?? 0n) + product) & mask;
      if (reduced === 0n) result.delete(key);
      else result.set(key, reduced);
    }
  }
  return result;
}

function invertUnit(precision, polynomial) {
  // Newton's update doubles the precision of the inverse at each iteration.
  let bits = 1;
  let inverse = one;
  while (bits < precision) {
    bits = Math.min(2 * bits, precision);
    const product = multiply(bits, polynomial, inverse);
    inverse = multiply(bits, inverse, add(bits, two, product, -1n));
  }
  const witness = multiply(precision, polynomial, inverse);
  assert.equal(witness.size, 1, 'inverse leaves nonconstant terms');
  assert.equal(witness.get(constant), 1n, 'inverse has wrong constant product');
  return inverse;
}

function valuationAt(valuations, index) {
  return valuations[((index % period) + period) % period];
}

const w = (index) => valuationAt(sequenceValuations, index);
const t = (index) => valuationAt(successorValuations, index);

function normalizeFactor(jet, index) {
  const scaled = new Map();
  for (const [key, coefficient] of jet.polynomial) {
    scaled.set(key, coefficient * powerOfTwo(w(index)));
  }
  const precision = jet.precision + w(index) - t(index);
  assert(precision >= 1, `factor ${index} has insufficient precision`);
  const divisor = powerOfTwo(t(index));
  const numerator = add(precision + t(index), scaled, one);
  const polynomial = new Map();
  for (const [key, coefficient] of numerator) {
    assert.equal(coefficient % divisor, 0n, `factor ${index} division is inexact`);
    const normalized = coefficient / divisor;
    assert.equal(normalized % 2n, key === constant ? 1n : 0n,
      `factor ${index} is not the expected unit modulo 2`);
    polynomial.set(key, normalized);
  }
  assert(polynomial.has(constant), `factor ${index} has no odd constant coefficient`);
  return { precision, polynomial };
}

const start = performance.now();
const jets = exponents.map((variable) => ({
  precision: 34,
  polynomial: new Map([[constant, 1n], [variable, 16n]]),
}));

// The jets represent c_n / 2^w(n). The recurrence uses the product of
// (1 + c_j) / 2^t(j) for the next three indices and the inverse of the current jet.
for (let index = 0; index < period; index++) {
  assert.equal(w(index + 4) + w(index), t(index + 1) + t(index + 2) + t(index + 3),
    `valuation balance fails at ${index}`);
  const factors = [1, 2, 3].map((offset) => normalizeFactor(jets[index + offset], index + offset));
  const denominator = jets[index];
  const precision = Math.min(denominator.precision, ...factors.map((factor) => factor.precision));
  const numerator = factors.reduce((product, factor) => multiply(precision, product, factor.polynomial), one);
  const polynomial = multiply(precision, numerator, invertUnit(precision, denominator.polynomial));
  jets.push({ precision, polynomial });
}

for (const [index, jet] of jets.entries()) {
  assert(jet.precision >= 1, `jet ${index} has insufficient precision`);
  assert.equal((jet.polynomial.get(constant) ?? 0n) % 2n, 1n, `jet ${index} is not an odd unit`);
  for (const [key, coefficient] of jet.polynomial) {
    if (key !== constant) assert.equal(coefficient % 2n, 0n, `jet ${index} changes parity`);
  }
  if (w(index) > 0) {
    assert.equal(t(index), 0, `1 + c_${index} must be odd`);
    continue;
  }
  assert(jet.precision > t(index), `jet ${index} cannot distinguish the claimed valuation`);
  const modulus = powerOfTwo(t(index) + 1);
  const coefficient = jet.polynomial.get(constant) ?? 0n;
  assert.equal((1n + coefficient) % modulus, powerOfTwo(t(index)),
    `constant term disagrees with t_${index}`);
  for (const [key, value] of jet.polynomial) {
    if (key !== constant) assert.equal(value % modulus, 0n, `perturbation changes t_${index}`);
  }
}

const returnPrecisions = [];
for (let offset = 0; offset < variableCount; offset++) {
  const index = period + offset;
  const { precision, polynomial } = jets[index];
  assert.equal(w(index), 0, `return jet ${index} must be unscaled`);
  assert(precision >= 4, `return jet ${index} has insufficient precision`);
  assert.equal((polynomial.get(constant) ?? 0n) % 16n, 1n, `wrong return constant at ${index}`);
  for (const [key, coefficient] of polynomial) {
    if (key !== constant) assert.equal(coefficient % 16n, 0n, `wrong return perturbation at ${index}`);
  }
  returnPrecisions.push(precision);
}

function positiveIntegerValuation(value) {
  assert(value > 0n);
  let valuation = 0;
  while (value % 2n === 0n) {
    value /= 2n;
    valuation++;
  }
  return valuation;
}

// OEIS A362884 gives alpha_n = 4 c_n c_(n-2) / (c_(n-1) (1 + c_(n-1))) for n >= 2.
// The periodic check covers every residue; alpha_0 = 2 and alpha_1 = 16 are separate.
const alphaValuations = Array.from({ length: period }, (_, index) =>
  2 + w(index) + w(index - 2) - w(index - 1) - t(index - 1));
const initialValuations = [2n, 16n].map(positiveIntegerValuation);
for (const value of [...initialValuations, ...alphaValuations]) assert(value >= 0 && value <= 5);
assert.equal(Math.min(...alphaValuations), 0);
assert.equal(Math.max(...alphaValuations), 5);

console.log(`Verified the 44-step return modulo 16 (precisions ${returnPrecisions.join(', ')}).`);
console.log(`Verified all 44 A362884 valuation residues lie between 0 and 5, plus both initial values.`);
console.log(`Computed ${pairProducts.toLocaleString('en-US')} coefficient pairs in ${((performance.now() - start) / 1000).toFixed(2)} s.`);
