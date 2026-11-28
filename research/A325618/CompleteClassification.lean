import OMAStatements.S_oeis_a325618

/-!
# The largest exception to OEIS A325618

This proves Charlie Neder's 2019 conjecture (https://oeis.org/A325618) in the formulation
contributed by @warshanks. Formal proof by @sturdy4days.

Replacing one k by k+1 copies of k+1 preserves the reciprocal factorial sum. Retaining
four equal parts lets the resulting ordinary sums fill contiguous intervals. Finite
partitions start this induction at seven. A separate exhaustive recursion, with an upper
bound on the remaining reciprocal mass, rules out 137. The converse constructs a partition
from every successful branch. Together these give the exact finite complement below 138.
-/

namespace OMA.S_oeis_a325618

/-- A reciprocal-factorial partition with four designated copies of the level k. -/
def Grow (k m : ℕ) : Prop :=
  ∃ R : Multiset ℕ, (∀ x ∈ R, 0 < x) ∧ R.sum + 4*k = m ∧
    (R.map fun x => (1 : ℚ)/(x.factorial : ℚ)).sum + 4/(k.factorial : ℚ) = 1

theorem term_of_list (l : List ℕ) {m : ℕ} (positive : ∀ x ∈ l, 0 < x)
    (size : l.sum = m) (mass : (l.map fun x => (1 : ℚ)/(x.factorial : ℚ)).sum = 1) :
    IsTerm m := by
  refine ⟨⟨(l : Multiset ℕ), ?_, ?_⟩, ?_⟩
  · intro x hx; exact positive x hx
  · simpa using size
  · exact mass

end OMA.S_oeis_a325618

namespace OMA.S_oeis_a325618

private def jump (k : ℕ) := k*k+k+1

private theorem grow_term {k m : ℕ} (hk : 0 < k) (g : Grow k m) : IsTerm m := by
  obtain ⟨R, pos, size, mass⟩ := g
  refine ⟨⟨R + Multiset.replicate 4 k, ?_, ?_⟩, ?_⟩
  · intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact pos x h
    · have := Multiset.eq_of_mem_replicate h; omega
  · simpa only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_ofNat] using size
  · change ((R + Multiset.replicate 4 k).map _).sum = 1
    simpa only [Multiset.map_add, Multiset.map_replicate, Multiset.sum_add,
      Multiset.sum_replicate,nsmul_eq_mul,div_eq_mul_inv,one_mul,Nat.cast_ofNat] using mass

private theorem split_four {k n : ℕ} (hk : 3 ≤ k) (g : Grow k n)
    (q : ℕ) (lo : 1 ≤ q) (hi : q ≤ 4) : Grow (k+1) (n + q*jump k) := by
  obtain ⟨R, pos, size, mass⟩ := g
  have enough : 4 ≤ (k+1)*q := by nlinarith [Nat.mul_le_mul_left (k+1) lo]
  refine ⟨R + Multiset.replicate (4-q) k +
    Multiset.replicate ((k+1)*q-4) (k+1), ?_, ?_, ?_⟩
  · intro x h
    rcases Multiset.mem_add.mp h with h | h
    · rcases Multiset.mem_add.mp h with h | h
      · exact pos x h
      · have := Multiset.eq_of_mem_replicate h; omega
    · have := Multiset.eq_of_mem_replicate h; omega
  · simp only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul]
    dsimp [jump]
    rw [Nat.sub_mul, Nat.sub_mul]
    have hkq : q*k ≤ 4*k := Nat.mul_le_mul_right k hi
    have hqq : 4*(k+1) ≤ ((k+1)*q)*(k+1) := Nat.mul_le_mul_right (k+1) enough
    zify [hkq,hqq] at size ⊢
    nlinarith
  · simp only [Multiset.map_add, Multiset.map_replicate, Multiset.sum_add,
      Multiset.sum_replicate,nsmul_eq_mul]
    push_cast [Nat.cast_sub hi, Nat.cast_sub enough, Nat.factorial_succ]
    have fac : (k.factorial : ℚ) ≠ 0 := by positivity
    have succ : (k : ℚ)+1 ≠ 0 := by positivity
    field_simp [fac,succ] at mass ⊢
    linear_combination ((k : ℚ)+1) * mass

/-- Once each target in a jump-length interval admits four copies of k, the next interval
is covered by splitting between one and four of them. -/
private theorem grow_interval {a k : ℕ} (hk : 3 ≤ k)
    (seed : ∀ n, a ≤ n → n < a + jump k → Grow k n) :
    ∀ m, a + jump k ≤ m → m < a + jump k + jump (k+1) → Grow (k+1) m := by
  intro m lo hi
  have big : jump (k+1) ≤ 4 * jump k := by unfold jump; nlinarith
  have single (q : ℕ) (minq : 1 ≤ q) (maxq : q ≤ 4)
      (low : a + q * jump k ≤ m) (high : m < a + q * jump k + jump k) :
      Grow (k+1) m := by
    have base := seed (m-q*jump k) (by omega) (by omega)
    have built := split_four hk base q minq maxq
    rwa [Nat.sub_add_cancel (by omega : q*jump k ≤ m)] at built
  by_cases b : m < a + 2 * jump k
  · apply single 1 (by decide) (by decide) <;> omega
  by_cases c : m < a + 3 * jump k
  · apply single 2 (by decide) (by decide) <;> omega
  by_cases d : m < a + 4 * jump k
  · apply single 3 (by decide) (by decide) <;> omega
  · apply single 4 (by decide) (by decide) <;> omega

/-- The consecutive intervals start at 211. Each step advances the left endpoint by
exactly the width of the preceding interval, so their union has no gaps. -/
theorem propagation
    (base : ∀ m, 138 ≤ m → m < 211 → IsTerm m)
    (seed : ∀ m, 211 ≤ m → m ≤ 267 → Grow 7 m) :
    ∀ m, 137 < m → IsTerm m := by
  have stages (t : ℕ) : ∃ a : ℕ, t ≤ a ∧
      (∀ m, 138 ≤ m → m < a → IsTerm m) ∧
      (∀ m, a ≤ m → m < a + jump (t+7) → Grow (t+7) m) := by
    induction t with
    | zero =>
      exact ⟨211, by decide, base, fun m hm h => seed m hm (by norm_num [jump] at h; omega)⟩
    | succ t ih =>
      obtain ⟨a, reached, previous, available⟩ := ih
      have pos : 0 < jump (t+7) := by unfold jump; omega
      refine ⟨a+jump (t+7), by omega, ?_, ?_⟩
      · intro m hm high
        by_cases earlier : m < a
        · exact previous m hm earlier
        · exact grow_term (by omega) (available m (by omega) high)
      · exact grow_interval (by omega) available
  intro m h
  obtain ⟨a, reached, previous, _⟩ := stages (m+1)
  exact previous m (by omega) (by omega)

end OMA.S_oeis_a325618

namespace OMA.S_oeis_a325618

private def baseLists : List (List ℕ) := [
[4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5],
[2,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[3,3,3,4,4,4,4,4,4,4,4,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,3,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[2,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[3,3,3,3,3,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,3,3,4,4,5,5,5,5,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,7,7],
[3,3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,3,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,3,3,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,3,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,3,3,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7],
[3,3,3,3,4,4,4,4,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,7,7],
[3,3,3,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,3,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,4,4,4,4,4,4,4,4,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[3,3,3,3,3,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,7,7],
[2,3,3,4,4,4,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,3,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,4,4,4,4,4,4,4,4,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,3,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,3,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,3,3,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7],
[3,3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,3,3,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,4,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[3,3,3,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,3,4,4,4,4,4,4,4,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,3,3,4,4,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,3,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,3,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[2,4,4,4,4,4,4,4,4,4,4,4,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[3,3,3,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7],
[2,3,3,4,4,4,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,4,4,4,4,4,4,4,4,4,4,4,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,3,4,4,4,4,4,4,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,3,3,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[2,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[2,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6],
[3,3,3,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6],
[3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5],
[3,3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6]]

private def seedsLists : List (List ℕ) := [
[3,3,3,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,4,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,7,7,7],
[2,3,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,4,5,5,5,5,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,4,4,4,4,4,4,4,4,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[3,3,3,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[3,3,3,3,3,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[3,3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,5,5,5,5,5,5,5,5,5,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,7,7,7],
[2,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[3,3,3,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[3,3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,7,7,7],
[3,3,3,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,4,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,4,5,5,5,5,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,4,4,4,4,4,4,4,4,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[3,3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,4,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[2,3,3,4,4,4,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,3,4,4,4,4,4,4,4,5,5,5,5,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[2,4,4,4,4,4,4,4,4,4,4,4,5,5,5,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7],
[3,3,3,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7],
[3,3,3,3,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7],
[2,3,3,4,4,4,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7]]

def witnessList (i : ℕ) (seed : Bool) : List ℕ :=
  if seed then seedsLists.getD i [] else baseLists.getD i []

def witnessed (l : List ℕ) (m w : ℕ) : Prop :=
  (∀ x ∈ l, 0<x) ∧ l.sum + 7*w = m ∧
    (l.map (fun x => (1:ℚ)/(x.factorial:ℚ))).sum + (w:ℚ)/(Nat.factorial 7:ℚ) = 1

instance (l : List ℕ) (m w : ℕ) : Decidable (witnessed l m w) := by
  unfold witnessed
  infer_instance

theorem checkedBase : ∀ i : Fin 73, witnessed (witnessList i.val false) (138+i.val) 0 := by
  decide +kernel

theorem checkedSeeds : ∀ i : Fin 57, witnessed (witnessList i.val true) (211+i.val) 4 := by
  decide +kernel

end OMA.S_oeis_a325618

namespace OMA.S_oeis_a325618

theorem base_terms (m : ℕ) (lo : 138 ≤ m) (hi : m < 211) : IsTerm m := by
  let i : Fin 73 := ⟨m-138,by omega⟩
  have mk : 138+i.val=m := by dsimp [i]; omega
  obtain ⟨pos,sz,sm⟩ := checkedBase i
  apply term_of_list (witnessList i.val false) pos
  · simpa only [Nat.mul_zero,add_zero,mk] using sz
  · simpa using sm

theorem seed_terms (m : ℕ) (lo : 211 ≤ m) (hi : m ≤ 267) : Grow 7 m := by
  let i : Fin 57 := ⟨m-211,by omega⟩
  have mk : 211+i.val=m := by dsimp [i]; omega
  obtain ⟨pos,sz,sm⟩ := checkedSeeds i
  refine ⟨(witnessList i.val true : Multiset ℕ),fun x hx => pos x hx,?_,?_⟩
  · change (witnessList i.val true).sum+4*7 = m
    simpa only [mk,Nat.mul_comm 4 7] using sz
  · exact sm

end OMA.S_oeis_a325618

namespace OMA.S_oeis_a325618

private def mass (S : Multiset ℕ) : ℚ :=
  (S.map (fun i => (1 : ℚ) / (i.factorial : ℚ))).sum

private theorem mass_cons (i : ℕ) (S : Multiset ℕ) :
    mass (i ::ₘ S) = 1 / (i.factorial : ℚ) + mass S := by simp [mass]

private theorem mass_nonneg (S : Multiset ℕ) : 0 ≤ mass S := by
  induction S using Multiset.induction_on with
  | empty => simp [mass]
  | cons x S ih =>
    rw [mass_cons]
    positivity

/-- With all remaining parts at least k, each unit of k! times the remaining
reciprocal sum consumes at least k units of the partition's total. -/
private theorem mass_budget (k : ℕ) (S : Multiset ℕ) (lower : ∀ x ∈ S, k ≤ x) :
    (k : ℚ) * k.factorial * mass S ≤ (S.sum : ℚ) := by
  induction S using Multiset.induction_on with
  | empty => simp [mass]
  | cons x S ih =>
    have hkx := lower x (Multiset.mem_cons_self _ _)
    have h₁ : (k : ℚ) ≤ x := by exact_mod_cast hkx
    have h₂ : (k.factorial : ℚ) ≤ x.factorial := by exact_mod_cast Nat.factorial_le hkx
    have h₃ : (0 : ℚ) < x.factorial := by exact_mod_cast Nat.factorial_pos x
    have unit : (k : ℚ)*k.factorial*(1/(x.factorial : ℚ)) ≤ x := by
      rw [← mul_div_assoc, mul_one, div_le_iff₀ h₃]
      exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
    rw [mass_cons, mul_add, Multiset.sum_cons, Nat.cast_add]
    exact add_le_add unit (ih (fun y hy => lower y (Multiset.mem_cons_of_mem hy)))

/-- m is the remaining budget and u is the remaining mass in units of 1/k!.
Either a part k is present, or every remaining part is larger. -/
private def fits : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, m, u => decide (m=0 ∧ u=0)
  | f+1, k, m, u =>
    if m=0 then decide (u=0)
    else if k>m ∨ u=0 ∨ m<k*u then false
    else fits f (k+1) m ((k+1)*u) || fits f k (m-k) (u-1)

private theorem fits_of_parts (f k u : ℕ) (S : Multiset ℕ) (hk : 0<k)
    (lower : ∀ x ∈ S, k ≤ x) (units : (u : ℚ) = k.factorial * mass S)
    (fuel : 2*S.sum < f+k) : fits f k S.sum u = true := by
  by_cases null : S=0
  · subst S
    have hu : u=0 := by simpa [mass] using units
    cases f <;> simp [fits,hu]
  obtain ⟨x,hx⟩ := Multiset.exists_mem_of_ne_zero null
  have ks := (lower x hx).trans (Multiset.le_sum_of_mem hx)
  have ms : 0 < mass S := by
    rw [← Multiset.cons_erase hx, mass_cons]
    exact add_pos_of_pos_of_nonneg (by positivity) (mass_nonneg _)
  have hu : 0<u := by
    have upos : (0 : ℚ) < u := by rw [units]; positivity
    exact_mod_cast upos
  have budget : k*u ≤ S.sum := by
    have hb := mass_budget k S lower
    rw [mul_assoc, ← units] at hb
    exact_mod_cast hb
  cases f with
  | zero => omega
  | succ f =>
    have nonzero : S.sum ≠ 0 := by omega
    have viable : ¬(k>S.sum ∨ u=0 ∨ S.sum<k*u) := by omega
    simp only [fits,if_neg nonzero,if_neg viable,Bool.or_eq_true]
    by_cases hit : k ∈ S
    · right
      let T := S.erase k
      have restore : k ::ₘ T = S := Multiset.cons_erase hit
      have sm : k+T.sum = S.sum := by rw [← restore,Multiset.sum_cons]
      have sum' : S.sum-k=T.sum := by omega
      rw [sum']
      apply fits_of_parts f k (u-1) T hk (fun y hy => lower y (Multiset.erase_subset k S hy))
      · rw [Nat.cast_sub (by omega),Nat.cast_one,units,← restore,mass_cons,mul_add]
        have fac : (k.factorial : ℚ) ≠ 0 := by positivity
        field_simp
        ring
      · omega
    · left
      apply fits_of_parts f (k+1) ((k+1)*u) S (by omega)
      · intro y hy
        have := lower y hy
        have : y ≠ k := fun h => hit (h ▸ hy)
        omega
      · rw [Nat.cast_mul,units,Nat.factorial_succ,Nat.cast_mul,mul_assoc]
      · omega
termination_by f

private theorem no_budget_137 : fits 274 1 137 1 = false := by decide

theorem not_term_137 : ¬IsTerm 137 := by
  rintro ⟨p,hp⟩
  have units : (1 : ℚ) = (Nat.factorial 1 : ℚ)*mass p.parts := by
    change mass p.parts = 1 at hp
    simp [hp]
  have yes := fits_of_parts 274 1 1 p.parts (by decide)
    (fun _ h => p.parts_pos h) units (by rw [p.parts_sum]; decide)
  rw [p.parts_sum,no_budget_137] at yes
  contradiction

/-- Every successful branch constructs a multiset with exactly the given budget
and reciprocal-factorial sum. -/
private theorem parts_of_fits (f k m u : ℕ) (hk : 0 < k)
    (h : fits f k m u = true) : ∃ S : Multiset ℕ, (∀ x ∈ S, k ≤ x) ∧ S.sum = m ∧
      (u : ℚ) = k.factorial * mass S := by
  induction f generalizing k m u with
  | zero =>
    simp only [fits,decide_eq_true_eq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨0,by simp,by simp,by simp [mass]⟩
  | succ f ih =>
    by_cases zero : m=0
    · subst m
      have hu : u=0 := by simpa [fits] using h
      subst u
      exact ⟨0,by simp,by simp,by simp [mass]⟩
    by_cases bad : k>m ∨ u=0 ∨ m<k*u
    · simp [fits,zero,bad] at h
    simp only [fits,if_neg zero,if_neg bad,Bool.or_eq_true] at h
    rcases h with hs|hp
    · obtain ⟨S,lo,budget,hunits⟩ := ih _ _ _ (by omega) hs
      refine ⟨S,fun x hx => (Nat.le_succ k).trans (lo x hx),budget,?_⟩
      rw [Nat.cast_mul,Nat.factorial_succ,Nat.cast_mul,mul_assoc] at hunits
      exact mul_left_cancel₀ (by positivity : ((k+1 : ℕ) : ℚ) ≠ 0) hunits
    · obtain ⟨S,lo,budget,hunits⟩ := ih _ _ _ hk hp
      refine ⟨k ::ₘ S,?_,?_,?_⟩
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl|hx
        · rfl
        · exact lo x hx
      · rw [Multiset.sum_cons,budget]
        omega
      · have hu : 1 ≤ u := by omega
        rw [Nat.cast_sub hu, Nat.cast_one] at hunits
        rw [mass_cons,mul_add, ← hunits]
        have fac : (k.factorial : ℚ) ≠ 0 := by positivity
        field_simp
        ring

/-- An exact integer decision procedure for the partition problem at every weight. -/
def partitionDecision (m : ℕ) : Bool := fits (2*m) 1 m 1

theorem isTerm_iff_decision (m : ℕ) : IsTerm m ↔ partitionDecision m = true := by
  constructor
  · rintro ⟨p,hp⟩
    have units : (1 : ℚ) = (Nat.factorial 1 : ℚ)*mass p.parts := by
      change mass p.parts = 1 at hp
      simp [hp]
    have yes := fits_of_parts (2*m) 1 1 p.parts (by decide)
      (fun _ h => p.parts_pos h) units (by rw [p.parts_sum]; omega)
    simpa only [partitionDecision,p.parts_sum] using yes
  · intro success
    obtain ⟨S,lower,budget,units⟩ := parts_of_fits (2*m) 1 m 1 (by decide) success
    refine ⟨⟨S,fun hx => lower _ hx,budget⟩,?_⟩
    simpa [recipFactorialSum,mass] using units.symm

def exceptions : List ℕ := [0, 2, 3, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 46, 47, 48, 49, 51, 53, 54, 55, 56, 59, 60, 61, 62, 63, 64, 67, 68, 69, 72, 74, 75, 77, 80, 81, 82, 84, 85, 88, 90, 93, 95, 98, 101, 103, 105, 106, 111, 116, 124, 129, 136, 137]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
private theorem finite_decisions : ∀ m : Fin 138, partitionDecision m = decide (m.val ∉ exceptions) := by decide +kernel

theorem exact_complement (m : ℕ) :
    IsTerm m ↔ m ∉ exceptions := by
  by_cases small : m<138
  · have eq := finite_decisions ⟨m,small⟩
    rw [isTerm_iff_decision,eq,decide_eq_true_eq]
  · have bound : ∀ x ∈ exceptions, x < 138 := by decide
    exact ⟨fun _ h => small (bound m h),fun _ => propagation base_terms seed_terms m (by omega)⟩

end OMA.S_oeis_a325618


theorem OMA.solution : type_of% @OMA.S_oeis_a325618.main :=
  ⟨OMA.S_oeis_a325618.not_term_137,
    OMA.S_oeis_a325618.propagation OMA.S_oeis_a325618.base_terms OMA.S_oeis_a325618.seed_terms⟩
