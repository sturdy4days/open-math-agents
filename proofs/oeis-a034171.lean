import OMAStatements.S_oeis_a034171

/-!
# A counterexample to the A034171 supercongruence

Peter Bala's published exception set is finite for each prime. With the
offset-one indexing used in the conjecture, @Solfanbtc observed during the
formalization stage that the prime 7 and index 50 give a counterexample.
We evaluate the two factorial quotients in the original definition modulo 49.
-/

namespace TripleFactorial
open OMA.S_oeis_a034171

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem counterexample : a 50 % 49 = 17 ∧ a 350 % 49 = 31 := by
  decide +kernel

end TripleFactorial

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a034171.main) := by
  intro claim
  have outside : ¬ OMA.S_oeis_a034171.excluded 7 50 := by
    rintro ⟨m,k,hm,hk,hk',e⟩
    omega
  have h := claim 7 50 (by decide) (by decide) (by decide) outside
  rw [show (7 : ℕ) * 50 = 350 from rfl,show (7 : ℕ) ^ 2 = 49 from rfl] at h
  unfold Nat.ModEq at h
  obtain ⟨left,right⟩ := TripleFactorial.counterexample
  rw [right,left] at h
  exact (by decide : (31 : ℕ) ≠ 17) h
