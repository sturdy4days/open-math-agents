import OMAStatements.S_oeis_a074987

/-!
# Bounded witnesses for T. D. Noe’s conjecture on equal totients

The project formulation is by @FFD-007. The initial prime-square forcing
argument adapts the classical Carmichael divisibility method to replacements
within a factor of two. Each proof-tree move certifies its numerical size bound,
equality of totients, and the exceptional prime overlaps after scaling.

https://oeis.org/A074987
https://doi.org/10.1090/S0025-5718-1994-1226815-3
-/

namespace Noe

/-- No distinct preimage at or below twice the given argument. -/
def Exceptional (n : ℕ) : Prop :=
  0 < n ∧ ∀ m, m ≤ 2*n → m.totient=n.totient → m=n

private theorem scale_saturated (a : ℕ) {u : ℕ} (pos : 0<a)
    (all : ∀ q, q.Prime → q ∣ a → q ∣ u) : (a*u).totient = a*u.totient := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases one : a=1
    · simp [one]
    obtain ⟨p,hp,v,hv⟩ := Nat.exists_prime_and_dvd one
    have vpos : 0<v := Nat.pos_of_dvd_of_pos (hv ▸ dvd_mul_left _ _) pos
    have small : v<a := by rw [hv]; simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt vpos
    have pu := all p hp (hv ▸ dvd_mul_right _ _)
    have rest := ih v small vpos (fun q hq qv => all q hq (qv.trans (hv ▸ dvd_mul_left _ _)))
    rw [hv,mul_assoc,Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_right pu _),rest,mul_assoc]

private theorem replace_prime {p u : ℕ} (prime : p.Prime) (absent : ¬p ∣ u)
    (all : ∀ q, q.Prime → q ∣ p - 1 → q ∣ u) :
    ((p - 1)*u).totient = (p*u).totient := by
  have bigger := prime.two_le
  rw [scale_saturated _ (by omega) all, Nat.totient_mul_of_prime_of_not_dvd prime absent]

/-- If the other-inverse bound fails at (p−1)u and all primes of p−1 already
divide u, both copies of p are forced in the original argument. -/
theorem force_prime_square {p u : ℕ} (prime : p.Prime) (hn : Exceptional ((p - 1)*u))
    (all : ∀ q, q.Prime → q ∣ p - 1 → q ∣ u) : p^2 ∣ (p - 1)*u := by
  obtain ⟨positive,ex⟩ := hn
  have u0 : 0<u := Nat.pos_of_dvd_of_pos (dvd_mul_left _ _) positive
  have p2 := prime.two_le
  have pri : p ∣ u := by
    by_contra absent
    have small : p*u ≤ 2*((p - 1)*u) := by
      rw [←mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    have eq := ex _ small (replace_prime prime absent all).symm
    have impossible := Nat.eq_of_mul_eq_mul_right u0 eq
    omega
  obtain ⟨v,hv⟩ := pri
  let w := (p - 1)*v
  have nform : (p - 1)*u = p*w := by rw [hv]; dsimp [w]; ring
  have wpos : 0<w := Nat.pos_of_dvd_of_pos (nform ▸ dvd_mul_left _ _) positive
  have pw : p ∣ w := by
    by_contra absent
    have cover : ∀ q, q.Prime → q∣p - 1 → q∣w := fun q _ h => dvd_mul_of_dvd_left h _
    have small : (p - 1)*w ≤ 2*((p - 1)*u) := by
      calc
        (p - 1)*w ≤ p*w := Nat.mul_le_mul_right _ (by omega)
        _ = (p - 1)*u := nform.symm
        _ ≤ 2*((p - 1)*u) := by omega
    have eq := ex _ small ((replace_prime prime absent cover).trans (congrArg Nat.totient nform.symm))
    rw [nform] at eq
    have impossible := Nat.eq_of_mul_eq_mul_right wpos eq
    omega
  rw [nform,pow_two]
  exact Nat.mul_dvd_mul_left _ pw

/-- A condition expressible as divisibility alone, so the rule can iterate. -/
theorem square_from_radical {n p : ℕ} (hn : Exceptional n) (hp : p.Prime)
    (hd : (p - 1)*(∏ q ∈ (p - 1).primeFactors,q) ∣ n) : p^2 ∣ n := by
  obtain ⟨c,hc⟩ := hd
  rw [mul_assoc] at hc
  subst n
  apply force_prime_square hp hn
  intro q hq div
  have p0 := hp.two_le
  have mem : q ∈ (p - 1).primeFactors := Nat.mem_primeFactors.mpr ⟨hq,div,by omega⟩
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id mem) c

private def trigger (p : ℕ) := (p - 1) * ∏ q ∈ (p - 1).primeFactors,q

private theorem forced {n p t : ℕ} (hn : Exceptional n) (hp : p.Prime)
    (ht : trigger p=t) (d : t ∣ n) : p^2 ∣ n := square_from_radical hn hp (by change trigger p ∣ n; rwa [ht])

theorem sylvester_divisor {n : ℕ} (hn : Exceptional n) : 3261636 ∣ n := by
  have d2 : 4 ∣ n := forced hn (p:=2) (t:=1) (by decide) (by decide +kernel) (one_dvd n)
  have d3 : 9 ∣ n := forced hn (p:=3) (by decide) (by decide +kernel) d2
  have d36 : 36 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 4 9) d2 d3
  have d7 : 49 ∣ n := forced hn (p:=7) (by decide) (by decide +kernel) d36
  have d1764 : 1764 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 36 49) d36 d7
  have d43 : 1849 ∣ n := forced hn (p:=43) (by decide) (by decide +kernel) d1764
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 1764 1849) d1764 d43

end Noe

namespace TotientLocal

/-- Multiplying by c preserves equal totients if overlaps with its prime divisors agree. -/
theorem scale_same (a b c : ℕ) (h : a.totient = b.totient)
    (agree : ∀ p : ℕ, p.Prime → p ∣ c → (p ∣ a ↔ p ∣ b)) :
    (a*c).totient = (b*c).totient := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hc : c ≤ 1
    · rcases (show c=0 ∨ c=1 by omega) with rfl|rfl <;> simp [h]
    obtain ⟨p, prime, d, hd⟩ := Nat.exists_prime_and_dvd (by omega : c ≠ 1)
    have hpp := prime.one_lt
    have dsmall : d < c := by
      rw [hd] at hc ⊢
      by_cases dz : d=0
      · simp [dz] at hc
      · simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hpp (Nat.pos_of_ne_zero dz)
    have inner := ih d dsmall fun q hq qd => agree q hq (qd.trans (hd ▸ dvd_mul_left _ _))
    have cmp := agree p prime (hd ▸ dvd_mul_right _ _)
    have cm : p ∣ a*d ↔ p ∣ b*d := by simp only [prime.dvd_mul, cmp]
    rw [hd, mul_left_comm a p, mul_left_comm b p]
    by_cases ha : p ∣ a*d
    · rw [Nat.totient_mul_of_prime_of_dvd prime ha, Nat.totient_mul_of_prime_of_dvd prime (cm.mp ha),inner]
    · rw [Nat.totient_mul_of_prime_of_not_dvd prime ha, Nat.totient_mul_of_prime_of_not_dvd prime (ha ∘ cm.mpr),inner]

def fastPhi (a : ℕ) : ℕ :=
  (a / ∏ p ∈ a.primeFactors, p) * ∏ p ∈ a.primeFactors, (p - 1)

abbrev guarded (a b : ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ a.primeFactors, p ∣ b ∨ p ∈ ps) ∧
  (∀ p ∈ b.primeFactors, p ∣ a ∨ p ∈ ps)

theorem scaled_guard (a b c : ℕ) (ps : List ℕ) (a0 : 0 < a) (b0 : 0 < b)
    (equal : fastPhi a = fastPhi b) (gd : guarded a b ps)
    (avoid : ∀ p ∈ ps, ¬ p ∣ c) : (a*c).totient = (b*c).totient := by
  apply scale_same
  · simpa only [Nat.totient_eq_div_primeFactors_mul, fastPhi] using equal
  · intro p hp pc
    constructor
    · intro pa
      exact (gd.1 p (Nat.mem_primeFactors.mpr ⟨hp,pa,a0.ne'⟩)).resolve_right (fun hm => avoid p hm pc)
    · intro pb
      exact (gd.2 p (Nat.mem_primeFactors.mpr ⟨hp,pb,b0.ne'⟩)).resolve_right (fun hm => avoid p hm pc)

/-- A displayed product of primes supplies the prime divisors of a number. -/
theorem factors_of_list {a : ℕ} (P : List ℕ) (product : P.prod=a) (prime : ∀ p ∈ P, Nat.Prime p) :
    a.primeFactors = P.toFinset := by
  subst a
  induction P with
  | nil => simp
  | cons p ps ih =>
    have hp := prime p (by simp)
    have hs : ∀ q ∈ ps, Nat.Prime q := fun q h => prime q (List.mem_cons_of_mem p h)
    have pos := List.prod_pos (fun q h => (hs q h).pos)
    simp [Nat.primeFactors_mul hp.ne_zero pos.ne', hp.primeFactors,ih hs]

def formPhi (a : ℕ) (s : Finset ℕ) : ℕ :=
  (a / ∏ p ∈ s, p) * ∏ p ∈ s, (p - 1)

abbrev guardCheck (a b : ℕ) (A B : Finset ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ A, p ∣ b ∨ p ∈ ps) ∧ (∀ p ∈ B, p ∣ a ∨ p ∈ ps)


end TotientLocal

namespace Noe
open TotientLocal

/-- If neither side of a replacement gains a new prime overlap from the cofactor,
the distinct scaled witnesses still have equal totient. -/
theorem forced_guard (a b : ℕ) (ps : List ℕ) (apos : 0<a) (bpos : 0<b) (diff : b≠a)
    (bound : b≤2*a) (equal : fastPhi a=fastPhi b) (guards : guarded a b ps)
    {c : ℕ} (hn : Exceptional (a*c)) : ∃ p ∈ ps, p ∣ c := by
  by_contra! avoid
  have eqn := scaled_guard a b c ps apos bpos equal guards avoid
  have small := Nat.mul_le_mul_right c bound
  rw [Nat.mul_assoc] at small
  have same := hn.2 _ small eqn.symm
  have pos : 0<c := Nat.pos_of_dvd_of_pos (dvd_mul_left c a) hn.1
  exact diff (Nat.eq_of_mul_eq_mul_right pos same)

/-- Prime factorizations verify both equality of totients and the exceptional
primes of a local move without factoring the argument of the conjecture. -/
theorem checked_guard (a b : ℕ) (ps A B : List ℕ) (pa : A.prod=a) (pb : B.prod=b)
    (primes : ∀ p∈A++B, Nat.Prime p)
    (checks : 0<a ∧ 0<b ∧ b≠a ∧ b≤2*a ∧ formPhi a A.toFinset=formPhi b B.toFinset ∧
      guardCheck a b A.toFinset B.toFinset ps)
    {c : ℕ} (hn : Exceptional (a*c)) : ∃ p ∈ ps, p ∣ c := by
  obtain ⟨apos,bpos,diff,le,phi,gd⟩ := checks
  have ha := factors_of_list A pa (fun p hp => primes p (by simp [hp]))
  have hb := factors_of_list B pb (fun p hp => primes p (by simp [hp]))
  apply forced_guard a b ps apos bpos diff le _ _ hn
  · simpa only [fastPhi,formPhi,ha,hb] using phi
  · simpa only [guarded,guardCheck,ha,hb] using gd

def Covered (ends : List ℕ) (a : ℕ) : Prop :=
  ∀ {n : ℕ}, Exceptional n → a ∣ n → ∃ d ∈ ends, d ∣ n

theorem terminal {ends : List ℕ} {a : ℕ} (mem : a∈ends) : Covered ends a :=
  fun _ h => ⟨a,mem,h⟩

theorem ascend {ends guards : List ℕ} {a b q : ℕ}
    (move : ∀ {c : ℕ}, Exceptional (b*c) → ∃ p ∈ guards, p ∣ c)
    (entry : b*q=a)
    (next : ∀ p ∈ guards, p.Coprime q ∧ Covered ends (a*p)) : Covered ends a := by
  rintro n hn ⟨u,rfl⟩
  have eqn : a*u=b*(q*u) := by rw [← Nat.mul_assoc,entry]
  obtain ⟨p,hp,hu⟩ := move (eqn ▸ hn)
  obtain ⟨cop,succ⟩ := next p hp
  exact succ hn (Nat.mul_dvd_mul_left a (cop.dvd_of_dvd_mul_left hu))

theorem witness_below {bound n : ℕ} (positive : 0 < n) (small : n < bound)
    (major : ∀ {x : ℕ}, Exceptional x → bound ≤ x) :
    ∃ m, m≠n ∧ m≤2*n ∧ m.totient=n.totient := by
  by_contra! no
  exact (Nat.not_lt_of_ge (major ⟨positive,fun m hm heq => by_contra fun h => no m h hm heq⟩)) small

end Noe

namespace Noe18
open Noe

def terminalDivisors : List ℕ := [1450102504381627068, 1671209179095592332, 2124769406632273548, 2999318254965448668, 3228714860015041236, 365476809021422618268, 429352143586128113148, 748321944761128215996, 1746406782776939532228, 12360820158317366084916, 15715502787921172585524]

private theorem cons {α : Type} {P : α → Prop} {x : α} {xs : List α} (h : P x) (t : ∀ y ∈ xs, P y) : ∀ y ∈ x::xs, P y := List.forall_mem_cons.mpr ⟨h,t⟩
private theorem nil {α : Type} {P : α → Prop} : ∀ y ∈ ([] : List α), P y := List.forall_mem_nil _

private theorem pr2 : Nat.Prime 2 := by norm_num1
private theorem pr3 : Nat.Prime 3 := by norm_num1
private theorem pr7 : Nat.Prime 7 := by norm_num1
private theorem pr43 : Nat.Prime 43 := by norm_num1
private theorem pr1373 : Nat.Prime 1373 := by norm_num1
private theorem pr3613 : Nat.Prime 3613 := by norm_num1
private theorem pr8429 : Nat.Prime 8429 := by norm_num1
private theorem pr10837 : Nat.Prime 10837 := by norm_num1
private theorem pr14407 : Nat.Prime 14407 := by norm_num1
private theorem pr22189 : Nat.Prime 22189 := by norm_num1
private theorem move0 {c : ℕ} (hx : Exceptional (19222*c)) : ∃ p ∈ ([1373] : List ℕ), p ∣ c :=
  checked_guard 19222 19208 [1373] [2, 7, 1373] [2, 2, 2, 7, 7, 7, 7] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr7 (cons pr1373 (cons pr2 (cons pr2 (cons pr2 (cons pr7 (cons pr7 (cons pr7 (cons pr7 nil)))))))))) (by decide +kernel) hx

private theorem move1 {c : ℕ} (hx : Exceptional (28812*c)) : ∃ p ∈ ([7, 1373] : List ℕ), p ∣ c :=
  checked_guard 28812 24714 [7, 1373] [2, 2, 3, 7, 7, 7, 7] [2, 3, 3, 1373] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr2 (cons pr3 (cons pr3 (cons pr1373 nil))))))))))) (by decide +kernel) hx

private theorem move2 {c : ℕ} (hx : Exceptional (66564*c)) : ∃ p ∈ ([43, 10837] : List ℕ), p ∣ c :=
  checked_guard 66564 65022 [43, 10837] [2, 2, 3, 3, 43, 43] [2, 3, 10837] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr43 (cons pr43 (cons pr2 (cons pr3 (cons pr10837 nil))))))))) (by decide +kernel) hx

private theorem move3 {c : ℕ} (hx : Exceptional (605052*c)) : ∃ p ∈ ([14407] : List ℕ), p ∣ c :=
  checked_guard 605052 605094 [14407] [2, 2, 3, 3, 7, 7, 7, 7, 7] [2, 3, 7, 14407] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr2 (cons pr3 (cons pr7 (cons pr14407 nil))))))))))))) (by decide +kernel) hx

private theorem move4 {c : ℕ} (hx : Exceptional (605094*c)) : ∃ p ∈ ([14407] : List ℕ), p ∣ c :=
  checked_guard 605094 605052 [14407] [2, 3, 7, 14407] [2, 2, 3, 3, 7, 7, 7, 7, 7] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr7 (cons pr14407 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr7 nil))))))))))))) (by decide +kernel) hx

private theorem move5 {c : ℕ} (hx : Exceptional (1087212*c)) : ∃ p ∈ ([43, 8429] : List ℕ), p ∣ c :=
  checked_guard 1087212 1062054 [43, 8429] [2, 2, 3, 7, 7, 43, 43] [2, 3, 3, 7, 8429] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr7 (cons pr7 (cons pr43 (cons pr43 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr8429 nil)))))))))))) (by decide +kernel) hx

private theorem move6 {c : ℕ} (hx : Exceptional (2226196*c)) : ∃ p ∈ ([43, 22189] : List ℕ), p ∣ c :=
  checked_guard 2226196 2174522 [43, 22189] [2, 2, 7, 43, 43, 43] [2, 7, 7, 22189] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr7 (cons pr43 (cons pr43 (cons pr43 (cons pr2 (cons pr7 (cons pr7 (cons pr22189 nil)))))))))) (by decide +kernel) hx

private theorem move7 {c : ℕ} (hx : Exceptional (2862252*c)) : ∃ p ∈ ([3, 22189] : List ℕ), p ∣ c :=
  checked_guard 2862252 1908254 [3, 22189] [2, 2, 3, 3, 43, 43, 43] [2, 43, 22189] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr43 (cons pr43 (cons pr43 (cons pr2 (cons pr43 (cons pr22189 nil)))))))))) (by decide +kernel) hx

private theorem move8 {c : ℕ} (hx : Exceptional (3261636*c)) : ∃ p ∈ ([3, 3613] : List ℕ), p ∣ c :=
  checked_guard 3261636 2175026 [3, 3613] [2, 2, 3, 3, 7, 7, 43, 43] [2, 7, 43, 3613] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr43 (cons pr43 (cons pr2 (cons pr7 (cons pr43 (cons pr3613 nil)))))))))))) (by decide +kernel) hx

private theorem move9 {c : ℕ} (hx : Exceptional (3261636*c)) : ∃ p ∈ ([7, 10837] : List ℕ), p ∣ c :=
  checked_guard 3261636 2795946 [7, 10837] [2, 2, 3, 3, 7, 7, 43, 43] [2, 3, 43, 10837] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr43 (cons pr43 (cons pr2 (cons pr3 (cons pr43 (cons pr10837 nil)))))))))))) (by decide +kernel) hx

private theorem move10 {c : ℕ} (hx : Exceptional (5074258*c)) : ∃ p ∈ ([8429] : List ℕ), p ∣ c :=
  checked_guard 5074258 5073656 [8429] [2, 7, 43, 8429] [2, 2, 2, 7, 7, 7, 43, 43] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr7 (cons pr43 (cons pr8429 (cons pr2 (cons pr2 (cons pr2 (cons pr7 (cons pr7 (cons pr7 (cons pr43 (cons pr43 nil)))))))))))) (by decide +kernel) hx

private theorem move11 {c : ℕ} (hx : Exceptional (5724762*c)) : ∃ p ∈ ([22189] : List ℕ), p ∣ c :=
  checked_guard 5724762 5724504 [22189] [2, 3, 43, 22189] [2, 2, 2, 3, 3, 43, 43, 43] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr43 (cons pr22189 (cons pr2 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr43 (cons pr43 (cons pr43 nil)))))))))))) (by decide +kernel) hx

private theorem move12 {c : ℕ} (hx : Exceptional (7610484*c)) : ∃ p ∈ ([7, 8429] : List ℕ), p ∣ c :=
  checked_guard 7610484 6524046 [7, 8429] [2, 2, 3, 7, 7, 7, 43, 43] [2, 3, 3, 43, 8429] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr43 (cons pr43 (cons pr2 (cons pr3 (cons pr3 (cons pr43 (cons pr8429 nil))))))))))))) (by decide +kernel) hx

private theorem move13 {c : ℕ} (hx : Exceptional (19571622*c)) : ∃ p ∈ ([10837] : List ℕ), p ∣ c :=
  checked_guard 19571622 19569816 [10837] [2, 3, 7, 43, 10837] [2, 2, 2, 3, 3, 3, 7, 7, 43, 43] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr7 (cons pr43 (cons pr10837 (cons pr2 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr43 (cons pr43 nil))))))))))))))) (by decide +kernel) hx

private theorem node1450102504381627068 : Covered terminalDivisors 1450102504381627068 := terminal (by decide +kernel)
private theorem node1671209179095592332 : Covered terminalDivisors 1671209179095592332 := terminal (by decide +kernel)
private theorem node2124769406632273548 : Covered terminalDivisors 2124769406632273548 := terminal (by decide +kernel)
private theorem node2999318254965448668 : Covered terminalDivisors 2999318254965448668 := terminal (by decide +kernel)
private theorem node3228714860015041236 : Covered terminalDivisors 3228714860015041236 := terminal (by decide +kernel)
private theorem node365476809021422618268 : Covered terminalDivisors 365476809021422618268 := terminal (by decide +kernel)
private theorem node429352143586128113148 : Covered terminalDivisors 429352143586128113148 := terminal (by decide +kernel)
private theorem node748321944761128215996 : Covered terminalDivisors 748321944761128215996 := terminal (by decide +kernel)
private theorem node1746406782776939532228 : Covered terminalDivisors 1746406782776939532228 := terminal (by decide +kernel)
private theorem node12360820158317366084916 : Covered terminalDivisors 12360820158317366084916 := terminal (by decide +kernel)
private theorem node15715502787921172585524 : Covered terminalDivisors 15715502787921172585524 := terminal (by decide +kernel)
private theorem node708256468877424516 : Covered terminalDivisors 708256468877424516 :=
  ascend (q:=247447278883) (@move7) (by decide +kernel) (cons ⟨by decide +kernel, node2124769406632273548⟩ (cons ⟨by decide +kernel, node15715502787921172585524⟩ nil))
private theorem node557069726365197444 : Covered terminalDivisors 557069726365197444 :=
  ascend (q:=194626373347) (@move7) (by decide +kernel) (cons ⟨by decide +kernel, node1671209179095592332⟩ (cons ⟨by decide +kernel, node12360820158317366084916⟩ nil))
private theorem node483367501460542356 : Covered terminalDivisors 483367501460542356 :=
  ascend (q:=148197868021) (@move8) (by decide +kernel) (cons ⟨by decide +kernel, node1450102504381627068⟩ (cons ⟨by decide +kernel, node1746406782776939532228⟩ nil))
private theorem node69052500208648908 : Covered terminalDivisors 69052500208648908 :=
  ascend (q:=21171124003) (@move9) (by decide +kernel) (cons ⟨by decide +kernel, node483367501460542356⟩ (cons ⟨by decide +kernel, node748321944761128215996⟩ nil))
private theorem node29801634176867364 : Covered terminalDivisors 29801634176867364 :=
  ascend (q:=49251247206) (@move4) (by decide +kernel) (cons ⟨by decide +kernel, node429352143586128113148⟩ nil)
private theorem node16471080671568012 : Covered terminalDivisors 16471080671568012 :=
  ascend (q:=7398755847) (@move6) (by decide +kernel) (cons ⟨by decide +kernel, node708256468877424516⟩ (cons ⟨by decide +kernel, node365476809021422618268⟩ nil))
private theorem node405731774483028 : Covered terminalDivisors 405731774483028 :=
  ascend (q:=21107677374) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node557069726365197444⟩ nil)
private theorem node383048387710884 : Covered terminalDivisors 383048387710884 :=
  ascend (q:=352321707) (@move5) (by decide +kernel) (cons ⟨by decide +kernel, node16471080671568012⟩ (cons ⟨by decide +kernel, node3228714860015041236⟩ nil))
private theorem node355833225170892 : Covered terminalDivisors 355833225170892 :=
  ascend (q:=70125174) (@move10) (by decide +kernel) (cons ⟨by decide +kernel, node2999318254965448668⟩ nil)
private theorem node65355399914868 : Covered terminalDivisors 65355399914868 :=
  ascend (q:=3339294) (@move13) (by decide +kernel) (cons ⟨by decide +kernel, node708256468877424516⟩ nil)
private theorem node3112014971772 : Covered terminalDivisors 3112014971772 :=
  ascend (q:=543606) (@move11) (by decide +kernel) (cons ⟨by decide +kernel, node69052500208648908⟩ nil)
private theorem node2068552382652 : Covered terminalDivisors 2068552382652 :=
  ascend (q:=3418801) (@move3) (by decide +kernel) (cons ⟨by decide +kernel, node29801634176867364⟩ nil)
private theorem node295507483236 : Covered terminalDivisors 295507483236 :=
  ascend (q:=10256403) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node2068552382652⟩ (cons ⟨by decide +kernel, node405731774483028⟩ nil))
private theorem node42215354748 : Covered terminalDivisors 42215354748 :=
  ascend (q:=5547) (@move12) (by decide +kernel) (cons ⟨by decide +kernel, node295507483236⟩ (cons ⟨by decide +kernel, node355833225170892⟩ nil))
private theorem node35346349332 : Covered terminalDivisors 35346349332 :=
  ascend (q:=1806) (@move13) (by decide +kernel) (cons ⟨by decide +kernel, node383048387710884⟩ nil)
private theorem node6030764964 : Covered terminalDivisors 6030764964 :=
  ascend (q:=1849) (@move9) (by decide +kernel) (cons ⟨by decide +kernel, node42215354748⟩ (cons ⟨by decide +kernel, node65355399914868⟩ nil))
private theorem node140250348 : Covered terminalDivisors 140250348 :=
  ascend (q:=63) (@move6) (by decide +kernel) (cons ⟨by decide +kernel, node6030764964⟩ (cons ⟨by decide +kernel, node3112014971772⟩ nil))
private theorem node3261636 : Covered terminalDivisors 3261636 :=
  ascend (q:=49) (@move2) (by decide +kernel) (cons ⟨by decide +kernel, node140250348⟩ (cons ⟨by decide +kernel, node35346349332⟩ nil))

theorem covered {n : ℕ} (h : Exceptional n) : ∃ d ∈ terminalDivisors, d ∣ n :=
  node3261636 h (sylvester_divisor h)
theorem terminal_floor : ∀ d ∈ terminalDivisors, 1450102504381627068 ≤ d := by decide +kernel
theorem exceptional_lower {n : ℕ} (h : Exceptional n) : 1450102504381627068 ≤ n := by
  obtain ⟨d,mem,div⟩ := covered h
  exact (terminal_floor d mem).trans (Nat.le_of_dvd h.1 div)
theorem bounded {n : ℕ} (h : 0 < n) (limit : n < 1450102504381627068) :
    ∃ m, m ≠ n ∧ m ≤ 2*n ∧ m.totient = n.totient := witness_below h limit exceptional_lower

end Noe18

namespace TotientDensity

/-- If every member of a finite set of positive integers up to N is a multiple
of one of D given divisors, each at least B, at most |D| floor(N/B) can occur. -/
theorem count_covered {N B : ℕ} (D S : Finset ℕ) (bpos : 0<B)
    (rangeS : ∀ x∈S, 0<x ∧ x≤N)
    (divisor : ∀ x∈S, ∃ d∈D, d ∣ x)
    (floor : ∀ d∈D, B≤d) : S.card ≤ D.card*(N/B) := by
  let I := Finset.Icc 1 (N/B)
  let mult (d : ℕ) := I.image (d*·)
  have incl : S ⊆ D.biUnion mult := by
    intro x hx
    obtain ⟨d,hd,dvd⟩ := divisor x hx
    obtain ⟨xpos,xle⟩ := rangeS x hx
    obtain ⟨k,hk⟩ := dvd
    have kpos : 0<k := Nat.pos_of_dvd_of_pos (hk ▸ dvd_mul_left _ _) xpos
    have kle : k≤N/B := by
      apply (Nat.le_div_iff_mul_le bpos).mpr
      calc
        k*B ≤ k*d := Nat.mul_le_mul_left _ (floor d hd)
        _ = x := by simpa [mul_comm] using hk.symm
        _ ≤ N := xle
    apply Finset.mem_biUnion.mpr ⟨d,hd,?_⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_Icc.mpr ⟨kpos,kle⟩,hk.symm⟩
  calc
    S.card ≤ (D.biUnion mult).card := Finset.card_le_card incl
    _ ≤ ∑ d ∈ D, (mult d).card := Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ D, I.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = D.card*(N/B) := by simp [I]

end TotientDensity

namespace Noe18

/-- A uniform count, at every scale, for a set of failures of Noe's bound. -/
theorem exceptional_count {N : ℕ} (S : Finset ℕ)
    (fail : ∀ x ∈ S, Noe.Exceptional x ∧ x ≤ N) :
    S.card ≤ 11 * (N / 1450102504381627068) := by
  have bound := TotientDensity.count_covered (N:=N) (B:=1450102504381627068) terminalDivisors.toFinset S
    (by decide) (fun x hx => ⟨(fail x hx).1.1,(fail x hx).2⟩)
    (fun x hx => by simpa only [List.mem_toFinset] using covered (fail x hx).1)
    (fun d hd => terminal_floor d (List.mem_toFinset.mp hd))
  have length : terminalDivisors.toFinset.card = 11 := by decide +kernel
  rwa [length] at bound

end Noe18
