import OMAStatements.S_oeis_a074987
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A certified range for T. D. Noe's factor-two totient conjecture

This file proves the registered assertion for all positive inputs up to ten to
the thousandth power. See CarmichaelKlee.md for the size-controlled transfer of
the classical prime-square forcing argument, and for Kevin Ford's larger
published computation. The cited large prime products are independent of the
finite prime and divisibility certificates checked in this file.
-/

namespace Noe

/-- No distinct preimage at or below twice the given argument. -/
def Exceptional (n : ℕ) : Prop :=
  0<n ∧ ∀ m, m ≤ 2*n → m.totient=n.totient → m=n

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
    (all : ∀ q, q.Prime → q ∣ p-1 → q ∣ u) :
    ((p-1)*u).totient = (p*u).totient := by
  have bigger := prime.two_le
  rw [scale_saturated _ (by omega) all, Nat.totient_mul_of_prime_of_not_dvd prime absent]

/-- If the other-inverse bound fails at (p−1)u and all primes of p−1 already
divide u, both copies of p are forced in the original argument. -/
theorem force_prime_square {p u : ℕ} (prime : p.Prime) (hn : Exceptional ((p-1)*u))
    (all : ∀ q, q.Prime → q ∣ p-1 → q ∣ u) : p^2 ∣ (p-1)*u := by
  obtain ⟨positive,ex⟩ := hn
  have u0 : 0<u := Nat.pos_of_dvd_of_pos (dvd_mul_left _ _) positive
  have p2 := prime.two_le
  have pri : p ∣ u := by
    by_contra absent
    have small : p*u ≤ 2*((p-1)*u) := by
      rw [←mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    have eq := ex _ small (replace_prime prime absent all).symm
    have impossible := Nat.eq_of_mul_eq_mul_right u0 eq
    omega
  obtain ⟨v,hv⟩ := pri
  let w := (p-1)*v
  have nform : (p-1)*u = p*w := by rw [hv]; dsimp [w]; ring
  have wpos : 0<w := Nat.pos_of_dvd_of_pos (nform ▸ dvd_mul_left _ _) positive
  have pw : p ∣ w := by
    by_contra absent
    have cover : ∀ q, q.Prime → q∣p-1 → q∣w := fun q _ h => dvd_mul_of_dvd_left h _
    have small : (p-1)*w ≤ 2*((p-1)*u) := by
      calc
        (p-1)*w ≤ p*w := Nat.mul_le_mul_right _ (by omega)
        _ = (p-1)*u := nform.symm
        _ ≤ 2*((p-1)*u) := by omega
    have eq := ex _ small ((replace_prime prime absent cover).trans (congrArg Nat.totient nform.symm))
    rw [nform] at eq
    have impossible := Nat.eq_of_mul_eq_mul_right wpos eq
    omega
  rw [nform,pow_two]
  exact Nat.mul_dvd_mul_left _ pw

/-- A condition expressible as divisibility alone, so the rule can iterate. -/
theorem square_from_radical {n p : ℕ} (hn : Exceptional n) (hp : p.Prime)
    (hd : (p-1)*(∏ q ∈ (p-1).primeFactors,q) ∣ n) : p^2 ∣ n := by
  obtain ⟨c,hc⟩ := hd
  rw [mul_assoc] at hc
  subst n
  apply force_prime_square hp hn
  intro q hq div
  have p0 := hp.two_le
  have mem : q ∈ (p-1).primeFactors := Nat.mem_primeFactors.mpr ⟨hq,div,by omega⟩
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id mem) c

private def trigger (p : ℕ) := (p-1) * ∏ q ∈ (p-1).primeFactors,q

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

/-!
## Transfer of the Carmichael–Klee prime-square forcing rules to Noe's bounded problem

The branches below are those used by Aaron Schlafly and Stan Wagon (1994), DOI
10.1090/S0025-5718-1994-1226815-3. The proof checks that every substitution stays within
Noe's upper bound of twice the original preimage. The enumeration of primes in that paper
is separate from the substitution lemmas.
-/

namespace Noe

private theorem transfer_scale (a : ℕ) {u : ℕ} (pos : 0<a)
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

/-- A forced prime occurring once can be removed and replaced by its predecessor
if every prime factor of that predecessor already occurs in the preimage. -/
theorem square_of_forced_prime {n p : ℕ} (hn : Exceptional n) (hp : p.Prime)
    (forced : p ∣ n) (support : ∀ q, q.Prime → q ∣ p-1 → q ∣ n) : p^2 ∣ n := by
  obtain ⟨w,rfl⟩ := forced
  have wpos := Nat.pos_of_dvd_of_pos (dvd_mul_left w p) hn.1
  have bigger := hp.two_le
  have pw : p ∣ w := by
    by_contra neg
    have supp (q : ℕ) (prime : q.Prime) (hq : q ∣ p-1) : q ∣ w := by
      rcases prime.dvd_mul.mp (support q prime hq) with qp|qw
      · have eq := (Nat.prime_dvd_prime_iff_eq prime hp).mp qp
        subst q
        have le := Nat.le_of_dvd (by omega : 0<p-1) hq
        omega
      · exact qw
    have eqphi : ((p-1)*w).totient = (p*w).totient := by
      rw [transfer_scale _ (by omega) supp,Nat.totient_mul_of_prime_of_not_dvd hp neg]
    have small : (p-1)*w ≤ 2*(p*w) :=
      (Nat.mul_le_mul_right _ (by omega : p-1 ≤ p)).trans (by omega)
    have eq := Nat.eq_of_mul_eq_mul_right wpos (hn.2 _ small eqphi)
    omega
  rw [pow_two]
  exact Nat.mul_dvd_mul_left _ pw

/-- Insertion of p = e φ(d) + 1 into the saturated part of a totient preimage. -/
theorem square_by_insertion {d e u p : ℕ} (hn : Exceptional (d*(e*u))) (hp : p.Prime)
    (eqp : p=e*d.totient+1) (cop : d.Coprime (e*u))
    (sat : ∀ q, q.Prime → q ∣ e → q ∣ u)
    (support : ∀ q, q.Prime → q ∣ p-1 → q ∣ d*(e*u)) : p^2 ∣ d*(e*u) := by
  apply square_of_forced_prime hn hp _ support
  by_contra absent
  have pu : ¬p ∣ u := fun h => absent (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h _) _)
  have de : 0 < d*e := Nat.pos_of_dvd_of_pos (show d*e ∣ d*(e*u) by rw [←mul_assoc]; exact dvd_mul_right _ _) hn.1
  have epos : 0 < e := Nat.pos_of_dvd_of_pos (dvd_mul_left e d) de
  have bound : p ≤ 2*(d*e) := by
    have le := Nat.mul_le_mul_left e (Nat.totient_le d)
    rw [mul_comm e d] at le
    omega
  have small : p*u ≤ 2*(d*(e*u)) := by
    rw [← mul_assoc d e, ← mul_assoc]
    exact Nat.mul_le_mul_right u bound
  have phi : (p*u).totient = (d*(e*u)).totient := by
    rw [Nat.totient_mul_of_prime_of_not_dvd hp pu,Nat.totient_mul cop,transfer_scale _ epos sat,eqp]
    simp only [Nat.add_sub_cancel]
    ring
  have eq := hn.2 _ small phi
  exact absent (eq ▸ dvd_mul_right _ _)

private theorem multiple {n k : ℕ} (cop : k.Coprime 6) (hs : k^2 ∣ n)
    (hb : 36 ∣ n) : 36*k^2 ∣ n := by
  have c : (6^2).Coprime (k^2) := (cop.symm.pow_left 2).pow_right 2
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by simpa using c) hb hs

/-- The common 6k+1 step in both branches of the Schlafly–Wagon sieve. -/
theorem square_six {n k : ℕ} (hn : Exceptional n) (hb : 36 ∣ n)
    (cop : k.Coprime 6) (hs : k^2 ∣ n) (hp : (6*k+1).Prime) : (6*k+1)^2 ∣ n := by
  obtain ⟨c,hc⟩ := multiple cop hs hb
  have eq : (6*k+1-1)*(6*k*c) = n := by rw [hc]; simp only [Nat.add_sub_cancel]; ring
  rw [←eq] at hn ⊢
  apply force_prime_square hp hn
  intro q _ h
  exact dvd_mul_of_dvd_left (by simpa using h) _

/-- When the 3-adic valuation is two, insert 12k+1 in place of 18k. -/
theorem square_twelve {n k : ℕ} (hn : Exceptional n) (miss : ¬27 ∣ n) (hb : 36 ∣ n)
    (cop : k.Coprime 6) (hs : k^2 ∣ n) (hp : (12*k+1).Prime) : (12*k+1)^2 ∣ n := by
  obtain ⟨c,hc⟩ := multiple cop hs hb
  let u := 2*k*c
  have eq : n = 9*((2*k)*u) := by rw [hc]; dsimp [u]; ring
  have three : ¬3 ∣ (2*k)*u := by
    rintro ⟨t,ht⟩
    exact miss ⟨t, by rw [eq,ht]; ring⟩
  have prime3 : Nat.Prime 3 := by decide
  have c9 : (3^2).Coprime (2*k*u) := (prime3.coprime_iff_not_dvd.mpr three).pow_left 2
  rw [eq] at hn ⊢
  refine square_by_insertion hn hp ?_ (by simpa using c9) ?_ ?_
  · rw [show Nat.totient 9 = 6 from by decide]
    ring
  · intro q _ h
    exact dvd_mul_of_dvd_left h _
  · intro q _ h
    have dvd : 12*k ∣ 9*(2*k*u) := ⟨3*k*c,by dsimp [u]; ring⟩
    exact (show q ∣ 12*k by simpa using h).trans dvd

/-- In the 27-divisible branch, all prime factors of 18k are already in 6k. -/
theorem square_eighteen {n k : ℕ} (hn : Exceptional n) (cube : 27 ∣ n) (hb : 36 ∣ n)
    (cop : k.Coprime 6) (hs : k^2 ∣ n) (hp : (18*k+1).Prime) : (18*k+1)^2 ∣ n := by
  have h4 : 4 ∣ n := (by decide : 4 ∣ 36).trans hb
  have h108 : 108 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 4 27) h4 cube
  have h216 : (6^3).Coprime (k^2) := (cop.symm.pow_left 3).pow_right 2
  have c108 : (108:ℕ).Coprime (k^2) := h216.coprime_dvd_left (by decide)
  obtain ⟨c,hc⟩ := c108.mul_dvd_of_dvd_of_dvd h108 hs
  have eq : (18*k+1-1)*(6*k*c) = n := by rw [hc]; simp only [Nat.add_sub_cancel]; ring
  rw [←eq] at hn ⊢
  apply force_prime_square hp hn
  intro q prime h
  have d : (18*k) ∣ (6*k)^2 := ⟨2*k,by ring⟩
  have qd := (show q ∣ 18*k by simpa using h).trans d
  exact dvd_mul_of_dvd_left (prime.dvd_of_dvd_pow qd) _

end Noe

namespace Noe

/-- Kevin Ford, *The distribution of totients*, §7.3, Lemma 7.2, with uniqueness
among inputs at most twice n in place of uniqueness among all inputs. -/
theorem bounded_ford_rule {n d e p : ℕ} (hn : Exceptional n) (hd : d ∣ n)
    (hc : d.Coprime (n/d))
    (phiSupport : (∏ q ∈ d.totient.primeFactors, q) ∣ n)
    (he : e ∣ (n/d) / (∏ q ∈ (n/d).primeFactors, q))
    (eqp : p = 1+e*d.totient) (hp : p.Prime) : p^2 ∣ n := by
  let v := n/d
  let r := ∏ q ∈ v.primeFactors, q
  have dv : d*v=n := Nat.mul_div_cancel' hd
  have vp : 0<v := Nat.pos_of_dvd_of_pos (dv ▸ dvd_mul_left _ _) hn.1
  have dp : 0<d := Nat.pos_of_dvd_of_pos hd hn.1
  have rv : r ∣ v := Nat.prod_primeFactors_dvd v
  obtain ⟨t,ht⟩ := he
  change v / r = e*t at ht
  let u := r*t
  have vu : v = e*u := by
    calc v = r*(v/r) := (Nat.mul_div_cancel' rv).symm
         _ = _ := by rw [ht]; dsimp [u]; ring
  have nd : n = d*(e*u) := dv.symm.trans (congrArg (d*·) vu)
  have sat (q : ℕ) (hq : q.Prime) (divides : q ∣ e) : q ∣ u := by
    have qv : q ∣ v := vu ▸ dvd_mul_of_dvd_left divides _
    have mem : q ∈ v.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,qv,vp.ne'⟩
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id mem) _
  have support (q : ℕ) (hq : q.Prime) (divides : q ∣ p-1) : q ∣ d*(e*u) := by
    have diff : p-1=e*d.totient := by omega
    rw [diff] at divides
    rcases hq.dvd_mul.mp divides with qe|qφ
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left qe _) _
    · have mem := Nat.mem_primeFactors.mpr ⟨hq,qφ,(Nat.totient_pos.mpr dp).ne'⟩
      exact nd ▸ (Finset.dvd_prod_of_mem id mem).trans phiSupport
  rw [nd] at hn ⊢
  exact square_by_insertion hn hp (by simpa only [add_comm] using eqp)
    (vu ▸ hc) sat support

end Noe

namespace NoeLucas

private def binaryPower (a m : ℕ) : List Bool → ℕ × ℕ
  | [] => (0, 1)
  | b :: bs =>
    let (e, r) := binaryPower a m bs
    if b then (e+e+1, (r*r*a) % m) else (e+e, (r*r) % m)

private theorem binaryPower_correct (a m : ℕ) (bs : List Bool) :
    a ^ (binaryPower a m bs).1 ≡ (binaryPower a m bs).2 [MOD m] := by
  induction bs with
  | nil => simpa [binaryPower] using (Nat.ModEq.refl (n:=m) 1)
  | cons b bs ih =>
    generalize he : binaryPower a m bs = v at *
    obtain ⟨e,r⟩ := v
    change a^e ≡ r [MOD m] at ih
    have reduce {u w : ℕ} (h : u ≡ w [MOD m]) : u ≡ w%m [MOD m] := by
      simpa only [Nat.ModEq,Nat.mod_mod] using h
    cases b
    · simpa [binaryPower,he,pow_add] using reduce (ih.mul ih)
    · simpa [binaryPower,he,pow_add] using reduce ((ih.mul ih).mul (Nat.ModEq.refl a))

/-- Recover all prime divisors from a displayed product of certified primes. -/
theorem prime_factors_of_product (ps : List ℕ) (hp : ∀ p ∈ ps, Nat.Prime p) :
    ps.prod.primeFactors = ps.toFinset := by
  have pos (l : List ℕ) (h : ∀ p ∈ l, Nat.Prime p) : 0 < l.prod :=
    List.prod_pos (fun x hx => (h x hx).pos)
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have prime := hp p (by simp)
    have hs : ∀ q ∈ ps, Nat.Prime q := fun q h => hp q (List.mem_cons_of_mem p h)
    simp [Nat.primeFactors_mul prime.ne_zero (pos ps hs).ne',prime.primeFactors,ih hs]

def checkPower (a p n : ℕ) (expected : Bool) : Prop :=
  let v := binaryPower a p n.bits
  v.1 = n ∧ decide (v.2 ≡ 1 [MOD p]) = expected

instance (a p n : ℕ) (b : Bool) : Decidable (checkPower a p n b) := by
  unfold checkPower
  infer_instance

/-- A recursively certified factor list for p−1 and a generator witness
certify primality using the ordinary Lucas criterion. -/
theorem lucas_check (p a : ℕ) (ps : List ℕ) (fac : (p-1).primeFactors = ps.toFinset)
    (hp : 1<p) (ha : checkPower a p (p-1) true)
    (hb : ∀ q ∈ ps, checkPower a p ((p-1)/q) false) : Nat.Prime p := by
  apply lucas_primality p (a : ZMod p)
  · obtain ⟨eqn,yes⟩ := ha
    have h := binaryPower_correct a p (p-1).bits
    rw [eqn] at h
    have eq1 := of_decide_eq_true yes
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr (h.trans eq1)
  · intro q hq dvd
    have mem : q∈ps := List.mem_toFinset.mp (fac ▸ (Nat.mem_primeFactors.mpr ⟨hq,dvd,by omega⟩))
    obtain ⟨eqn,no⟩ := hb q mem
    have h := binaryPower_correct a p ((p-1)/q).bits
    rw [eqn] at h
    intro bad
    have e : a^((p-1)/q) ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using bad)
    exact (of_decide_eq_false no) (h.symm.trans e)

end NoeLucas


namespace NoeCensus

theorem prime2 : Nat.Prime 2 := by decide +kernel
theorem prime3 : Nat.Prime 3 := by decide +kernel
theorem prime7 : Nat.Prime 7 := by decide +kernel
theorem prime13 : Nat.Prime 13 := by decide +kernel
theorem prime19 : Nat.Prime 19 := by decide +kernel
theorem prime43 : Nat.Prime 43 := by decide +kernel
theorem prime79 : Nat.Prime 79 := by decide +kernel
theorem prime127 : Nat.Prime 127 := by decide +kernel
theorem prime157 : Nat.Prime 157 := by decide +kernel
theorem prime547 : Nat.Prime 547 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 13] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime13,(by simp)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 13] : List ℕ).prod = 547-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 547 2 [2, 3, 7, 13] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime1093 : Nat.Prime 1093 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 7, 13] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime13,(by simp)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 7, 13] : List ℕ).prod = 1093-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 1093 5 [2, 2, 3, 7, 13] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime2287 : Nat.Prime 2287 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 127] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime127,(by simp)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 127] : List ℕ).prod = 2287-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 2287 19 [2, 3, 3, 127] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime3613 : Nat.Prime 3613 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 7, 43] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime43,(by simp)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 7, 43] : List ℕ).prod = 3613-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 3613 2 [2, 2, 3, 7, 43] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime4903 : Nat.Prime 4903 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 19, 43] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime43,(by simp)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 19, 43] : List ℕ).prod = 4903-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 4903 3 [2, 3, 19, 43] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime5419 : Nat.Prime 5419 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 7, 43] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime43,(by simp)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 7, 43] : List ℕ).prod = 5419-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 5419 3 [2, 3, 3, 7, 43] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime6709 : Nat.Prime 6709 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 13, 43] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(by simp)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 13, 43] : List ℕ).prod = 6709-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 6709 2 [2, 2, 3, 13, 43] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime14479 : Nat.Prime 14479 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 19, 127] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime127,(by simp)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 19, 127] : List ℕ).prod = 14479-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 14479 3 [2, 3, 19, 127] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime46957 : Nat.Prime 46957 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 7, 13, 43] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 7, 13, 43] : List ℕ).prod = 46957-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 46957 5 [2, 2, 3, 7, 13, 43] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime98299 : Nat.Prime 98299 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 43, 127] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime127,(by simp)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 43, 127] : List ℕ).prod = 98299-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 98299 2 [2, 3, 3, 43, 127] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime101347 : Nat.Prime 101347 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 19, 127] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime127,(by simp)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 19, 127] : List ℕ).prod = 101347-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 101347 2 [2, 3, 7, 19, 127] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime303493 : Nat.Prime 303493 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 7, 3613] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime3613,(by simp)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 7, 3613] : List ℕ).prod = 303493-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 303493 5 [2, 2, 3, 7, 3613] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime304039 : Nat.Prime 304039 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 7, 19, 127] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime127,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 7, 19, 127] : List ℕ).prod = 304039-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 304039 3 [2, 3, 3, 7, 19, 127] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime617767 : Nat.Prime 617767 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 19, 5419] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime5419,(by simp)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 19, 5419] : List ℕ).prod = 617767-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 617767 3 [2, 3, 19, 5419] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime12118003 : Nat.Prime 12118003 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 13, 43, 3613] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime3613,(by simp)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 13, 43, 3613] : List ℕ).prod = 12118003-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 12118003 5 [2, 3, 13, 43, 3613] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime56739825819987904059035875856149 : Nat.Prime 56739825819987904059035875856149 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 13, 43, 79, 157, 1093, 3613, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 13, 43, 79, 157, 1093, 3613, 46957, 303493, 12118003] : List ℕ).prod = 56739825819987904059035875856149-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 56739825819987904059035875856149 2 [2, 2, 3, 13, 43, 79, 157, 1093, 3613, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime120281850455994959752320782994877 : Nat.Prime 120281850455994959752320782994877 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 7, 13, 43, 79, 157, 547, 1093, 3613, 6709, 46957, 303493] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 7, 13, 43, 79, 157, 547, 1093, 3613, 6709, 46957, 303493] : List ℕ).prod = 120281850455994959752320782994877-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 120281850455994959752320782994877 5 [2, 2, 3, 7, 13, 43, 79, 157, 547, 1093, 3613, 6709, 46957, 303493] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime184549569863135066324678230069147 : Nat.Prime 184549569863135066324678230069147 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 13, 43, 79, 157, 547, 6709, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 13, 43, 79, 157, 547, 6709, 46957, 303493, 12118003] : List ℕ).prod = 184549569863135066324678230069147-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 184549569863135066324678230069147 2 [2, 3, 7, 13, 43, 79, 157, 547, 6709, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime360845581145629029504245626950943 : Nat.Prime 360845581145629029504245626950943 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 79, 157, 547, 1093, 6709, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 79, 157, 547, 1093, 6709, 46957, 303493, 12118003] : List ℕ).prod = 360845581145629029504245626950943-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 360845581145629029504245626950943 5 [2, 3, 7, 79, 157, 547, 1093, 6709, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime369435925317577541457299485375093 : Nat.Prime 369435925317577541457299485375093 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 7, 43, 79, 157, 547, 1093, 3613, 6709, 46957, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 7, 43, 79, 157, 547, 1093, 3613, 6709, 46957, 12118003] : List ℕ).prod = 369435925317577541457299485375093-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 369435925317577541457299485375093 19 [2, 2, 3, 7, 43, 79, 157, 547, 1093, 3613, 6709, 46957, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime388652581511151493098476509218589 : Nat.Prime 388652581511151493098476509218589 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 7, 79, 157, 547, 1093, 3613, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 7, 79, 157, 547, 1093, 3613, 46957, 303493, 12118003] : List ℕ).prod = 388652581511151493098476509218589-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 388652581511151493098476509218589 6 [2, 2, 3, 7, 79, 157, 547, 1093, 3613, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime2411492209459338136097875027992133 : Nat.Prime 2411492209459338136097875027992133 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 13, 43, 157, 547, 3613, 6709, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 13, 43, 157, 547, 3613, 6709, 46957, 303493, 12118003] : List ℕ).prod = 2411492209459338136097875027992133-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 2411492209459338136097875027992133 11 [2, 2, 3, 13, 43, 157, 547, 3613, 6709, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime4430415919704365412830979702590197 : Nat.Prime 4430415919704365412830979702590197 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 13, 79, 157, 547, 3613, 6709, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 13, 79, 157, 547, 3613, 6709, 46957, 303493, 12118003] : List ℕ).prod = 4430415919704365412830979702590197-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 4430415919704365412830979702590197 2 [2, 2, 3, 13, 79, 157, 547, 3613, 6709, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime4434378640249280619239798433503773 : Nat.Prime 4434378640249280619239798433503773 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 13, 43, 79, 157, 547, 1093, 3613, 6709, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 13, 43, 79, 157, 547, 1093, 3613, 6709, 303493, 12118003] : List ℕ).prod = 4434378640249280619239798433503773-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 4434378640249280619239798433503773 5 [2, 2, 3, 13, 43, 79, 157, 547, 1093, 3613, 6709, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime5077898000961363149246511915945679 : Nat.Prime 5077898000961363149246511915945679 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 19, 43, 127, 4903, 5419, 14479, 98299, 101347, 304039] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 19, 43, 127, 4903, 5419, 14479, 98299, 101347, 304039] : List ℕ).prod = 5077898000961363149246511915945679-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 5077898000961363149246511915945679 3 [2, 3, 7, 19, 43, 127, 4903, 5419, 14479, 98299, 101347, 304039] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime8356030502489757101617244948199643 : Nat.Prime 8356030502489757101617244948199643 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 43, 79, 157, 547, 1093, 3613, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 43, 79, 157, 547, 1093, 3613, 46957, 303493, 12118003] : List ℕ).prod = 8356030502489757101617244948199643-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 8356030502489757101617244948199643 2 [2, 3, 7, 43, 79, 157, 547, 1093, 3613, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime9381985109786354767110386300724493 : Nat.Prime 9381985109786354767110386300724493 := by
  have h := NoeLucas.prime_factors_of_product [2, 2, 3, 7, 13, 79, 157, 547, 1093, 6709, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 2, 3, 7, 13, 79, 157, 547, 1093, 6709, 46957, 303493, 12118003] : List ℕ).prod = 9381985109786354767110386300724493-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 9381985109786354767110386300724493 2 [2, 2, 3, 7, 13, 79, 157, 547, 1093, 6709, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime14667180345286093576766435952749923 : Nat.Prime 14667180345286093576766435952749923 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 7, 19, 43, 127, 2287, 4903, 5419, 98299, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 7, 19, 43, 127, 2287, 4903, 5419, 98299, 304039, 617767] : List ℕ).prod = 14667180345286093576766435952749923-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 14667180345286093576766435952749923 3 [2, 3, 3, 7, 19, 43, 127, 2287, 4903, 5419, 98299, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime44637471330223523736590837979281983 : Nat.Prime 44637471330223523736590837979281983 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 7, 19, 127, 5419, 14479, 98299, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 7, 19, 127, 5419, 14479, 98299, 101347, 304039, 617767] : List ℕ).prod = 44637471330223523736590837979281983-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 44637471330223523736590837979281983 3 [2, 3, 3, 7, 19, 127, 5419, 14479, 98299, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime78379110417272215440461953312051279 : Nat.Prime 78379110417272215440461953312051279 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 43, 2287, 4903, 14479, 98299, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 43, 2287, 4903, 14479, 98299, 101347, 304039, 617767] : List ℕ).prod = 78379110417272215440461953312051279-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 78379110417272215440461953312051279 11 [2, 3, 43, 2287, 4903, 14479, 98299, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime82096375219206345679665135708014443 : Nat.Prime 82096375219206345679665135708014443 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 19, 43, 2287, 4903, 5419, 14479, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 19, 43, 2287, 4903, 5419, 14479, 101347, 304039, 617767] : List ℕ).prod = 82096375219206345679665135708014443-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 82096375219206345679665135708014443 2 [2, 3, 19, 43, 2287, 4903, 5419, 14479, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime261950813418014380202859535754160127 : Nat.Prime 261950813418014380202859535754160127 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 43, 127, 2287, 4903, 5419, 14479, 98299, 101347, 304039] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 43, 127, 2287, 4903, 5419, 14479, 98299, 101347, 304039] : List ℕ).prod = 261950813418014380202859535754160127-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 261950813418014380202859535754160127 5 [2, 3, 3, 43, 127, 2287, 4903, 5419, 14479, 98299, 101347, 304039] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime270018673069170913931234520374027767 : Nat.Prime 270018673069170913931234520374027767 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 19, 43, 127, 2287, 14479, 98299, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 19, 43, 127, 2287, 14479, 98299, 101347, 304039, 617767] : List ℕ).prod = 270018673069170913931234520374027767-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 270018673069170913931234520374027767 3 [2, 3, 7, 19, 43, 127, 2287, 14479, 98299, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime557395016235180539513922446377617163 : Nat.Prime 557395016235180539513922446377617163 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 7, 19, 43, 2287, 4903, 5419, 14479, 98299, 101347, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 7, 19, 43, 2287, 4903, 5419, 14479, 98299, 101347, 617767] : List ℕ).prod = 557395016235180539513922446377617163-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 557395016235180539513922446377617163 12 [2, 3, 3, 7, 19, 43, 2287, 4903, 5419, 14479, 98299, 101347, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime666777595915506994631062445239824499 : Nat.Prime 666777595915506994631062445239824499 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 13, 43, 79, 157, 547, 3613, 6709, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 13, 43, 79, 157, 547, 3613, 6709, 46957, 303493, 12118003] : List ℕ).prod = 666777595915506994631062445239824499-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 666777595915506994631062445239824499 2 [2, 3, 7, 13, 43, 79, 157, 547, 3613, 6709, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime1303735084679157683598839450173753447 : Nat.Prime 1303735084679157683598839450173753447 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 79, 157, 547, 1093, 3613, 6709, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime157,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 79, 157, 547, 1093, 3613, 6709, 46957, 303493, 12118003] : List ℕ).prod = 1303735084679157683598839450173753447-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 1303735084679157683598839450173753447 3 [2, 3, 7, 79, 157, 547, 1093, 3613, 6709, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime3841246187888128489959068718127623103 : Nat.Prime 3841246187888128489959068718127623103 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 43, 127, 2287, 4903, 5419, 14479, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 43, 127, 2287, 4903, 5419, 14479, 101347, 304039, 617767] : List ℕ).prod = 3841246187888128489959068718127623103-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 3841246187888128489959068718127623103 3 [2, 3, 7, 43, 127, 2287, 4903, 5419, 14479, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime4641961225067828949883765940427568003 : Nat.Prime 4641961225067828949883765940427568003 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 7, 13, 43, 79, 547, 1093, 3613, 6709, 46957, 303493, 12118003] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime13,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime79,(List.forall_mem_cons.mpr ⟨prime547,(List.forall_mem_cons.mpr ⟨prime1093,(List.forall_mem_cons.mpr ⟨prime3613,(List.forall_mem_cons.mpr ⟨prime6709,(List.forall_mem_cons.mpr ⟨prime46957,(List.forall_mem_cons.mpr ⟨prime303493,(List.forall_mem_cons.mpr ⟨prime12118003,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 7, 13, 43, 79, 547, 1093, 3613, 6709, 46957, 303493, 12118003] : List ℕ).prod = 4641961225067828949883765940427568003-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 4641961225067828949883765940427568003 2 [2, 3, 7, 13, 43, 79, 547, 1093, 3613, 6709, 46957, 303493, 12118003] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime34569179684969993621501115918682473139 : Nat.Prime 34569179684969993621501115918682473139 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 7, 19, 127, 2287, 4903, 5419, 98299, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime7,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 7, 19, 127, 2287, 4903, 5419, 98299, 101347, 304039, 617767] : List ℕ).prod = 34569179684969993621501115918682473139-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 34569179684969993621501115918682473139 3 [2, 3, 3, 7, 19, 127, 2287, 4903, 5419, 98299, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime70758446940448836735802329175443917167 : Nat.Prime 70758446940448836735802329175443917167 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 43, 127, 4903, 5419, 14479, 98299, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 43, 127, 4903, 5419, 14479, 98299, 101347, 304039, 617767] : List ℕ).prod = 70758446940448836735802329175443917167-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 70758446940448836735802329175443917167 3 [2, 3, 3, 43, 127, 4903, 5419, 14479, 98299, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime209033027051691026084765695129550923423 : Nat.Prime 209033027051691026084765695129550923423 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 19, 43, 127, 2287, 5419, 14479, 98299, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime43,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 19, 43, 127, 2287, 5419, 14479, 98299, 101347, 304039, 617767] : List ℕ).prod = 209033027051691026084765695129550923423-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 209033027051691026084765695129550923423 3 [2, 3, 19, 43, 127, 2287, 5419, 14479, 98299, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

theorem prime71503878951240076806530665340943361223587 : Nat.Prime 71503878951240076806530665340943361223587 := by
  have h := NoeLucas.prime_factors_of_product [2, 3, 3, 19, 127, 2287, 4903, 5419, 14479, 98299, 101347, 304039, 617767] (List.forall_mem_cons.mpr ⟨prime2,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime3,(List.forall_mem_cons.mpr ⟨prime19,(List.forall_mem_cons.mpr ⟨prime127,(List.forall_mem_cons.mpr ⟨prime2287,(List.forall_mem_cons.mpr ⟨prime4903,(List.forall_mem_cons.mpr ⟨prime5419,(List.forall_mem_cons.mpr ⟨prime14479,(List.forall_mem_cons.mpr ⟨prime98299,(List.forall_mem_cons.mpr ⟨prime101347,(List.forall_mem_cons.mpr ⟨prime304039,(List.forall_mem_cons.mpr ⟨prime617767,(by simp)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
  have fac : ([2, 3, 3, 19, 127, 2287, 4903, 5419, 14479, 98299, 101347, 304039, 617767] : List ℕ).prod = 71503878951240076806530665340943361223587-1 := by decide +kernel
  rw [fac] at h
  exact NoeLucas.lucas_check 71503878951240076806530665340943361223587 3 [2, 3, 3, 19, 127, 2287, 4903, 5419, 14479, 98299, 101347, 304039, 617767] h (by decide) (by decide +kernel) (by decide +kernel)

end NoeCensus

namespace NoeCensus

private theorem merge_factors {a b c n : ℕ} (mul : a*b=c) (cop : a.Coprime b)
    (da : a ∣ n) (db : b ∣ n) : c ∣ n :=
  mul ▸ cop.mul_dvd_of_dvd_of_dvd da db

/-- Product of the forced prime squares in the 12-branch. -/
theorem branch12 {n : ℕ} (hn : Noe.Exceptional n) (branch : ¬27 ∣ n) : 508052094112639059070587694754755272431041485314043201086038239294943900028247267592852400962467236850116949010636185499445664351805878405992352692910028881506567251622828013464781740704744481414664053342541375956571628386248312907445272634414400937692437999948826000952094551030405965627529623960047048764929628940831376905190844004521302030693359017157009159972029738953724265835550751298848838023823838700322247077418957621504959351785364694721769847522195392234659010337611974541888734554116902182724673774302624768997560077254434732581227536148383049111009051124322123818234086775740617299371753755268953293003070871410625044181726540479555332705937271017249264214602167357205403656790787414865873932871400487094093057176669656573712975074920977666711382486853460616415989357882784262831989346100166276117916404377446205746848570048823211011932543721594794713622844990851295724132869691974066183898308868745444899852700031799478970569382456757059079836708787354555157849911042632073862120700535195084305167969556324 ∣ n := by
  have entry := Noe.sylvester_divisor hn
  have base : 36 ∣ n := (by decide +kernel : 36 ∣ 3261636).trans entry
  have h7 : 49 ∣ n := (by decide +kernel : 49 ∣ 3261636).trans entry
  have h43 : 1849 ∣ n := (by decide +kernel : 1849 ∣ 3261636).trans entry
  have h13 : 169 ∣ n :=
    Noe.square_twelve hn branch base (k:=1) (by decide +kernel)
      (one_dvd n) prime13
  have h3613 : 13053769 ∣ n :=
    Noe.square_twelve hn branch base (k:=301) (by decide +kernel)
      (merge_factors (a:=49) (b:=1849) (by decide +kernel) (by decide +kernel) h7 h43) prime3613
  have h79 : 6241 ∣ n :=
    Noe.square_six hn base (k:=13) (by decide +kernel)
      h13 prime79
  have h157 : 24649 ∣ n :=
    Noe.square_twelve hn branch base (k:=13) (by decide +kernel)
      h13 prime157
  have h547 : 299209 ∣ n :=
    Noe.square_six hn base (k:=91) (by decide +kernel)
      (merge_factors (a:=49) (b:=169) (by decide +kernel) (by decide +kernel) h7 h13) prime547
  have h1093 : 1194649 ∣ n :=
    Noe.square_twelve hn branch base (k:=91) (by decide +kernel)
      (merge_factors (a:=49) (b:=169) (by decide +kernel) (by decide +kernel) h7 h13) prime1093
  have h6709 : 45010681 ∣ n :=
    Noe.square_twelve hn branch base (k:=559) (by decide +kernel)
      (merge_factors (a:=169) (b:=1849) (by decide +kernel) (by decide +kernel) h13 h43) prime6709
  have h46957 : 2204959849 ∣ n :=
    Noe.square_twelve hn branch base (k:=3913) (by decide +kernel)
      (merge_factors (a:=49) (b:=312481) (by decide +kernel) (by decide +kernel) h7 (merge_factors (a:=169) (b:=1849) (by decide +kernel) (by decide +kernel) h13 h43)) prime46957
  have h303493 : 92108001049 ∣ n :=
    Noe.square_twelve hn branch base (k:=25291) (by decide +kernel)
      (merge_factors (a:=49) (b:=13053769) (by decide +kernel) (by decide +kernel) h7 h3613) prime303493
  have h12118003 : 146845996708009 ∣ n :=
    Noe.square_six hn base (k:=2019667) (by decide +kernel)
      (merge_factors (a:=169) (b:=24136418881) (by decide +kernel) (by decide +kernel) h13 (merge_factors (a:=1849) (b:=13053769) (by decide +kernel) (by decide +kernel) h43 h3613)) prime12118003
  have h4641961225067828949883765940427568003 : 21547804015033219335590420271323195613536806683998861370353250037189408009 ∣ n :=
    Noe.square_six hn base (k:=773660204177971491647294323404594667) (by decide +kernel)
      (merge_factors (a:=28592263072515961) (b:=20933988681156585273524572848170921802892496078134390849) (by decide +kernel) (by decide +kernel) (merge_factors (a:=8281) (b:=3452754869281) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=169) (by decide +kernel) (by decide +kernel) h7 h13) (merge_factors (a:=1849) (b:=1867363369) (by decide +kernel) (by decide +kernel) h43 (merge_factors (a:=6241) (b:=299209) (by decide +kernel) (by decide +kernel) h79 h547))) (merge_factors (a:=701926810386153707161) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1194649) (b:=587559032306689) (by decide +kernel) (by decide +kernel) h1093 (merge_factors (a:=13053769) (b:=45010681) (by decide +kernel) (by decide +kernel) h3613 h6709)) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime4641961225067828949883765940427568003
  have h1303735084679157683598839450173753447 : 1699725171023370455813211904940925845936278460039969939304358560344381809 ∣ n :=
    Noe.square_six hn base (k:=217289180779859613933139908362292241) (by decide +kernel)
      (merge_factors (a:=2694415350033775964281) (b:=17523129120902110388511247109545081277339616973801) (by decide +kernel) (by decide +kernel) (merge_factors (a:=305809) (b:=8810778459868009) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=6241) (by decide +kernel) (by decide +kernel) h7 h79) (merge_factors (a:=24649) (b:=357449732641) (by decide +kernel) (by decide +kernel) h157 (merge_factors (a:=299209) (b:=1194649) (by decide +kernel) (by decide +kernel) h547 h1093))) (merge_factors (a:=587559032306689) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=13053769) (b:=45010681) (by decide +kernel) (by decide +kernel) h3613 h6709) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime1303735084679157683598839450173753447
  have h666777595915506994631062445239824499 : 444592362414863130009708516282058956264442292126158506477195900320601001 ∣ n :=
    Noe.square_six hn base (k:=111129599319251165771843740873304083) (by decide +kernel)
      (merge_factors (a:=2355446167977721) (b:=5243077941135999547236061736399874223911509455114023409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=8281) (b:=284439822241) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=169) (by decide +kernel) (by decide +kernel) h7 h13) (merge_factors (a:=1849) (b:=153834409) (by decide +kernel) (by decide +kernel) h43 (merge_factors (a:=6241) (b:=24649) (by decide +kernel) (by decide +kernel) h79 h157))) (merge_factors (a:=175802950497452109001) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=299209) (b:=587559032306689) (by decide +kernel) (by decide +kernel) h547 (merge_factors (a:=13053769) (b:=45010681) (by decide +kernel) (by decide +kernel) h3613 h6709)) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime666777595915506994631062445239824499
  have h9381985109786354767110386300724493 : 88021644600252879312459968285026808351734060383803900203816690107049 ∣ n :=
    Noe.square_twelve hn branch base (k:=781832092482196230592532191727041) (by decide +kernel)
      (merge_factors (a:=381163165210625161) (b:=1603673903005069667888605417191841053943309099321) (by decide +kernel) (by decide +kernel) (merge_factors (a:=8281) (b:=46028639682481) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=169) (by decide +kernel) (by decide +kernel) h7 h13) (merge_factors (a:=6241) (b:=7375202641) (by decide +kernel) (by decide +kernel) h79 (merge_factors (a:=24649) (b:=299209) (by decide +kernel) (by decide +kernel) h157 h547))) (merge_factors (a:=53771965045969) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1194649) (b:=45010681) (by decide +kernel) (by decide +kernel) h1093 h6709) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime9381985109786354767110386300724493
  have h8356030502489757101617244948199643 : 69823245758539222563609486651307778181276867975907865970346985327449 ∣ n :=
    Noe.square_six hn base (k:=1392671750414959516936207491366607) (by decide +kernel)
      (merge_factors (a:=4170240783872461081) (b:=465089356927449848482065242429256331467024373129) (by decide +kernel) (by decide +kernel) (merge_factors (a:=90601) (b:=46028639682481) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=1849) (by decide +kernel) (by decide +kernel) h7 h43) (merge_factors (a:=6241) (b:=7375202641) (by decide +kernel) (by decide +kernel) h79 (merge_factors (a:=24649) (b:=299209) (by decide +kernel) (by decide +kernel) h157 h547))) (merge_factors (a:=15594672082081) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1194649) (b:=13053769) (by decide +kernel) (by decide +kernel) h1093 h3613) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime8356030502489757101617244948199643
  have h4434378640249280619239798433503773 : 19663713925099058906708011249997760066153045033261837441229205235529 ∣ n :=
    Noe.square_twelve hn branch base (k:=369531553354106718269983202791981) (by decide +kernel)
      (merge_factors (a:=14383075356621345361) (b:=9494045295496256119593664695420456974902719001) (by decide +kernel) (by decide +kernel) (merge_factors (a:=312481) (b:=46028639682481) (by decide +kernel) (by decide +kernel) (merge_factors (a:=169) (b:=1849) (by decide +kernel) (by decide +kernel) h13 h43) (merge_factors (a:=6241) (b:=7375202641) (by decide +kernel) (by decide +kernel) h79 (merge_factors (a:=24649) (b:=299209) (by decide +kernel) (by decide +kernel) h157 h547))) (merge_factors (a:=15594672082081) (b:=608800572754931704065088095091321) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1194649) (b:=13053769) (by decide +kernel) (by decide +kernel) h1093 h3613) (merge_factors (a:=45010681) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h6709 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime4434378640249280619239798433503773
  have h4430415919704365412830979702590197 : 19628585221569878037094889296235545110139776420249220258710920498809 ∣ n :=
    Noe.square_twelve hn branch base (k:=369201326642030451069248308549183) (by decide +kernel)
      (merge_factors (a:=7778840106339289) (b:=17523129120902110388511247109545081277339616973801) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1054729) (b:=7375202641) (by decide +kernel) (by decide +kernel) (merge_factors (a:=169) (b:=6241) (by decide +kernel) (by decide +kernel) h13 h79) (merge_factors (a:=24649) (b:=299209) (by decide +kernel) (by decide +kernel) h157 h547)) (merge_factors (a:=587559032306689) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=13053769) (b:=45010681) (by decide +kernel) (by decide +kernel) h3613 h6709) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime4430415919704365412830979702590197
  have h2411492209459338136097875027992133 : 5815294676283080354204206106191241247430881910872636818309509889689 ∣ n :=
    Noe.square_twelve hn branch base (k:=200957684121611511341489585666011) (by decide +kernel)
      (merge_factors (a:=2304610696462321) (b:=17523129120902110388511247109545081277339616973801) (by decide +kernel) (by decide +kernel) (merge_factors (a:=312481) (b:=7375202641) (by decide +kernel) (by decide +kernel) (merge_factors (a:=169) (b:=1849) (by decide +kernel) (by decide +kernel) h13 h43) (merge_factors (a:=24649) (b:=299209) (by decide +kernel) (by decide +kernel) h157 h547)) (merge_factors (a:=587559032306689) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=13053769) (b:=45010681) (by decide +kernel) (by decide +kernel) h3613 h6709) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime2411492209459338136097875027992133
  have h388652581511151493098476509218589 : 151050829115282255410729013848151694491135684274632844299383150921 ∣ n :=
    Noe.square_twelve hn branch base (k:=32387715125929291091539709101549) (by decide +kernel)
      (merge_factors (a:=2255403344441569) (b:=465089356927449848482065242429256331467024373129) (by decide +kernel) (by decide +kernel) (merge_factors (a:=305809) (b:=7375202641) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=6241) (by decide +kernel) (by decide +kernel) h7 h79) (merge_factors (a:=24649) (b:=299209) (by decide +kernel) (by decide +kernel) h157 h547)) (merge_factors (a:=15594672082081) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1194649) (b:=13053769) (by decide +kernel) (by decide +kernel) h1093 h3613) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime388652581511151493098476509218589
  have h369435925317577541457299485375093 : 136482902915254730675862061601205682173147814496950896594904758649 ∣ n :=
    Noe.square_twelve hn branch base (k:=30786327109798128454774957114591) (by decide +kernel)
      (merge_factors (a:=4170240783872461081) (b:=227276549732308644247327105492734487134820201) (by decide +kernel) (by decide +kernel) (merge_factors (a:=90601) (b:=46028639682481) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=1849) (by decide +kernel) (by decide +kernel) h7 h43) (merge_factors (a:=6241) (b:=7375202641) (by decide +kernel) (by decide +kernel) h79 (merge_factors (a:=24649) (b:=299209) (by decide +kernel) (by decide +kernel) h157 h547))) (merge_factors (a:=15594672082081) (b:=14573987098674547896936949976521) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1194649) (b:=13053769) (by decide +kernel) (by decide +kernel) h1093 h3613) (merge_factors (a:=45010681) (b:=323789526727546021730641) (by decide +kernel) (by decide +kernel) h6709 (merge_factors (a:=2204959849) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h46957 h12118003)))) prime369435925317577541457299485375093
  have h360845581145629029504245626950943 : 130209533432326744545059124681993013980753771747843573554928589249 ∣ n :=
    Noe.square_six hn base (k:=60140930190938171584040937825157) (by decide +kernel)
      (merge_factors (a:=2255403344441569) (b:=1603673903005069667888605417191841053943309099321) (by decide +kernel) (by decide +kernel) (merge_factors (a:=305809) (b:=7375202641) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=6241) (by decide +kernel) (by decide +kernel) h7 h79) (merge_factors (a:=24649) (b:=299209) (by decide +kernel) (by decide +kernel) h157 h547)) (merge_factors (a:=53771965045969) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1194649) (b:=45010681) (by decide +kernel) (by decide +kernel) h1093 h6709) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime360845581145629029504245626950943
  have h184549569863135066324678230069147 : 34058543736668170703013705565194525279694713898237951144401307609 ∣ n :=
    Noe.square_six hn base (k:=30758261643855844387446371678191) (by decide +kernel)
      (merge_factors (a:=2355446167977721) (b:=401652422464040810530358070255408550887602611561) (by decide +kernel) (by decide +kernel) (merge_factors (a:=8281) (b:=284439822241) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=169) (by decide +kernel) (by decide +kernel) h7 h13) (merge_factors (a:=1849) (b:=153834409) (by decide +kernel) (by decide +kernel) h43 (merge_factors (a:=6241) (b:=24649) (by decide +kernel) (by decide +kernel) h79 h157))) (merge_factors (a:=13467600851329) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=299209) (b:=45010681) (by decide +kernel) (by decide +kernel) h547 h6709) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime184549569863135066324678230069147
  have h120281850455994959752320782994877 : 14467723549118334907300774463665342924080230176110810257408245129 ∣ n :=
    Noe.square_twelve hn branch base (k:=10023487537999579979360065249573) (by decide +kernel)
      (merge_factors (a:=2355446167977721) (b:=42654467671698952699630367282304221849840094049) (by decide +kernel) (by decide +kernel) (merge_factors (a:=8281) (b:=284439822241) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=169) (by decide +kernel) (by decide +kernel) h7 h13) (merge_factors (a:=1849) (b:=153834409) (by decide +kernel) (by decide +kernel) h43 (merge_factors (a:=6241) (b:=24649) (by decide +kernel) (by decide +kernel) h79 h157))) (merge_factors (a:=4666066239007373929) (b:=9141419235568538298075380281) (by decide +kernel) (by decide +kernel) (merge_factors (a:=299209) (b:=15594672082081) (by decide +kernel) (by decide +kernel) h547 (merge_factors (a:=1194649) (b:=13053769) (by decide +kernel) (by decide +kernel) h1093 h3613)) (merge_factors (a:=45010681) (b:=203094444084694881601) (by decide +kernel) (by decide +kernel) h6709 (merge_factors (a:=2204959849) (b:=92108001049) (by decide +kernel) (by decide +kernel) h46957 h303493)))) prime120281850455994959752320782994877
  have h56739825819987904059035875856149 : 3219407834082566029233133332729863079510882681494636423741110201 ∣ n :=
    Noe.square_twelve hn branch base (k:=4728318818332325338252989654679) (by decide +kernel)
      (merge_factors (a:=48070329958729) (b:=465089356927449848482065242429256331467024373129) (by decide +kernel) (by decide +kernel) (merge_factors (a:=312481) (b:=153834409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=169) (b:=1849) (by decide +kernel) (by decide +kernel) h13 h43) (merge_factors (a:=6241) (b:=24649) (by decide +kernel) (by decide +kernel) h79 h157)) (merge_factors (a:=15594672082081) (b:=29823606067476022506761658023442409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1194649) (b:=13053769) (by decide +kernel) (by decide +kernel) h1093 h3613) (merge_factors (a:=2204959849) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) h46957 (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) prime56739825819987904059035875856149
  exact (merge_factors (a:=531131821166553823402968269267845448449229343480494102346467366835483470626596) (b:=956546141401915066125820425838572763291885186189759356566798345596728958572509684477169885583674085801503997962979967122604947300495579988882933280375368890246088100252463734950678531234616108448676535479275446554540312073167959279918926440646674611697913148236823709408863489600301118157002030658692667321207803247182068710368981682417197663612168598046803730712730150308131280224655478887588745113086715865857124885798612434825628907268907920912484547083682681684107431046914414875152116341911093667009345157250717542382056767329042025741041481435453018662275114453145220631829544920546767077508730718734135254529671266122401247991942872058561260121437596835569937037922869271375419714043908835490883682401216437940738573793751834219053587530784158955777793007655126961006549529416394837171598674335885414847945918601993591163434181021474313224721199356916503037666554358934018713850885473569084288751791446608572270748780046253596367674769) (by decide +kernel) (by decide +kernel) (merge_factors (a:=44906819995691071236) (b:=11827420004745767651001035566680172944694916733591570506761) (by decide +kernel) (by decide +kernel) (merge_factors (a:=3261636) (b:=13768188723601) (by decide +kernel) (by decide +kernel) (merge_factors (a:=36) (b:=90601) (by decide +kernel) (by decide +kernel) base (merge_factors (a:=49) (b:=1849) (by decide +kernel) (by decide +kernel) h7 h43)) (merge_factors (a:=169) (b:=81468572329) (by decide +kernel) (by decide +kernel) h13 (merge_factors (a:=13053769) (b:=6241) (by decide +kernel) (by decide +kernel) h3613 h79))) (merge_factors (a:=8810778459868009) (b:=1342380818972827724200669332324256793370529) (by decide +kernel) (by decide +kernel) (merge_factors (a:=24649) (b:=357449732641) (by decide +kernel) (by decide +kernel) h157 (merge_factors (a:=299209) (b:=1194649) (by decide +kernel) (by decide +kernel) h547 h1093)) (merge_factors (a:=99246744381147169) (b:=13525691218822743518701441) (by decide +kernel) (by decide +kernel) (merge_factors (a:=45010681) (b:=2204959849) (by decide +kernel) (by decide +kernel) h6709 h46957) (merge_factors (a:=92108001049) (b:=146845996708009) (by decide +kernel) (by decide +kernel) h303493 h12118003)))) (merge_factors (a:=38626715210901428321171243537726808304511417839729893485437723588066736562486119811972254336254931055762957544224856467924594919948181906811440140010714196954279656798263622155177066986905856385133202867294148850970209614832260479950724432759414228396200341140605306788845685951695759643766232185454977460106973857446555420993112772600084827475272084256700395200921605217524460271289459006613018493472435608299277877538207965230567374197762114200557415925319268029377126829378726165211041) (b:=24763848962542736269335941964723986468939221267013721244447167434563488986164241548694846063639781737625196305240243268820710315847642748489346983326237521043226908095913631144824554181746631557264176376163614215406067479272776958440557011101349465486332348531107121925459674236595534326192084368002398176315699252088030645590805928540406207601933533000509132590701257915154620570188931495079444751825680279641160129817675831857599997422356954912551399409) (by decide +kernel) (by decide +kernel) (merge_factors (a:=16283348597625108250076619294027337647332706521036862687708121384977570643494793624264391975128114105738305611897724296040282793814618398437150964126892775119670054371547313324625825123673720366493725066796079175389281) (b:=2372160429982752598923785373589379573035845202600447874820045932390721548842134162641716897172388985546212659257199409154489583485943664668818876024310249319198563795722825002671898432169697125937553020306218381877500731178308074037043793135875464452605870667292693552961) (by decide +kernel) (by decide +kernel) (merge_factors (a:=21547804015033219335590420271323195613536806683998861370353250037189408009) (b:=755684829241287532758055091570307314668155506950290108650913214650384571879698240801061993796554963090098741819265902194145539398710812691590809) (by decide +kernel) (by decide +kernel) h4641961225067828949883765940427568003 (merge_factors (a:=1699725171023370455813211904940925845936278460039969939304358560344381809) (b:=444592362414863130009708516282058956264442292126158506477195900320601001) (by decide +kernel) (by decide +kernel) h1303735084679157683598839450173753447 h666777595915506994631062445239824499)) (merge_factors (a:=6145956922994253718035477922543318475948368160313645589855857254184753889725227281241600191260070561816571961850425096278895756128088001) (b:=385970884551377207310848180080039635193082847822331519440339502599899577098412196618829983377193590241895448262136026954622911008984961) (by decide +kernel) (by decide +kernel) (merge_factors (a:=88021644600252879312459968285026808351734060383803900203816690107049) (b:=69823245758539222563609486651307778181276867975907865970346985327449) (by decide +kernel) (by decide +kernel) h9381985109786354767110386300724493 h8356030502489757101617244948199643) (merge_factors (a:=19663713925099058906708011249997760066153045033261837441229205235529) (b:=19628585221569878037094889296235545110139776420249220258710920498809) (by decide +kernel) (by decide +kernel) h4434378640249280619239798433503773 h4430415919704365412830979702590197))) (merge_factors (a:=119887275581772101496512367198971067566383447112167856103807488223152757038425128196863108516067341874397895590552644566044673488652629882777884453537236445092661689170744973756395078297630322368281) (b:=206559443797285529823231054133740531357163899926695057277700362643065421167747446656956438888153694467874968591131187950635044435587915865571207948615730158454337765696413620136795184707038357941855275359414699487052032739775800500704816797443008347890510489) (by decide +kernel) (by decide +kernel) (merge_factors (a:=5815294676283080354204206106191241247430881910872636818309509889689) (b:=20615855645409800687834822067757841772820510343962927323425754788467691529293115176063025156650646421322102662507104114234647065729) (by decide +kernel) (by decide +kernel) h2411492209459338136097875027992133 (merge_factors (a:=151050829115282255410729013848151694491135684274632844299383150921) (b:=136482902915254730675862061601205682173147814496950896594904758649) (by decide +kernel) (by decide +kernel) h388652581511151493098476509218589 h369435925317577541457299485375093)) (merge_factors (a:=4434747089336056820822959979765315202033735984335978643033376874583737565221231809407078514177366408838115942661449673173259295641) (b:=46577502535372393679093173074999541762472378153246105595492550701001828955665082306579992185752854937308582458456419853610460929) (by decide +kernel) (by decide +kernel) (merge_factors (a:=130209533432326744545059124681993013980753771747843573554928589249) (b:=34058543736668170703013705565194525279694713898237951144401307609) (by decide +kernel) (by decide +kernel) h360845581145629029504245626950943 h184549569863135066324678230069147) (merge_factors (a:=14467723549118334907300774463665342924080230176110810257408245129) (b:=3219407834082566029233133332729863079510882681494636423741110201) (by decide +kernel) (by decide +kernel) h120281850455994959752320782994877 h56739825819987904059035875856149)))))

/-- Product of the forced prime squares in the 18-branch. -/
theorem branch18 {n : ℕ} (hn : Noe.Exceptional n) (branch : 27 ∣ n) : 722071148305318044676647401794025765610430254815580770325628390633964214455014546783201311884231223820231417962086594541595410636046647751504614275520595561229655193201109732538545419925878853978685859856942466952338362806477858031927273139239172802318721592031959529688529515336737214598900685716469026446347341545173324452725815120222650326132798422365007909735028458713405186339641051261484160966472989408825988663518308593567601196519870791867222324904640548532915207490895741575242268350945862530937252999007875203761215807167126633271138746859879661263770116774725626638271289712082226103478713866501535648828722413141785608964519961128546651622135260945330325027735761161494730263297322569724473742624220252614368096987462887880433728792773387228270901237510590521355565436705274519045588840267992311896472102027097088821100813992575124695356786417746606068569324722682611395730036525892805293622992088658669584333600246396920713119374347245854006389072391240100242668947340532464090095089134028511192137713142274703204 ∣ n := by
  have entry := Noe.sylvester_divisor hn
  have base : 36 ∣ n := (by decide +kernel : 36 ∣ 3261636).trans entry
  have h7 : 49 ∣ n := (by decide +kernel : 49 ∣ 3261636).trans entry
  have h43 : 1849 ∣ n := (by decide +kernel : 1849 ∣ 3261636).trans entry
  have h19 : 361 ∣ n :=
    Noe.square_eighteen hn branch base (k:=1) (by decide +kernel)
      (one_dvd n) prime19
  have h127 : 16129 ∣ n :=
    Noe.square_eighteen hn branch base (k:=7) (by decide +kernel)
      h7 prime127
  have h5419 : 29365561 ∣ n :=
    Noe.square_eighteen hn branch base (k:=301) (by decide +kernel)
      (merge_factors (a:=49) (b:=1849) (by decide +kernel) (by decide +kernel) h7 h43) prime5419
  have h2287 : 5230369 ∣ n :=
    Noe.square_eighteen hn branch base (k:=127) (by decide +kernel)
      h127 prime2287
  have h4903 : 24039409 ∣ n :=
    Noe.square_six hn base (k:=817) (by decide +kernel)
      (merge_factors (a:=361) (b:=1849) (by decide +kernel) (by decide +kernel) h19 h43) prime4903
  have h14479 : 209641441 ∣ n :=
    Noe.square_six hn base (k:=2413) (by decide +kernel)
      (merge_factors (a:=361) (b:=16129) (by decide +kernel) (by decide +kernel) h19 h127) prime14479
  have h98299 : 9662693401 ∣ n :=
    Noe.square_eighteen hn branch base (k:=5461) (by decide +kernel)
      (merge_factors (a:=1849) (b:=16129) (by decide +kernel) (by decide +kernel) h43 h127) prime98299
  have h101347 : 10271214409 ∣ n :=
    Noe.square_six hn base (k:=16891) (by decide +kernel)
      (merge_factors (a:=49) (b:=5822569) (by decide +kernel) (by decide +kernel) h7 (merge_factors (a:=361) (b:=16129) (by decide +kernel) (by decide +kernel) h19 h127)) prime101347
  have h304039 : 92439713521 ∣ n :=
    Noe.square_eighteen hn branch base (k:=16891) (by decide +kernel)
      (merge_factors (a:=49) (b:=5822569) (by decide +kernel) (by decide +kernel) h7 (merge_factors (a:=361) (b:=16129) (by decide +kernel) (by decide +kernel) h19 h127)) prime304039
  have h617767 : 381636066289 ∣ n :=
    Noe.square_six hn base (k:=102961) (by decide +kernel)
      (merge_factors (a:=361) (b:=29365561) (by decide +kernel) (by decide +kernel) h19 h5419) prime617767
  have h71503878951240076806530665340943361223587 : 5112804705073593706227280318489644452673362960117478571456049153147327561805146569 ∣ n :=
    Noe.square_eighteen hn branch base (k:=3972437719513337600362814741163520067977) (by decide +kernel)
      (merge_factors (a:=21498544666043572036684357489) (b:=734015333621017847494537299623022746892905134971361) (by decide +kernel) (by decide +kernel) (merge_factors (a:=5822569) (b:=3692278213627622452681) (by decide +kernel) (by decide +kernel) (merge_factors (a:=361) (b:=16129) (by decide +kernel) (by decide +kernel) h19 h127) (merge_factors (a:=5230369) (b:=705930731393449) (by decide +kernel) (by decide +kernel) h2287 (merge_factors (a:=24039409) (b:=29365561) (by decide +kernel) (by decide +kernel) h4903 h5419))) (merge_factors (a:=2025700968526830841) (b:=362351277422166892735963190535721) (by decide +kernel) (by decide +kernel) (merge_factors (a:=209641441) (b:=9662693401) (by decide +kernel) (by decide +kernel) h14479 h98299) (merge_factors (a:=10271214409) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h101347 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime71503878951240076806530665340943361223587
  have h209033027051691026084765695129550923423 : 43694806398392992305141025855074300856394386214760577136468189729752010036929 ∣ n :=
    Noe.square_six hn base (k:=34838837841948504347460949188258487237) (by decide +kernel)
      (merge_factors (a:=1653568483630964667052729) (b:=734015333621017847494537299623022746892905134971361) (by decide +kernel) (by decide +kernel) (merge_factors (a:=667489) (b:=2477296979622083161) (by decide +kernel) (by decide +kernel) (merge_factors (a:=361) (b:=1849) (by decide +kernel) (by decide +kernel) h19 h43) (merge_factors (a:=16129) (b:=153592719922009) (by decide +kernel) (by decide +kernel) h127 (merge_factors (a:=5230369) (b:=29365561) (by decide +kernel) (by decide +kernel) h2287 h5419))) (merge_factors (a:=2025700968526830841) (b:=362351277422166892735963190535721) (by decide +kernel) (by decide +kernel) (merge_factors (a:=209641441) (b:=9662693401) (by decide +kernel) (by decide +kernel) h14479 h98299) (merge_factors (a:=10271214409) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h101347 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime209033027051691026084765695129550923423
  have h70758446940448836735802329175443917167 : 5006757813424313344310185268993530417454495949979461975503931956901157305889 ∣ n :=
    Noe.square_eighteen hn branch base (k:=3931024830024935374211240509746884287) (by decide +kernel)
      (merge_factors (a:=21052634061526492064929) (b:=734015333621017847494537299623022746892905134971361) (by decide +kernel) (by decide +kernel) (merge_factors (a:=29822521) (b:=705930731393449) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1849) (b:=16129) (by decide +kernel) (by decide +kernel) h43 h127) (merge_factors (a:=24039409) (b:=29365561) (by decide +kernel) (by decide +kernel) h4903 h5419)) (merge_factors (a:=2025700968526830841) (b:=362351277422166892735963190535721) (by decide +kernel) (by decide +kernel) (merge_factors (a:=209641441) (b:=9662693401) (by decide +kernel) (by decide +kernel) h14479 h98299) (merge_factors (a:=10271214409) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h101347 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime70758446940448836735802329175443917167
  have h34569179684969993621501115918682473139 : 1195028184091742107444952811624647143097447240654624671669586422789456513321 ∣ n :=
    Noe.square_eighteen hn branch base (k:=1920509982498332978972284217704581841) (by decide +kernel)
      (merge_factors (a:=35872929130696159007401) (b:=102817324435312150342877733982257598955691046829881) (by decide +kernel) (by decide +kernel) (merge_factors (a:=17689) (b:=2027979486160673809) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=361) (by decide +kernel) (by decide +kernel) h7 h19) (merge_factors (a:=16129) (b:=125734979611921) (by decide +kernel) (by decide +kernel) h127 (merge_factors (a:=5230369) (b:=24039409) (by decide +kernel) (by decide +kernel) h2287 h4903))) (merge_factors (a:=283750412491362961) (b:=362351277422166892735963190535721) (by decide +kernel) (by decide +kernel) (merge_factors (a:=29365561) (b:=9662693401) (by decide +kernel) (by decide +kernel) h5419 h98299) (merge_factors (a:=10271214409) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h101347 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime34569179684969993621501115918682473139
  have h3841246187888128489959068718127623103 : 14755172275965079321031453213834395672419234959348724909579071564419348609 ∣ n :=
    Noe.square_six hn base (k:=640207697981354748326511453021270517) (by decide +kernel)
      (merge_factors (a:=183736969425643207769209) (b:=2230720893219340850602813433804319822925028997121) (by decide +kernel) (by decide +kernel) (merge_factors (a:=90601) (b:=2027979486160673809) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=1849) (by decide +kernel) (by decide +kernel) h7 h43) (merge_factors (a:=16129) (b:=125734979611921) (by decide +kernel) (by decide +kernel) h127 (merge_factors (a:=5230369) (b:=24039409) (by decide +kernel) (by decide +kernel) h2287 h4903))) (merge_factors (a:=6156238523813401) (b:=362351277422166892735963190535721) (by decide +kernel) (by decide +kernel) (merge_factors (a:=29365561) (b:=209641441) (by decide +kernel) (by decide +kernel) h5419 h14479) (merge_factors (a:=10271214409) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h101347 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime3841246187888128489959068718127623103
  have h557395016235180539513922446377617163 : 310689204123817177225812754608881758375208700750736502263676117792168569 ∣ n :=
    Noe.square_eighteen hn branch base (k:=30966389790843363306329024798756509) (by decide +kernel)
      (merge_factors (a:=4112409074502895282081) (b:=233176534558240958383827878402011339334461785001) (by decide +kernel) (by decide +kernel) (merge_factors (a:=17689) (b:=232483977302441929) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=361) (by decide +kernel) (by decide +kernel) h7 h19) (merge_factors (a:=1849) (b:=125734979611921) (by decide +kernel) (by decide +kernel) h43 (merge_factors (a:=5230369) (b:=24039409) (by decide +kernel) (by decide +kernel) h2287 h4903))) (merge_factors (a:=6156238523813401) (b:=37876462007811032683441134531601) (by decide +kernel) (by decide +kernel) (merge_factors (a:=29365561) (b:=209641441) (by decide +kernel) (by decide +kernel) h5419 h14479) (merge_factors (a:=9662693401) (b:=3919865863061655958201) (by decide +kernel) (by decide +kernel) h98299 (merge_factors (a:=10271214409) (b:=381636066289) (by decide +kernel) (by decide +kernel) h101347 h617767)))) prime557395016235180539513922446377617163
  have h270018673069170913931234520374027767 : 72910083806035805784602932220455136470961318197728078277730450487006289 ∣ n :=
    Noe.square_six hn base (k:=45003112178195152321872420062337961) (by decide +kernel)
      (merge_factors (a:=2759179560639664561) (b:=734015333621017847494537299623022746892905134971361) (by decide +kernel) (by decide +kernel) (merge_factors (a:=17689) (b:=155982789340249) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=361) (by decide +kernel) (by decide +kernel) h7 h19) (merge_factors (a:=1849) (b:=84360621601) (by decide +kernel) (by decide +kernel) h43 (merge_factors (a:=16129) (b:=5230369) (by decide +kernel) (by decide +kernel) h127 h2287))) (merge_factors (a:=2025700968526830841) (b:=362351277422166892735963190535721) (by decide +kernel) (by decide +kernel) (merge_factors (a:=209641441) (b:=9662693401) (by decide +kernel) (by decide +kernel) h14479 h98299) (merge_factors (a:=10271214409) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h101347 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime270018673069170913931234520374027767
  have h261950813418014380202859535754160127 : 68618228650359382654396342687590432971544649063645890926279387156656129 ∣ n :=
    Noe.square_eighteen hn branch base (k:=14552822967667465566825529764120007) (by decide +kernel)
      (merge_factors (a:=3749734069911085872841) (b:=56479913609791416960732984647219686294598469289) (by decide +kernel) (by decide +kernel) (merge_factors (a:=29822521) (b:=125734979611921) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1849) (b:=16129) (by decide +kernel) (by decide +kernel) h43 h127) (merge_factors (a:=5230369) (b:=24039409) (by decide +kernel) (by decide +kernel) h2287 h4903)) (merge_factors (a:=6156238523813401) (b:=9174419313240916659155168636689) (by decide +kernel) (by decide +kernel) (merge_factors (a:=29365561) (b:=209641441) (by decide +kernel) (by decide +kernel) h5419 h14479) (merge_factors (a:=9662693401) (b:=949468117480727324089) (by decide +kernel) (by decide +kernel) h98299 (merge_factors (a:=10271214409) (b:=92439713521) (by decide +kernel) (by decide +kernel) h101347 h304039)))) prime261950813418014380202859535754160127
  have h82096375219206345679665135708014443 : 6739814824132717762646259697254934342798613211475359468374061496600249 ∣ n :=
    Noe.square_six hn base (k:=13682729203201057613277522618002407) (by decide +kernel)
      (merge_factors (a:=83926715806181536369) (b:=2230720893219340850602813433804319822925028997121) (by decide +kernel) (by decide +kernel) (merge_factors (a:=667489) (b:=125734979611921) (by decide +kernel) (by decide +kernel) (merge_factors (a:=361) (b:=1849) (by decide +kernel) (by decide +kernel) h19 h43) (merge_factors (a:=5230369) (b:=24039409) (by decide +kernel) (by decide +kernel) h2287 h4903)) (merge_factors (a:=6156238523813401) (b:=362351277422166892735963190535721) (by decide +kernel) (by decide +kernel) (merge_factors (a:=29365561) (b:=209641441) (by decide +kernel) (by decide +kernel) h5419 h14479) (merge_factors (a:=10271214409) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h101347 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime82096375219206345679665135708014443
  have h78379110417272215440461953312051279 : 6143284949802949922019433557511558002262559079293610666351774725535841 ∣ n :=
    Noe.square_six hn base (k:=13063185069545369240076992218675213) (by decide +kernel)
      (merge_factors (a:=48738276011095218814379689) (b:=3501289297191092325560466356568416961477121) (by decide +kernel) (by decide +kernel) (merge_factors (a:=9670952281) (b:=5039656343548369) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1849) (b:=5230369) (by decide +kernel) (by decide +kernel) h43 h2287) (merge_factors (a:=24039409) (b:=209641441) (by decide +kernel) (by decide +kernel) h4903 h14479)) (merge_factors (a:=99247595690100415009) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) (merge_factors (a:=9662693401) (b:=10271214409) (by decide +kernel) (by decide +kernel) h98299 h101347) (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767))) prime78379110417272215440461953312051279
  have h44637471330223523736590837979281983 : 1992503846756527037667345967342568830617443468393058992972744228412289 ∣ n :=
    Noe.square_eighteen hn branch base (k:=2479859518345751318699490998848999) (by decide +kernel)
      (merge_factors (a:=8378167252164241) (b:=734015333621017847494537299623022746892905134971361) (by decide +kernel) (by decide +kernel) (merge_factors (a:=17689) (b:=473637133369) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=361) (by decide +kernel) (by decide +kernel) h7 h19) (merge_factors (a:=16129) (b:=29365561) (by decide +kernel) (by decide +kernel) h127 h5419)) (merge_factors (a:=2025700968526830841) (b:=362351277422166892735963190535721) (by decide +kernel) (by decide +kernel) (merge_factors (a:=209641441) (b:=9662693401) (by decide +kernel) (by decide +kernel) h14479 h98299) (merge_factors (a:=10271214409) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h101347 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime44637471330223523736590837979281983
  have h14667180345286093576766435952749923 : 215126179281146691197040685658417051233308679079256978201425776505929 ∣ n :=
    Noe.square_eighteen hn branch base (k:=814843352515894087598135330708329) (by decide +kernel)
      (merge_factors (a:=2759179560639664561) (b:=240640260826451103710177459717041056722607254881) (by decide +kernel) (by decide +kernel) (merge_factors (a:=17689) (b:=155982789340249) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=361) (by decide +kernel) (by decide +kernel) h7 h19) (merge_factors (a:=1849) (b:=84360621601) (by decide +kernel) (by decide +kernel) h43 (merge_factors (a:=16129) (b:=5230369) (by decide +kernel) (by decide +kernel) h127 h2287))) (merge_factors (a:=705930731393449) (b:=340883673319402160048946784338169) (by decide +kernel) (by decide +kernel) (merge_factors (a:=24039409) (b:=29365561) (by decide +kernel) (by decide +kernel) h4903 h5419) (merge_factors (a:=9662693401) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) h98299 (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) prime14667180345286093576766435952749923
  have h5077898000961363149246511915945679 : 25785048108167408026589347834642634150103890677469551508424878771041 ∣ n :=
    Noe.square_six hn base (k:=846316333493560524874418652657613) (by decide +kernel)
      (merge_factors (a:=12681523227645544321) (b:=56479913609791416960732984647219686294598469289) (by decide +kernel) (by decide +kernel) (merge_factors (a:=17689) (b:=716915779730089) (by decide +kernel) (by decide +kernel) (merge_factors (a:=49) (b:=361) (by decide +kernel) (by decide +kernel) h7 h19) (merge_factors (a:=1849) (b:=387731627761) (by decide +kernel) (by decide +kernel) h43 (merge_factors (a:=16129) (b:=24039409) (by decide +kernel) (by decide +kernel) h127 h4903))) (merge_factors (a:=6156238523813401) (b:=9174419313240916659155168636689) (by decide +kernel) (by decide +kernel) (merge_factors (a:=29365561) (b:=209641441) (by decide +kernel) (by decide +kernel) h5419 h14479) (merge_factors (a:=9662693401) (b:=949468117480727324089) (by decide +kernel) (by decide +kernel) h98299 (merge_factors (a:=10271214409) (b:=92439713521) (by decide +kernel) (by decide +kernel) h101347 h304039)))) prime5077898000961363149246511915945679
  exact (merge_factors (a:=51469468787152518153099758237275586339627377878192217049788001372742212756463071997444) (b:=14029116004507061434304321475169760788471536775697380821233833580108566312349572019859291160803378824326568037107189315599003648112630100314861961587288352607209947681159878947507592945690466822603558497047579452931788684552578846053223985956751978347734242989489355929595075000567769143994770313044618423338207218720325732675754379119103771131371902301327008525898088468249971793871214433125109508182864174402319332870662937857155316668824396401682266520049477744600573267484024374090422153544976062331885107584984995815549371450494085841843397311153538439030907352478372505363639274605437636591995092134745658433665731742316302168528598465063466322231098794026311123409393340254638943082009891763806930497619458519849966737221616161722025352451675445114443289694391465975431516146729256148690619061370060900502419267207173274923627385972257581020277826449278782312313188716530180262318366028701724316393401763509020877688751597388477182041) (by decide +kernel) (by decide +kernel) (merge_factors (a:=557684324973060537924) (b:=92291403007676069978057712239522231919721444696069644033229194481) (by decide +kernel) (by decide +kernel) (merge_factors (a:=3261636) (b:=170983005146209) (by decide +kernel) (by decide +kernel) (merge_factors (a:=36) (b:=90601) (by decide +kernel) (by decide +kernel) base (merge_factors (a:=49) (b:=1849) (by decide +kernel) (by decide +kernel) h7 h43)) (merge_factors (a:=361) (b:=473637133369) (by decide +kernel) (by decide +kernel) h19 (merge_factors (a:=16129) (b:=29365561) (by decide +kernel) (by decide +kernel) h127 h5419))) (merge_factors (a:=26359262309948739218161) (b:=3501289297191092325560466356568416961477121) (by decide +kernel) (by decide +kernel) (merge_factors (a:=5230369) (b:=5039656343548369) (by decide +kernel) (by decide +kernel) h2287 (merge_factors (a:=24039409) (b:=209641441) (by decide +kernel) (by decide +kernel) h4903 h14479)) (merge_factors (a:=99247595690100415009) (b:=35278328637036525593569) (by decide +kernel) (by decide +kernel) (merge_factors (a:=9662693401) (b:=10271214409) (by decide +kernel) (by decide +kernel) h98299 h101347) (merge_factors (a:=92439713521) (b:=381636066289) (by decide +kernel) (by decide +kernel) h304039 h617767)))) (merge_factors (a:=6127653552092020217639651722794483542152743201756011654768489209132301349631079285247548841299469772349368431370399428121835863288849832995070692751979739783588806898568455893621622117541784568205943089448601811070444671924801403676817621008908371800306456934909701734471658849838356729748873518522007086808484552580977596640129393333724758277090548955725887289310989199798359915081097688714078482478930784573586814172576004989879925058288742994516512649) (b:=2289476042541183038245781243483313150082053292614285413958394725957436164287494751053983178254225339663701501910215481902521949586362607850835866568263542720779048287336862159446299702156092792815839365127959291056878182829809409829863123801216069107761157560211761062765883125193351228819902647137095031774193708086239500644326033621503199686040165590788164021123655723986252017404093747943760775603810500657702203105391537611053572758651000263554635932523283999499881971853998024201809) (by decide +kernel) (by decide +kernel) (merge_factors (a:=1118524774576692540900155641256556615089737079852940492431408928206159354076524271934393729654370698352808350751930978601492913103991375605936516628362842346922112224681226257977375605681568394271224684304892968050856711393587028133289) (b:=5478335117262861107592043591599474594839717034679024541286852356275120949878177714003344756366412095676092939542630688280620468381635523778181511296764038049344044663042458897082207947958939336031430517068547247231510241) (by decide +kernel) (by decide +kernel) (merge_factors (a:=5112804705073593706227280318489644452673362960117478571456049153147327561805146569) (b:=218769313341216794300101923334194682909503097355592783639573527186053136121141958657372311570763872706603270010988886951370787237028483556085425039174881) (by decide +kernel) (by decide +kernel) h71503878951240076806530665340943361223587 (merge_factors (a:=43694806398392992305141025855074300856394386214760577136468189729752010036929) (b:=5006757813424313344310185268993530417454495949979461975503931956901157305889) (by decide +kernel) (by decide +kernel) h209033027051691026084765695129550923423 h70758446940448836735802329175443917167)) (merge_factors (a:=1195028184091742107444952811624647143097447240654624671669586422789456513321) (b:=4584272731129402606738689826444919254258839314924312608784351729074394637630895130164518726652929434925045905990586014006342432425137956503670521) (by decide +kernel) (by decide +kernel) h34569179684969993621501115918682473139 (merge_factors (a:=14755172275965079321031453213834395672419234959348724909579071564419348609) (b:=310689204123817177225812754608881758375208700750736502263676117792168569) (by decide +kernel) (by decide +kernel) h3841246187888128489959068718127623103 h557395016235180539513922446377617163))) (merge_factors (a:=33719029374635556392686099877925389528687277794371150783515198753859014350378955050812393109096438172492997331793316397115888984377800348569628463242502225359317825371845715408320041495304666435070158082860024969) (b:=67898634243113596784576147580281301263443661541856677165262080342709065412817598999443755497594234941226451737875415179735270786496397976948109592955069587814210564416392899676982444854645718976601340163914966668395494206409103728336267559328474456005347513885008477927252361) (by decide +kernel) (by decide +kernel) (merge_factors (a:=72910083806035805784602932220455136470961318197728078277730450487006289) (b:=462474154663420537924814112652550219644998640745561842138593814000043816364686826489361385664918635338552711131615584796769625832704668776121) (by decide +kernel) (by decide +kernel) h270018673069170913931234520374027767 (merge_factors (a:=68618228650359382654396342687590432971544649063645890926279387156656129) (b:=6739814824132717762646259697254934342798613211475359468374061496600249) (by decide +kernel) (by decide +kernel) h261950813418014380202859535754160127 h82096375219206345679665135708014443)) (merge_factors (a:=12240518894203855826389937325935278651209183668297873424380116765514356904016508786350773724556254571568987029582588453173052389692194350049) (b:=5547038882090614139061877201459604388286806845636623600856242229119743481229101341717390451839684509727198031766008043366750244570002089) (by decide +kernel) (by decide +kernel) (merge_factors (a:=6143284949802949922019433557511558002262559079293610666351774725535841) (b:=1992503846756527037667345967342568830617443468393058992972744228412289) (by decide +kernel) (by decide +kernel) h78379110417272215440461953312051279 h44637471330223523736590837979281983) (merge_factors (a:=215126179281146691197040685658417051233308679079256978201425776505929) (b:=25785048108167408026589347834642634150103890677469551508424878771041) (by decide +kernel) (by decide +kernel) h14667180345286093576766435952749923 h5077898000961363149246511915945679)))))

/-- Every positive input at most 10^1000 admits a distinct totient sibling at most twice itself. -/
theorem thousand_digits {n : ℕ} (hn : Noe.Exceptional n) : 10^1000 < n := by
  by_cases cube : 27 ∣ n
  · exact (by decide +kernel : 10^1000 < 722071148305318044676647401794025765610430254815580770325628390633964214455014546783201311884231223820231417962086594541595410636046647751504614275520595561229655193201109732538545419925878853978685859856942466952338362806477858031927273139239172802318721592031959529688529515336737214598900685716469026446347341545173324452725815120222650326132798422365007909735028458713405186339641051261484160966472989408825988663518308593567601196519870791867222324904640548532915207490895741575242268350945862530937252999007875203761215807167126633271138746859879661263770116774725626638271289712082226103478713866501535648828722413141785608964519961128546651622135260945330325027735761161494730263297322569724473742624220252614368096987462887880433728792773387228270901237510590521355565436705274519045588840267992311896472102027097088821100813992575124695356786417746606068569324722682611395730036525892805293622992088658669584333600246396920713119374347245854006389072391240100242668947340532464090095089134028511192137713142274703204).trans_le (Nat.le_of_dvd hn.1 (branch18 hn cube))
  · exact (by decide +kernel : 10^1000 < 508052094112639059070587694754755272431041485314043201086038239294943900028247267592852400962467236850116949010636185499445664351805878405992352692910028881506567251622828013464781740704744481414664053342541375956571628386248312907445272634414400937692437999948826000952094551030405965627529623960047048764929628940831376905190844004521302030693359017157009159972029738953724265835550751298848838023823838700322247077418957621504959351785364694721769847522195392234659010337611974541888734554116902182724673774302624768997560077254434732581227536148383049111009051124322123818234086775740617299371753755268953293003070871410625044181726540479555332705937271017249264214602167357205403656790787414865873932871400487094093057176669656573712975074920977666711382486853460616415989357882784262831989346100166276117916404377446205746848570048823211011932543721594794713622844990851295724132869691974066183898308868745444899852700031799478970569382456757059079836708787354555157849911042632073862120700535195084305167969556324).trans_le (Nat.le_of_dvd hn.1 (branch12 hn cube))

end NoeCensus

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

namespace NoeCensus

/-- The positive assertion of the registered A074987 problem through 10^1000. -/
theorem bounded_twin {n : ℕ} (hn : 0 < n) (within : n ≤ 10^1000) :
    ∃ m, m ≠ n ∧ m ≤ 2*n ∧ m.totient = n.totient := by
  by_contra none
  have ex : Noe.Exceptional n := ⟨hn, fun m le eq => Classical.byContradiction
    (fun ne => none ⟨m,ne,le,eq⟩)⟩
  exact (Nat.not_lt_of_ge within) (thousand_digits ex)

/-- Only multiples of the two certified branch divisors can be exceptional. -/
theorem exceptional_count {N : ℕ} (S : Finset ℕ)
    (fail : ∀ n ∈ S, Noe.Exceptional n ∧ n ≤ N) :
    S.card ≤ 2 * (N / 10^1000) := by
  let a : ℕ := 508052094112639059070587694754755272431041485314043201086038239294943900028247267592852400962467236850116949010636185499445664351805878405992352692910028881506567251622828013464781740704744481414664053342541375956571628386248312907445272634414400937692437999948826000952094551030405965627529623960047048764929628940831376905190844004521302030693359017157009159972029738953724265835550751298848838023823838700322247077418957621504959351785364694721769847522195392234659010337611974541888734554116902182724673774302624768997560077254434732581227536148383049111009051124322123818234086775740617299371753755268953293003070871410625044181726540479555332705937271017249264214602167357205403656790787414865873932871400487094093057176669656573712975074920977666711382486853460616415989357882784262831989346100166276117916404377446205746848570048823211011932543721594794713622844990851295724132869691974066183898308868745444899852700031799478970569382456757059079836708787354555157849911042632073862120700535195084305167969556324
  let b : ℕ := 722071148305318044676647401794025765610430254815580770325628390633964214455014546783201311884231223820231417962086594541595410636046647751504614275520595561229655193201109732538545419925878853978685859856942466952338362806477858031927273139239172802318721592031959529688529515336737214598900685716469026446347341545173324452725815120222650326132798422365007909735028458713405186339641051261484160966472989408825988663518308593567601196519870791867222324904640548532915207490895741575242268350945862530937252999007875203761215807167126633271138746859879661263770116774725626638271289712082226103478713866501535648828722413141785608964519961128546651622135260945330325027735761161494730263297322569724473742624220252614368096987462887880433728792773387228270901237510590521355565436705274519045588840267992311896472102027097088821100813992575124695356786417746606068569324722682611395730036525892805293622992088658669584333600246396920713119374347245854006389072391240100242668947340532464090095089134028511192137713142274703204
  let D : Finset ℕ := {a,b}
  have floors : ∀ x ∈ D, 10^1000 ≤ x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hb
    · decide +kernel
    · obtain rfl := Finset.mem_singleton.mp hb
      decide +kernel
  have bounds := TotientDensity.count_covered (N:=N) (B:=10^1000) D S (by positivity)
    (fun n h => ⟨(fail n h).1.1,(fail n h).2⟩) (fun n h => by
      by_cases cube : 27 ∣ n
      · exact ⟨b,by simp [D],branch18 (fail n h).1 cube⟩
      · exact ⟨a,by simp [D],branch12 (fail n h).1 cube⟩) floors
  have size : D.card=2 := by decide +kernel
  rwa [size] at bounds

open scoped Classical in
/-- Counts the failures directly in the positive interval using the registered witness formulation. -/
theorem nontwin_count (N : ℕ) :
    ((Finset.Icc 1 N).filter fun n => ¬ ∃ m, m ≠ n ∧ m ≤ 2*n ∧ m.totient = n.totient).card ≤
      2 * (N / 10^1000) := by
  apply exceptional_count
  intro n h
  obtain ⟨I,none⟩ := Finset.mem_filter.mp h
  obtain ⟨pos,le⟩ := Finset.mem_Icc.mp I
  exact ⟨⟨pos, fun m small eq => Classical.byContradiction (fun ne => none ⟨m,ne,small,eq⟩)⟩,le⟩

end NoeCensus

#print axioms Noe.bounded_ford_rule
#print axioms Noe.square_six
#print axioms Noe.square_twelve
#print axioms Noe.square_eighteen
#print axioms NoeCensus.branch12
#print axioms NoeCensus.branch18
#print axioms NoeCensus.thousand_digits
#print axioms NoeCensus.bounded_twin
#print axioms NoeCensus.exceptional_count
#print axioms NoeCensus.nontwin_count
