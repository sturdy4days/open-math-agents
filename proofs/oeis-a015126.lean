import OMAStatements.S_oeis_a015126

/-!
# An odd input with even least totient preimage

This counterexample refutes Jianing Song’s 2022 conjecture in OEIS A015126 and the equivalent
form in A143510. The registered statement is due to @Dugongue. Formal proof by @sturdy4days.
For the number 25,387,551,686,656 we certify an odd preimage, a smaller even preimage and
a lower bound for every odd preimage. Prime-power peeling gives a finite table of admissible
factorizations whose totients equal the target.

https://oeis.org/A015126
https://oeis.org/A143510
-/

namespace OMA.S_oeis_a015126

/-- Remove the full power of any specified prime divisor of an odd integer. -/
theorem peel_at_prime {x p : ℕ} (hx : 1 < x) (oddx : Odd x) (hp : p.Prime) (hpx : p ∣ x) :
    ∃ k y : ℕ, 2 < p ∧ x = p^(k+1)*y ∧ ¬p ∣ y ∧
      Nat.totient x = ((p-1)*p^k)*Nat.totient y ∧ p-1 ∣ Nat.totient x ∧
      0 < y ∧ y < x ∧ Odd y := by
  have hx0 : x ≠ 0 := by omega
  have pbig : 2 < p := by
    have low := hp.two_le
    have ne : p ≠ 2 := fun h => oddx.not_two_dvd_nat (h ▸ hpx)
    omega
  have hexp := hp.factorization_pos_of_dvd hx0 hpx
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hexp.ne'
  let y := ordCompl[p] x
  have hprod : p^(k+1)*y = x := by
    change p^k.succ*y = x
    rw [← hk]
    exact Nat.ordProj_mul_ordCompl_eq_self x p
  have hcop : (p^(k+1)).Coprime y := (Nat.coprime_ordCompl hp hx0).pow_left _
  have ht : x.totient = ((p-1)*p^k)*y.totient := by
    calc
      x.totient = (p^(k+1)*y).totient := congrArg Nat.totient hprod.symm
      _ = ((p-1)*p^k)*y.totient := by rw [Nat.totient_mul hcop,Nat.totient_prime_pow_succ hp,mul_comm (p^k)]
  have hy : 0 < y := Nat.ordCompl_pos p hx0
  have high : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
  refine ⟨k,y,pbig,hprod.symm,Nat.not_dvd_ordCompl hp hx0,ht,?_,hy,?_,?_⟩
  · exact ⟨p^k * y.totient,by rw [ht,mul_assoc]⟩
  · calc
      y = 1*y := (one_mul _).symm
      _ < p^(k+1)*y := Nat.mul_lt_mul_of_pos_right high hy
      _ = x := hprod
  · exact (Nat.odd_mul.mp (hprod ▸ oddx)).2

theorem peel_prime_power (x : ℕ) (hx : 1 < x) (oddx : Odd x) :
    ∃ p k y : ℕ, p.Prime ∧ p ∣ x ∧ 2 < p ∧ x = p^(k+1)*y ∧ ¬p ∣ y ∧
      Nat.totient x = ((p-1)*p^k)*Nat.totient y ∧ p-1 ∣ Nat.totient x ∧
      0 < y ∧ y < x ∧ Odd y := by
  obtain ⟨p,hp,hpx⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
  obtain ⟨k,y,rest⟩ := peel_at_prime hx oddx hp hpx
  exact ⟨p,k,y,hp,hpx,rest⟩

end OMA.S_oeis_a015126

namespace OMA.S_oeis_a015126

private def odd_factors : List ℕ := [1, 23, 257, 5911]

set_option maxRecDepth 4096 in
/-- All divisors of the proposed totient occur among four odd multiples of the
33 powers of two from 1 to 2^32. -/
private theorem divisor_shape {d : ℕ} (hd : d ∣ 25387551686656) :
    ∃ e < 33, ∃ t ∈ odd_factors, d = 2^e*t := by
  have h : d ∣ 2^32 * (23*257) := by norm_num; exact hd
  obtain ⟨u,w,hu,hw,hdw⟩ := exists_dvd_and_dvd_of_dvd_mul h
  obtain ⟨e,he,heu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
  obtain ⟨v,z,hv,hz,hwz⟩ := exists_dvd_and_dvd_of_dvd_mul hw
  have a := (Nat.dvd_prime (by decide : Nat.Prime 23)).mp hv
  have b := (Nat.dvd_prime (by decide : Nat.Prime 257)).mp hz
  refine ⟨e,by omega,w,?_,hdw.trans (by rw [heu])⟩
  rw [hwz]
  rcases a with rfl | rfl <;> rcases b with rfl | rfl <;> decide

private def odd_primes : List ℕ := [3,5,17,47,257,11777,65537,188417,12348030977]

/-- A short common list of proper factors witnesses every excluded case. -/
private def divisibility_witnesses : List ℕ :=
  [2,3,5,7,11,17,19,31,37,67,97,149,499,641,647,1031,1123,552841]

private theorem check_divisors :
    (List.range 33).all (fun e => odd_factors.all (fun t =>
      let p := 2^e*t+1
      decide (p=2 ∨ p∈odd_primes) || divisibility_witnesses.any (fun q =>
        decide (1<q ∧ q<p ∧ q∣p)))) = true := by decide +kernel

theorem admissible_prime {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p-1 ∣ 25387551686656) :
    p ∈ ([3,5,17,47,257,11777,65537,188417,12348030977] : List ℕ) := by
  obtain ⟨e,he,t,ht,d⟩ := divisor_shape hd
  have hpp : 2^e*t+1 = p := by have := hp.pos; omega
  have witness := List.all_eq_true.mp (List.all_eq_true.mp check_divisors e (List.mem_range.mpr he)) t ht
  dsimp only at witness
  rw [hpp] at witness
  rcases Bool.or_eq_true_iff.mp witness with yes | no
  · rcases of_decide_eq_true yes with two | ok
    · exact (ho.not_two_dvd_nat (two ▸ dvd_rfl)).elim
    · exact ok
  · obtain ⟨q,_,hq⟩ := List.any_eq_true.mp no
    obtain ⟨large,small,divides⟩ := of_decide_eq_true hq
    have factors := hp.eq_one_or_self_of_dvd q divides
    omega

end OMA.S_oeis_a015126

namespace OMA.S_oeis_a015126

private abbrev target : ℕ := 25387551686656

/-- Multiply a previously tabulated number by a full prime power, and update its totient. -/
private def attachFactor (p k : ℕ) (pair : ℕ × ℕ) : ℕ × ℕ :=
  (p^(k+1)*pair.1, ((p-1)*p^k)*pair.2)

def inverseTable : List ℕ → List (ℕ × ℕ)
  | [] => [(1,1)]
  | p::ps =>
    let rest := inverseTable ps
    (rest ++ rest.map (attachFactor p 0)) ++
      (if p ∣ target then rest.map (attachFactor p 1) else [])

/-- Every possible pair occurs, provided the primes in the support have squarefree
exponent in the target. Extra table entries do not affect completeness. -/
theorem table_complete (ps : List ℕ) {x : ℕ} (oddx : Odd x)
    (ht : x.totient ∣ target)
    (supported : ∀ p : ℕ, p.Prime → p ∣ x → p ∈ ps)
    (sq : ∀ p ∈ ps, ¬ p^2 ∣ target) :
    (x,x.totient) ∈ inverseTable ps := by
  induction ps generalizing x with
  | nil =>
    have h : x = 1 := by
      by_contra hn
      obtain ⟨p,hpr,hdiv⟩ := Nat.exists_prime_and_dvd hn
      simpa using supported p hpr hdiv
    subst x
    simp [inverseTable]
  | cons p ps ih =>
    have sqtail : ∀ q ∈ ps, ¬ q^2 ∣ target :=
      fun q hq => sq q (List.mem_cons_of_mem _ hq)
    by_cases useP : p.Prime ∧ p ∣ x
    · have hx : 1 < x := lt_of_lt_of_le useP.1.one_lt
          (Nat.le_of_dvd (by obtain ⟨n,hn⟩ := oddx; omega) useP.2)
      obtain ⟨k,y,_,hxy,hnd,htot,_,_,_,oddy⟩ := peel_at_prime hx oddx useP.1 useP.2
      have hyx : y ∣ x := hxy ▸ dvd_mul_left _ _
      have hyt : y.totient ∣ target := (htot ▸ dvd_mul_left _ _).trans ht
      have rest := ih oddy hyt (fun q hq hqy => by
        rcases List.mem_cons.mp (supported q hq (hqy.trans hyx)) with he | hm
        · exact False.elim (hnd (he ▸ hqy))
        · exact hm) sqtail
      have hk : p^k ∣ target :=
        (dvd_mul_of_dvd_left (dvd_mul_left (p^k) (p-1)) y.totient).trans (htot ▸ ht)
      have hklt : k < 2 := by
        by_contra! h
        exact sq p (by simp) ((pow_dvd_pow p h).trans hk)
      rcases (by omega : k=0 ∨ k=1) with hz | hz
      · subst k
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨(y,y.totient),rest,Prod.ext hxy.symm htot.symm⟩))
      · subst k
        have hpdiv : p ∣ target := by simpa using hk
        apply List.mem_append_right
        rw [if_pos hpdiv]
        exact List.mem_map.mpr ⟨(y,y.totient),rest,Prod.ext hxy.symm htot.symm⟩
    · apply List.mem_append_left
      apply List.mem_append_left
      exact ih oddx ht (fun q hq hqx => by
        rcases List.mem_cons.mp (supported q hq hqx) with he | hm
        · exact False.elim (useP (he ▸ And.intro hq hqx))
        · exact hm) sqtail

def possiblePrimes : List ℕ := [3,5,17,47,257,11777,65537,188417,12348030977]

set_option maxRecDepth 12000 in
theorem unique_from_support {x : ℕ} (oddx : Odd x) (ht : x.totient = target)
    (hs : ∀ p : ℕ, p.Prime → p ∣ x → p ∈ possiblePrimes) :
    x = 51878909956305 := by
  have sq : possiblePrimes.all (fun p => decide (¬ p^2 ∣ target)) = true := by decide
  have pair := table_complete possiblePrimes oddx (ht ▸ dvd_refl _) hs (by simpa using sq)
  have hcheck : (inverseTable possiblePrimes).all
      (fun v => decide (v.2 = target → v.1 = 51878909956305)) = true := by decide
  exact (of_decide_eq_true ((List.all_eq_true.mp hcheck) _ pair)) ht

end OMA.S_oeis_a015126

namespace OMA.S_oeis_a015126

theorem supported_at_target {x : ℕ} (oddx : Odd x) (ht : x.totient ∣ 25387551686656) :
    ∀ p : ℕ, p.Prime → p ∣ x → p ∈ possiblePrimes := by
  intro p hp hpx
  have hx : 1 < x := lt_of_lt_of_le hp.one_lt
    (Nat.le_of_dvd (by obtain ⟨n,hn⟩ := oddx; omega) hpx)
  obtain ⟨k,y,hp2,_,_,_,hd,_,_,_⟩ := peel_at_prime hx oddx hp hpx
  exact admissible_prime hp (hp.odd_of_ne_two (by omega)) (hd.trans ht)

theorem unique_odd_inverse {x : ℕ} (hx : Odd x) (ht : x.totient = 25387551686656) :
    x = 51878909956305 := unique_from_support hx ht (supported_at_target hx (ht ▸ dvd_refl _))

theorem odd_lower {x : ℕ} (hx : Odd x) (ht : x.totient = 25387551686656) :
    51878909956305 ≤ x := (unique_odd_inverse hx ht).ge

end OMA.S_oeis_a015126

namespace OMA.S_oeis_a015126

/-- The odd preimage has factorization 3 · 5 · 17 · 47 · 257² · 65537. -/
theorem odd_totient : Nat.totient 51878909956305 = 25387551686656 := by
  rw [show (51878909956305 : ℕ) = 3*(5*(17*(47*(257^2*65537)))) by decide]
  rw [Nat.totient_mul (by decide : Nat.Coprime 3 (5*(17*(47*(257^2*65537))))),
      Nat.totient_mul (by decide : Nat.Coprime 5 (17*(47*(257^2*65537)))),
      Nat.totient_mul (by decide : Nat.Coprime 17 (47*(257^2*65537))),
      Nat.totient_mul (by decide : Nat.Coprime 47 (257^2*65537)),
      Nat.totient_mul (by decide : Nat.Coprime (257^2) 65537)]
  rw [Nat.totient_prime (by norm_num1 : Nat.Prime 3), Nat.totient_prime (by norm_num1 : Nat.Prime 5),
      Nat.totient_prime (by norm_num1 : Nat.Prime 17), Nat.totient_prime (by norm_num1 : Nat.Prime 47),
      Nat.totient_prime_pow (by norm_num1 : Nat.Prime 257) (by decide : 0 < 2),
      Nat.totient_prime (by norm_num1 : Nat.Prime 65537)]
  decide

/-- This smaller preimage is 2¹² · 257² · 188417. -/
theorem even_totient : Nat.totient 50973714157568 = 25387551686656 := by
  rw [show (50973714157568 : ℕ) = 2^12*(257^2*188417) by decide]
  rw [Nat.totient_mul (by decide : Nat.Coprime (2^12) (257^2*188417)),
      Nat.totient_mul (by decide : Nat.Coprime (257^2) 188417),
      Nat.totient_prime_pow (by norm_num1 : Nat.Prime 2) (by decide : 0 < 12),
      Nat.totient_prime_pow (by norm_num1 : Nat.Prime 257) (by decide : 0 < 2),
      Nat.totient_prime (by norm_num1 : Nat.Prime 188417)]
  decide

theorem not_all_odd
    (lower : ∀ {x : ℕ}, Odd x → x.totient = 25387551686656 → 51878909956305 ≤ x) :
    ¬ (∀ n : ℕ, Odd n → Odd (aSeq n)) := by
  intro parity
  have hopen : Odd 51878909956305 := ⟨25939454978152, by decide⟩
  let ex : ∃ k : ℕ, k.totient = Nat.totient 51878909956305 := ⟨_,rfl⟩
  have hsmall : aSeq 51878909956305 ≤ 50973714157568 :=
    Nat.find_min' ex (even_totient.trans odd_totient.symm)
  have same : Nat.totient (aSeq 51878909956305) = Nat.totient 51878909956305 :=
    Nat.find_spec ex
  have hlarge := lower (parity _ hopen) (same.trans odd_totient)
  omega

end OMA.S_oeis_a015126

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a015126.main) :=
  OMA.S_oeis_a015126.not_all_odd OMA.S_oeis_a015126.odd_lower
