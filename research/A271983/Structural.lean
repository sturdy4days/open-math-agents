import OMAStatements.S_oeis_a271983

/-!
# Necessary conditions for an all-even two-element totient fiber

This partial result concerns the conjecture recorded in Geoffrey Critzer's OEIS A271983.
Jianing Song records the equivalent doubling formulation in A007366. The project
statement was contributed by @darealpandaboi. Formalization by @sturdy4days.

https://oeis.org/A271983
https://oeis.org/A007366
-/

namespace OMA.S_oeis_a271983

/-- When p² does not divide x, removing p changes the totient by either 1 or p−1. -/
private theorem strip_single (x p j : ℕ) (hp : p.Prime) (sq : ¬ p^2 ∣ x)
    (power : p-1 = 2^j) : ∃ y e : ℕ, y ∣ x ∧ p.Coprime y ∧
      x.totient = y.totient*2^e := by
  by_cases useP : p ∣ x
  · obtain ⟨y,rfl⟩ := useP
    have cop : p.Coprime y := hp.coprime_iff_not_dvd.mpr fun h =>
      sq (by simpa [pow_two] using Nat.mul_dvd_mul_left p h)
    refine ⟨y,j,dvd_mul_left _ _,cop,?_⟩
    rw [Nat.totient_mul cop,Nat.totient_prime hp,power,mul_comm]
  · exact ⟨x,0,dvd_refl _,hp.coprime_iff_not_dvd.mpr useP,by simp⟩

/-- Strip the entire power of 2 and the (at most single) factors 3 and 5. -/
theorem strip_235 {x : ℕ} (hx : 0<x) (no9 : ¬ 9 ∣ x) (no25 : ¬ 25 ∣ x) :
    ∃ c t : ℕ, 0<c ∧ c.Coprime 30 ∧ x.totient = c.totient*2^t := by
  let u := ordCompl[2] x
  let a := x.factorization 2
  have xu : 2^a*u = x := Nat.ordProj_mul_ordCompl_eq_self x 2
  have ud : u ∣ x := xu ▸ dvd_mul_left _ _
  have cop2 : Nat.Coprime 2 u := Nat.coprime_ordCompl Nat.prime_two hx.ne'
  have phi2 : (2^a).totient = 2^(a-1) := by
    cases a with
    | zero => simp
    | succ k => simp [Nat.totient_prime_pow_succ Nat.prime_two]
  have pt : x.totient = u.totient*2^(a-1) := by
    calc
      x.totient = (2^a*u).totient := congrArg Nat.totient xu.symm
      _ = u.totient*2^(a-1) := by rw [Nat.totient_mul (cop2.pow_left _),phi2,mul_comm]
  obtain ⟨v,e,vu,cop3,pv⟩ := strip_single u 3 1 (by decide)
    (fun h => no9 (h.trans ud)) (by decide)
  obtain ⟨c,f,cv,cop5,pc⟩ := strip_single v 5 2 (by decide)
    (fun h => no25 (h.trans (vu.trans ud))) (by decide)
  have cop2c : Nat.Coprime 2 c := cop2.of_dvd_right (cv.trans vu)
  have cop3c : Nat.Coprime 3 c := cop3.of_dvd_right cv
  refine ⟨c,f+e+(a-1),Nat.pos_of_dvd_of_pos (cv.trans (vu.trans ud)) hx,?_,?_⟩
  · exact (cop2c.symm.mul_right cop3c.symm).mul_right cop5.symm
  · rw [pt,pv,pc,pow_add,pow_add]; ac_rfl

end OMA.S_oeis_a271983

namespace OMA.S_oeis_a271983

private theorem scale_totient (a k : ℕ) (ha : 2 ∣ a) :
    (2^k*a).totient = 2^k*a.totient := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_assoc,Nat.totient_mul_of_prime_of_dvd Nat.prime_two
      (dvd_mul_of_dvd_right ha _),ih, mul_assoc]

/-- A totient of a number supported away from 2, 3, 5, multiplied by a power
of two, cannot have exactly two preimages that are both even. -/
theorem family_obstruction (c t n m : ℕ) (hc : 0 < c) (hcop : c.Coprime 30)
    (hn : Even n) (hm : Even m)
    (covers : ∀ k : ℕ, k.totient = c.totient * 2^t → k = n ∨ k = m) : False := by
  have oddc : Odd c :=
    Nat.coprime_two_right.mp (Nat.Coprime.of_dvd_right (by decide : 2 ∣ 30) hcop)
  have noOdd (z : ℕ) (hz : Odd z) (hit : z.totient = c.totient * 2^t) : False := by
    rcases covers z hit with h | h
    · obtain ⟨i, hi⟩ := hz; obtain ⟨j,hj⟩ := hn; omega
    · obtain ⟨i, hi⟩ := hz; obtain ⟨j,hj⟩ := hm; omega
  cases t with
  | zero => exact noOdd c oddc (by simp)
  | succ t =>
    cases t with
    | zero =>
      apply noOdd (c*3) (oddc.mul (by decide : Odd 3))
      rw [Nat.totient_mul (Nat.Coprime.of_dvd_right (by decide : 3 ∣ 30) hcop)]
      rfl
    | succ t =>
      have targetHit (v : ℕ) (dv : v ∣ 30^3) (evenv : 2 ∣ v) (hv : v.totient=4) :
          ((2^t*c)*v).totient = c.totient * 2^(t+1+1) := by
        rw [mul_assoc,scale_totient _ _ (dvd_mul_of_dvd_right evenv _),
            Nat.totient_mul (Nat.Coprime.of_dvd_right dv (hcop.pow_right 3)),hv]
        ring
      have h8 := covers _ (targetHit 8 (by decide) (by decide) (by decide))
      have h10 := covers _ (targetHit 10 (by decide) (by decide) (by decide))
      have h12 := covers _ (targetHit 12 (by decide) (by decide) (by decide))
      have pos : 0 < 2^t*c := Nat.mul_pos (pow_pos (by decide) _) hc
      omega

end OMA.S_oeis_a271983

namespace OMA.S_oeis_a271983

/-- In an all-even fiber with exactly two members, every member contains a squared
factor of 3 or 5. -/
theorem square_obstruction {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m)
    {x : ℕ} (hit : x.totient = n.totient) : 9 ∣ x ∨ 25 ∣ x := by
  have nonzero : x ≠ 0 := by
    rintro rfl
    have a := Nat.totient_eq_zero.mp hit.symm
    have b := Nat.totient_eq_zero.mp (same.symm.trans hit.symm)
    exact distinct (a.trans b.symm)
  by_contra! bad
  obtain ⟨c,t,hc,cop,rep⟩ := strip_235 (Nat.pos_of_ne_zero nonzero) bad.1 bad.2
  exact family_obstruction c t n m hc cop hn hm fun k hk =>
    covers k ((hk.trans rep.symm).trans hit)

/-- The common totient is divisible by 3 or 5. -/
theorem common_totient_obstruction {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m) :
    3 ∣ n.totient ∨ 5 ∣ n.totient := by
  rcases square_obstruction distinct same hn hm covers rfl with h | h
  · left
    exact (show 3 ∣ Nat.totient 9 by decide).trans (Nat.totient_dvd_of_dvd h)
  · right
    exact (show 5 ∣ Nat.totient 25 by decide).trans (Nat.totient_dvd_of_dvd h)

/-- The two-preimage parity conclusion of A271983 on all totients coprime to 15. -/
theorem mixed_when_coprime_fifteen {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m) (cop : n.totient.Coprime 15) :
    (Odd n ∧ Even m) ∨ (Even n ∧ Odd m) := by
  rcases Nat.even_or_odd n with hn | hn
  · rcases Nat.even_or_odd m with hm | hm
    · rcases common_totient_obstruction distinct same hn hm covers with h | h
      · exact False.elim ((Nat.prime_three.coprime_iff_not_dvd.mp
          (cop.symm.of_dvd_left (by decide : 3 ∣ 15))) h)
      · exact False.elim (((by decide : Nat.Prime 5).coprime_iff_not_dvd.mp
          (cop.symm.of_dvd_left (by decide : 5 ∣ 15))) h)
    · exact Or.inr ⟨hn,hm⟩
  · have mate := covers (2*n) (Nat.totient_two_mul_of_odd hn)
    rcases mate with h | h
    · obtain ⟨j,hj⟩ := hn
      omega
    · exact Or.inl ⟨hn,h ▸ ⟨n,by omega⟩⟩

end OMA.S_oeis_a271983

namespace OMA.S_oeis_a271983

/-- Dividing an even number with exactly one factor 2 yields an odd preimage of
the same totient. Thus every all-even fiber is supported on multiples of four. -/
theorem four_dvd_all_even {n m : ℕ} (hn : Even n) (hm : Even m)
    (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m)
    {x : ℕ} (hit : x.totient = n.totient) : 4 ∣ x := by
  have evenx : Even x := (covers x hit).elim (fun e => e ▸ hn) (fun e => e ▸ hm)
  obtain ⟨y,hy⟩ := evenx
  have eq : x = 2*y := by omega
  rcases Nat.even_or_odd y with eveny | oddy
  · obtain ⟨k,hk⟩ := eveny
    exact ⟨k,by omega⟩
  · have hyphi : y.totient = n.totient := (Nat.totient_two_mul_of_odd oddy).symm.trans
      (eq ▸ hit)
    rcases covers y hyphi with h | h
    · obtain ⟨s,hs⟩ := hn; obtain ⟨t,ht⟩ := oddy; omega
    · obtain ⟨s,hs⟩ := hm; obtain ⟨t,ht⟩ := oddy; omega

theorem multiple_of_36_or_100 {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m)
    {x : ℕ} (hit : x.totient = n.totient) : 36 ∣ x ∨ 100 ∣ x := by
  have four := four_dvd_all_even hn hm covers hit
  rcases square_obstruction distinct same hn hm covers hit with h | h
  · exact Or.inl ((by decide : Nat.Coprime 4 9).mul_dvd_of_dvd_of_dvd four h)
  · exact Or.inr ((by decide : Nat.Coprime 4 25).mul_dvd_of_dvd_of_dvd four h)

/-- The common totient in any exceptional pair must be a multiple of 12 or 40. -/
theorem common_multiple_12_or_40 {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m) :
    12 ∣ n.totient ∨ 40 ∣ n.totient := by
  rcases multiple_of_36_or_100 distinct same hn hm covers rfl with h | h
  · exact Or.inl ((show 12 ∣ Nat.totient 36 by decide).trans (Nat.totient_dvd_of_dvd h))
  · exact Or.inr ((show 40 ∣ Nat.totient 100 by decide).trans (Nat.totient_dvd_of_dvd h))

end OMA.S_oeis_a271983

namespace OMA.S_oeis_a271983

/-- Outside the multiples of 12 and 40, every two-element totient fiber consists of
an odd integer and its double. -/
theorem doubling_outside_12_and_40 {n m : ℕ}
    (distinct : n ≠ m) (same : n.totient = m.totient)
    (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m)
    (no12 : ¬ 12 ∣ n.totient) (no40 : ¬ 40 ∣ n.totient) :
    (Odd n ∧ m=2*n) ∨ (Odd m ∧ n=2*m) := by
  have odd_side : Odd n ∨ Odd m := by
    rcases Nat.even_or_odd n with en | on
    · rcases Nat.even_or_odd m with em | om
      · exact False.elim ((common_multiple_12_or_40 distinct same en em covers).elim no12 no40)
      · exact Or.inr om
    · exact Or.inl on
  rcases odd_side with hn | hm
  · rcases covers (2*n) (Nat.totient_two_mul_of_odd hn) with h | h
    · obtain ⟨i,hi⟩ := hn; omega
    · exact Or.inl ⟨hn,h.symm⟩
  · rcases covers (2*m) ((Nat.totient_two_mul_of_odd hm).trans same.symm) with h | h
    · exact Or.inr ⟨hm,h.symm⟩
    · obtain ⟨i,hi⟩ := hm; omega

end OMA.S_oeis_a271983

namespace OMA.S_oeis_a271983

/-- If 5 is absent from the totient, swapping a single 3² for 7 excludes valuation
one at 3. Both factors have totient 6. -/
private theorem replace_nine {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m)
    (no5 : ¬ 5 ∣ n.totient) : 9 ∣ n.totient := by
  have force {x : ℕ} (hit : x.totient = n.totient) : 9 ∣ x := by
    rcases square_obstruction distinct same hn hm covers hit with h | h
    · exact h
    · exact False.elim (no5 (hit ▸ (show 5 ∣ Nat.totient 25 by decide).trans (Nat.totient_dvd_of_dvd h)))
  by_contra no9
  obtain ⟨y,hy⟩ := force (x:=n) rfl
  have exclude (p : ℕ) (hp : 9 ∣ (9*p).totient) : ¬p ∣ y := by
    intro h
    have dvd : 9*p ∣ n := hy ▸ Nat.mul_dvd_mul_left 9 h
    exact no9 (hp.trans (Nat.totient_dvd_of_dvd dvd))
  have c3 : Nat.Coprime 3 y := Nat.prime_three.coprime_iff_not_dvd.mpr (exclude 3 (by decide))
  have c7 : Nat.Coprime 7 y := (by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr
    (exclude 7 (by decide))
  have hit : (7*y).totient = n.totient := by
    rw [hy,Nat.totient_mul c7,Nat.totient_mul (show Nat.Coprime 9 y from c3.pow_left 2)]
    rfl
  have h3 : 3 ∣ 7*y := (show 3 ∣ 9 by decide).trans (force hit)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp c3) ((Nat.prime_three.dvd_mul.mp h3).resolve_left (by decide))

/-- When 3 is absent from the totient, swap a factor 5² for 2·11. The even
cofactor makes the extra factor 2 contribute a factor 2 to the totient. -/
private theorem replace_twentyfive {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m)
    (no3 : ¬ 3 ∣ n.totient) : 25 ∣ n.totient := by
  have force {x : ℕ} (hit : x.totient = n.totient) : 25 ∣ x := by
    rcases square_obstruction distinct same hn hm covers hit with h | h
    · exact False.elim (no3 (hit ▸ (show 3 ∣ Nat.totient 9 by decide).trans (Nat.totient_dvd_of_dvd h)))
    · exact h
  by_contra no25
  obtain ⟨y,hy⟩ := force (x:=n) rfl
  have exclude (p : ℕ) (hp : 25 ∣ (25*p).totient) : ¬p ∣ y := by
    intro h
    have dvd : 25*p ∣ n := hy ▸ Nat.mul_dvd_mul_left 25 h
    exact no25 (hp.trans (Nat.totient_dvd_of_dvd dvd))
  have c5 : Nat.Coprime 5 y := (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr
    (exclude 5 (by decide))
  have c11 : Nat.Coprime 11 y := (by decide : Nat.Prime 11).coprime_iff_not_dvd.mpr
    (exclude 11 (by rw [Nat.totient_mul (by decide : Nat.Coprime 25 11)]; decide))
  have ey : Even y := by
    obtain ⟨k,hk⟩ := hn
    exact ⟨y/2,by omega⟩
  have hite : Even (11*y) := ey.mul_left _
  have hit : (2*(11*y)).totient = n.totient := by
    rw [Nat.totient_two_mul_of_even hite,hy,Nat.totient_mul c11,
      Nat.totient_mul (show Nat.Coprime 25 y from c5.pow_left 2)]
    change 2*(10*y.totient)=20*y.totient
    omega
  have h5 : 5 ∣ 22*y := (show 5 ∣ 25 by decide).trans (by simpa [← Nat.mul_assoc] using force hit)
  exact ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mp c5)
    (((by decide : Nat.Prime 5).dvd_mul.mp h5).resolve_left (by decide))

/-- A counterexample at a totient N requires that N be divisible by 36, 60 or 200. -/
theorem common_multiple_36_60_200 {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m) :
    36 ∣ n.totient ∨ 60 ∣ n.totient ∨ 200 ∣ n.totient := by
  have first := common_multiple_12_or_40 distinct same hn hm covers
  have second := replace_nine distinct same hn hm covers
  have third := replace_twentyfive distinct same hn hm covers
  omega

/-- Outside the multiples of 36, 60, and 200, every two-element totient fiber consists of
an odd integer and its double. -/
theorem doubling_outside_36_60_200 {n m : ℕ}
    (distinct : n ≠ m) (same : n.totient = m.totient)
    (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m)
    (no36 : ¬ 36 ∣ n.totient) (no60 : ¬ 60 ∣ n.totient) (no200 : ¬ 200 ∣ n.totient) :
    (Odd n ∧ m=2*n) ∨ (Odd m ∧ n=2*m) := by
  have odd_side : Odd n ∨ Odd m := by
    rcases Nat.even_or_odd n with en | on
    · rcases Nat.even_or_odd m with em | om
      · exact False.elim ((common_multiple_36_60_200 distinct same en em covers).elim no36 (fun h => h.elim no60 no200))
      · exact Or.inr om
    · exact Or.inl on
  rcases odd_side with hn | hm
  · rcases covers (2*n) (Nat.totient_two_mul_of_odd hn) with h | h
    · obtain ⟨i,hi⟩ := hn; omega
    · exact Or.inl ⟨hn,h.symm⟩
  · rcases covers (2*m) ((Nat.totient_two_mul_of_odd hm).trans same.symm) with h | h
    · exact Or.inr ⟨hm,h.symm⟩
    · obtain ⟨i,hi⟩ := hm; omega

end OMA.S_oeis_a271983

namespace OMA.S_oeis_a271983

private theorem phi_threes (a : ℕ) : (36*3^a).totient = 12*3^a := by
  induction a with
  | zero => decide
  | succ a ih =>
    have shift : 36*3^(a+1) = 3*(36*3^a) := by rw [pow_succ]; ac_rfl
    rw [shift,Nat.totient_mul_of_prime_of_dvd Nat.prime_three
      (dvd_mul_of_dvd_left (by decide : 3 ∣ 36) _),ih,pow_succ]
    ac_rfl

/-- A multiple of 36 whose totient is not divisible by 8 has the form 36 · 3ᵃ.
In particular its totient determines it uniquely. -/
private theorem unique_low_two {x : ℕ} (mul36 : 36 ∣ x) (no8 : ¬ 8 ∣ x.totient) :
    x = 3*x.totient := by
  obtain ⟨y,rfl⟩ := mul36
  have yn : y ≠ 0 := by rintro rfl; simp at no8
  obtain ⟨a,u,no3,split⟩ := Nat.exists_eq_pow_mul_and_not_dvd yn 3 (by decide)
  have uy : u ∣ y := split ▸ dvd_mul_left _ _
  have no2 : ¬ 2 ∣ u := by
    intro two
    have div : 72 ∣ 36*y := Nat.mul_dvd_mul_left 36 (two.trans uy)
    exact no8 ((show 8 ∣ Nat.totient 72 by decide).trans (Nat.totient_dvd_of_dvd div))
  have u1 : u=1 := by
    by_contra other
    have u_pos : 0 < u := Nat.pos_of_dvd_of_pos uy (Nat.pos_of_ne_zero yn)
    have big : 2<u := by omega
    have c2 := Nat.prime_two.coprime_iff_not_dvd.mpr no2
    have c3 := Nat.prime_three.coprime_iff_not_dvd.mpr no3
    have cop : Nat.Coprime 36 u := (c2.pow_left 2).mul_left (c3.pow_left 2)
    have div : (36*u).totient ∣ (36*y).totient := Nat.totient_dvd_of_dvd
      (Nat.mul_dvd_mul_left 36 uy)
    apply no8
    apply dvd_trans _ div
    rw [Nat.totient_mul cop]
    obtain ⟨k,h⟩ := Nat.totient_even big
    change 8 ∣ 12*u.totient
    exact ⟨3*k,by omega⟩
  rw [u1,mul_one] at split
  rw [split,phi_threes]
  omega

/-- All-even two-element fibers have at least three factors of 2 in the common totient. -/
theorem eight_dvd {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m) :
    8 ∣ n.totient := by
  by_contra no8
  have determine {x : ℕ} (hit : x.totient = n.totient) : x = 3*n.totient := by
    have fail : ¬8 ∣ x.totient := hit ▸ no8
    rcases multiple_of_36_or_100 distinct same hn hm covers hit with h | h
    · rw [← hit]
      exact unique_low_two h fail
    · exact False.elim (fail ((show 8 ∣ Nat.totient 100 by decide).trans (Nat.totient_dvd_of_dvd h)))
  exact distinct ((determine rfl).trans (determine same.symm).symm)

theorem necessary_72_120_200 {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m) :
    72 ∣ n.totient ∨ 120 ∣ n.totient ∨ 200 ∣ n.totient := by
  have := eight_dvd distinct same hn hm covers
  have := common_multiple_36_60_200 distinct same hn hm covers
  omega

/-- Outside the multiples of 72, 120 and 200, every two-element totient fiber consists of
an odd integer and its double. -/
theorem doubling_outside_72_120_200 {n m : ℕ}
    (distinct : n ≠ m) (same : n.totient = m.totient)
    (covers : ∀ k : ℕ, k.totient = n.totient → k=n ∨ k=m)
    (no72 : ¬ 72 ∣ n.totient) (no120 : ¬ 120 ∣ n.totient) (no200 : ¬ 200 ∣ n.totient) :
    (Odd n ∧ m=2*n) ∨ (Odd m ∧ n=2*m) := by
  have odd_side : Odd n ∨ Odd m := by
    rcases Nat.even_or_odd n with en | on
    · rcases Nat.even_or_odd m with em | om
      · exact False.elim ((necessary_72_120_200 distinct same en em covers).elim no72 (fun h => h.elim no120 no200))
      · exact Or.inr om
    · exact Or.inl on
  rcases odd_side with hn | hm
  · rcases covers (2*n) (Nat.totient_two_mul_of_odd hn) with h | h
    · obtain ⟨i,hi⟩ := hn; omega
    · exact Or.inl ⟨hn,h.symm⟩
  · rcases covers (2*m) ((Nat.totient_two_mul_of_odd hm).trans same.symm) with h | h
    · exact Or.inr ⟨hm,h.symm⟩
    · obtain ⟨i,hi⟩ := hm; omega

end OMA.S_oeis_a271983
