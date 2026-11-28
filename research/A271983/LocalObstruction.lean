import OMAStatements.S_oeis_a271983

/-!
# A finite obstruction for two-element totient fibers

This research supplement concerns the conjecture in Geoffrey Critzer's A271983
and Jianing Song's doubling formulation in A007366. It builds on the previous
36-or-100 divisibility lemma. Fifty-seven checked local substitutions force a
strict increase among 352 candidate divisors unless a terminal divisor is reached.
The numerical certificates are verified directly by the Lean kernel.
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

abbrev exceptional (x : ℕ) : Prop := ∃ n m : ℕ, Even n ∧ Even m ∧
  ∀ k : ℕ, k.totient = x.totient → k=n ∨ k=m

def fastPhi (a : ℕ) : ℕ :=
  (a / ∏ p ∈ a.primeFactors, p) * ∏ p ∈ a.primeFactors, (p-1)

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

structure Move where
  a : ℕ
  b : ℕ
  e : ℕ
  guards : List ℕ
deriving DecidableEq, Repr

abbrev Move.valid (r : Move) : Prop :=
  0<r.a ∧ 0<r.b ∧ fastPhi r.a = fastPhi r.b ∧ guarded r.a r.b r.guards ∧
  (if r.e=0 then Odd r.b ∧ 2∈r.guards
  else fastPhi r.a = fastPhi r.e ∧ guarded r.a r.e r.guards ∧ r.a≠r.b ∧ r.b≠r.e ∧ r.a≠r.e)

theorem Move.force (r : Move) (ok : r.valid) (c : ℕ) (hc : 0<c) (E : exceptional (r.a*c)) :
    ∃ p ∈ r.guards, p ∣ c := by
  by_contra! avoid
  obtain ⟨a0,b0,eqb,gb,extra⟩ := ok
  obtain ⟨n,m,ne,me,cover⟩ := E
  have Hb := (scaled_guard _ _ c _ a0 b0 eqb gb avoid).symm
  rcases he : r.e with _ | e
  · simp only [he,if_true] at extra
    have oddc : Odd c := Nat.odd_iff.mpr (by have := avoid _ extra.2; omega)
    have oddval := extra.1.mul oddc
    rcases cover _ Hb with hn|hm
    · exact (Nat.not_odd_iff_even.mpr ne) (hn ▸ oddval)
    · exact (Nat.not_odd_iff_even.mpr me) (hm ▸ oddval)
  · have nz : r.e ≠ 0 := by omega
    simp only [if_neg nz] at extra
    have He := (scaled_guard _ _ c _ a0 (Nat.pos_of_ne_zero nz) extra.1 extra.2.1 avoid).symm
    have distinctAB : r.a*c ≠ r.b*c := fun h => extra.2.2.1 (Nat.eq_of_mul_eq_mul_right hc h)
    have distinctBE : r.b*c ≠ r.e*c := fun h => extra.2.2.2.1 (Nat.eq_of_mul_eq_mul_right hc h)
    have distinctAE : r.a*c ≠ r.e*c := fun h => extra.2.2.2.2 (Nat.eq_of_mul_eq_mul_right hc h)
    rcases cover _ rfl with h₁|h₁ <;> rcases cover _ Hb with h₂|h₂ <;>
      rcases cover _ He with h₃|h₃ <;> grind

end TotientLocal

namespace TotientLocal

/-- The list stores a path to a larger divisor or to one of the terminal divisors. -/
abbrev nodeOK (goals parents : List ℕ) (rules : List Move) (v : ℕ × Move) : Prop :=
  0<v.1 ∧ v.2 ∈ rules ∧ v.2.a ∣ v.1 ∧
  ∀ p ∈ v.2.guards, 1<p ∧ p.Coprime (v.1/v.2.a) ∧
    (v.1*p ∈ parents ∨ ∃ g ∈ goals, g ∣ v.1*p)

theorem climb (goals : List ℕ) (rules : List Move) (nodes : List (ℕ × Move))
    (sound : ∀ r ∈ rules, r.valid)
    (links : ∀ v ∈ nodes, nodeOK goals (nodes.map Prod.fst) rules v)
    {x : ℕ} (xpos : 0<x) (E : exceptional x) (entry : ∃ a ∈ nodes.map Prod.fst, a ∣ x) :
    ∃ g ∈ goals, g ∣ x := by
  let D := (nodes.map Prod.fst).toFinset.filter (· ∣ x)
  have nonempty : D.Nonempty := by
    obtain ⟨a,ha,d⟩ := entry
    exact ⟨a,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ha,d⟩⟩
  let a := D.max' nonempty
  have hm := Finset.mem_filter.mp (D.max'_mem nonempty)
  obtain ⟨v, hnode, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm.1)
  obtain ⟨pa,hr,divides,branches⟩ := links v hnode
  have va : v.1 ∣ x := he.symm ▸ hm.2
  obtain ⟨c,hc⟩ := va
  have cp : 0<c := Nat.pos_of_dvd_of_pos (hc ▸ dvd_mul_left _ _) xpos
  let q := v.1 / v.2.a
  have factor : v.2.a*q = v.1 := Nat.mul_div_cancel' divides
  have qp : 0<q := by
    have := Nat.pos_of_dvd_of_pos (factor ▸ dvd_mul_left _ _) pa
    exact this
  have xe : x=v.2.a*(q*c) := by rw [← mul_assoc,factor,hc]
  obtain ⟨p,hp,pc⟩ := v.2.force (sound _ hr) (q*c) (Nat.mul_pos qp cp) (xe ▸ E)
  obtain ⟨big,cop,next⟩ := branches p hp
  have pc' : p∣c := cop.dvd_of_dvd_mul_left pc
  have nx : v.1*p ∣ x := hc ▸ Nat.mul_dvd_mul_left v.1 pc'
  rcases next with hd | ⟨g,hg,hnext⟩
  · have mem : v.1*p ∈ D := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hd,nx⟩
    have bound : v.1*p ≤ a := D.le_max' _ mem
    have lt' : v.1 < v.1*p := by simpa using Nat.mul_lt_mul_of_pos_left big pa
    exact False.elim (Nat.not_lt_of_ge (show v.1*p ≤ v.1 from he.symm ▸ bound) lt')
  · exact ⟨g,hg,hnext.trans nx⟩

end TotientLocal

namespace Local19

open TotientLocal
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

private def r0 : Move := ⟨4, 3, 0, [2, 3]⟩
private def r1 : Move := ⟨8, 5, 0, [2, 5]⟩
private def r2 : Move := ⟨36, 13, 0, [2, 3, 13]⟩
private def r3 : Move := ⟨36, 21, 0, [2, 7]⟩
private def r4 : Move := ⟨36, 28, 42, [3, 7]⟩
private def r5 : Move := ⟨72, 39, 0, [2, 13]⟩
private def r6 : Move := ⟨72, 52, 78, [3, 13]⟩
private def r7 : Move := ⟨72, 90, 84, [5, 7]⟩
private def r8 : Move := ⟨72, 84, 78, [7, 13]⟩
private def r9 : Move := ⟨78, 72, 90, [5, 13]⟩
private def r10 : Move := ⟨78, 72, 84, [7, 13]⟩
private def r11 : Move := ⟨84, 72, 90, [5, 7]⟩
private def r12 : Move := ⟨84, 72, 78, [7, 13]⟩
private def r13 : Move := ⟨90, 72, 84, [5, 7]⟩
private def r14 : Move := ⟨100, 55, 0, [2, 11]⟩
private def r15 : Move := ⟨100, 150, 110, [3, 11]⟩
private def r16 : Move := ⟨100, 88, 110, [5, 11]⟩
private def r17 : Move := ⟨108, 57, 0, [2, 19]⟩
private def r18 : Move := ⟨108, 76, 114, [3, 19]⟩
private def r19 : Move := ⟨108, 126, 114, [7, 19]⟩
private def r20 : Move := ⟨110, 100, 150, [3, 11]⟩
private def r21 : Move := ⟨114, 108, 126, [7, 19]⟩
private def r22 : Move := ⟨126, 108, 114, [7, 19]⟩
private def r23 : Move := ⟨150, 100, 110, [3, 11]⟩
private def r24 : Move := ⟨210, 144, 168, [5, 7]⟩
private def r25 : Move := ⟨216, 234, 228, [13, 19]⟩
private def r26 : Move := ⟨228, 216, 234, [13, 19]⟩
private def r27 : Move := ⟨234, 216, 228, [13, 19]⟩
private def r28 : Move := ⟨306, 288, 336, [7, 17]⟩
private def r29 : Move := ⟨306, 288, 312, [13, 17]⟩
private def r30 : Move := ⟨312, 288, 306, [13, 17]⟩
private def r31 : Move := ⟨330, 200, 220, [3, 11]⟩
private def r32 : Move := ⟨336, 288, 306, [7, 17]⟩
private def r33 : Move := ⟨390, 288, 312, [5, 13]⟩
private def r34 : Move := ⟨546, 432, 468, [7, 13]⟩
private def r35 : Move := ⟨714, 576, 612, [7, 17]⟩
private def r36 : Move := ⟨798, 648, 684, [7, 19]⟩
private def r37 : Move := ⟨850, 800, 880, [11, 17]⟩
private def r38 : Move := ⟨880, 800, 850, [11, 17]⟩
private def r39 : Move := ⟨900, 1050, 990, [7, 11]⟩
private def r40 : Move := ⟨912, 864, 918, [17, 19]⟩
private def r41 : Move := ⟨918, 864, 912, [17, 19]⟩
private def r42 : Move := ⟨990, 900, 1050, [7, 11]⟩
private def r43 : Move := ⟨1050, 900, 990, [7, 11]⟩
private def r44 : Move := ⟨1326, 1152, 1224, [13, 17]⟩
private def r45 : Move := ⟨1482, 1296, 1368, [13, 19]⟩
private def r46 : Move := ⟨1800, 1980, 1950, [11, 13]⟩
private def r47 : Move := ⟨1870, 1600, 1700, [11, 17]⟩
private def r48 : Move := ⟨1938, 1728, 1824, [17, 19]⟩
private def r49 : Move := ⟨1950, 1800, 1980, [11, 13]⟩
private def r50 : Move := ⟨1980, 1800, 1950, [11, 13]⟩
private def r51 : Move := ⟨2310, 1800, 1980, [7, 11]⟩
private def r52 : Move := ⟨2700, 2970, 2850, [11, 19]⟩
private def r53 : Move := ⟨2850, 2700, 2970, [11, 19]⟩
private def r54 : Move := ⟨2970, 2700, 2850, [11, 19]⟩
private def r55 : Move := ⟨4290, 3600, 3900, [11, 13]⟩
private def r56 : Move := ⟨6270, 5400, 5700, [11, 19]⟩
private def rules := [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56]
private def goals : List ℕ := [24200, 36300, 298116, 1910412]

private def ns0 : List (ℕ × Move) := [
  (36, r3), (72, r5), (100, r14), (144, r6),
  (200, r16), (252, r12), (432, r18), (936, r1),
  (1000, r15), (1100, r0), (1296, r25), (1764, r2),
  (1872, r30), (2200, r20), (3000, r23), (3276, r34),
  (3300, r31), (3528, r5), (4680, r33), (5292, r18),
  (6600, r31), (7056, r6), (8208, r40), (9000, r5),
  (9900, r50), (11000, r20), (15876, r17), (16848, r30),
  (18000, r6), (19800, r50), (21168, r18), (22932, r27)]
private def ns1 : List (ℕ × Move) := [
  (23400, r30), (24336, r4), (24624, r40), (31752, r5),
  (31824, r44), (33000, r31), (42588, r22), (45864, r30),
  (54000, r18), (60840, r13), (63504, r25), (73008, r18),
  (91728, r30), (99000, r50), (100548, r26), (117000, r30),
  (128700, r55), (139536, r48), (155952, r8), (162000, r25),
  (170352, r32), (219024, r19), (234000, r30), (257400, r55),
  (286416, r44), (301644, r26), (304200, r16), (397800, r44),
  (402192, r40), (412776, r30), (413712, r28), (418608, r48)]
private def ns2 : List (ℕ × Move) := [
  (425880, r24), (435708, r45), (467856, r8), (541008, r27),
  (779688, r44), (809172, r36), (825552, r30), (1026000, r40),
  (1091664, r12), (1206576, r40), (1287000, r55), (1307124, r45),
  (1387152, r40), (1521000, r4), (1533168, r32), (1559376, r44),
  (1673100, r42), (1989000, r44), (2027376, r30), (2106000, r30),
  (2129400, r43), (2372112, r26), (2651184, r29), (2895984, r35),
  (3042000, r4), (3078000, r40), (3274992, r12), (3346200, r42),
  (3723408, r41), (3921372, r45), (3978000, r44), (4161456, r40)]
private def ns3 : List (ℕ × Move) := [
  (4563000, r18), (4869072, r27), (5171400, r37), (6082128, r30),
  (6762600, r27), (6837264, r48), (7017192, r44), (7033104, r4),
  (7116336, r26), (7953552, r29), (8278452, r9), (9126000, r18),
  (10279152, r45), (10647000, r43), (11711700, r51), (13254696, r27),
  (13689000, r52), (14034384, r44), (14191632, r34), (15374268, r11),
  (16731000, r42), (17442000, r48), (19494000, r46), (20511792, r48),
  (21099312, r18), (21294000, r43), (23423400, r51), (23581584, r48),
  (25857000, r37), (26063856, r35), (26355888, r7), (26509392, r27)]
private def ns4 : List (ℕ × Move) := [
  (27378000, r52), (30837456, r45), (33813000, r27), (34465392, r44),
  (35802000, r44), (41392260, r33), (42574896, r34), (45070128, r8),
  (49231728, r22), (51714000, r37), (52326000, r48), (56885400, r47),
  (58482000, r46), (63297936, r19), (67626000, r27), (70744752, r48),
  (76871340, r24), (79067664, r7), (86697000, r53), (87913800, r16),
  (92512368, r45), (103396176, r44), (116233488, r26), (117117000, r51),
  (119292264, r27), (128489400, r45), (131779440, r13), (133628976, r21),
  (135210384, r8), (150579000, r54), (173394000, r40), (184491216, r32)]
private def ns5 : List (ℕ × Move) := [
  (195303888, r10), (206961300, r49), (214434000, r50), (234234000, r51),
  (238584528, r27), (251839224, r45), (253422000, r30), (260091000, r53),
  (284427000, r47), (296514000, r26), (301158000, r38), (315490896, r12),
  (331398000, r29), (348700464, r26), (384356700, r43), (395338320, r13),
  (400886928, r21), (439569000, r4), (443085552, r22), (448050096, r28),
  (465426000, r41), (503678448, r45), (520182000, r40), (553473648, r32),
  (568854000, r47), (585911664, r10), (608634000, r27), (642447000, r45),
  (643302000, r50), (658897200, r16), (760266000, r30), (879138000, r4)]
private def ns6 : List (ℕ × Move) := [
  (889542000, r26), (922456080, r24), (935402832, r36), (946472688, r12),
  (953667000, r56), (967051800, r42), (994194000, r29), (1202660784, r21),
  (1284894000, r45), (1318707000, r18), (1344150288, r28), (1367127216, r34),
  (1511035344, r45), (1647243000, r39), (1670362200, r53), (1757734992, r10),
  (1976691600, r16), (2266553016, r45), (2276574300, r55), (2441298600, r49),
  (2538950544, r4), (2637414000, r18), (2767368240, r24), (2787642000, r55),
  (2806208496, r36), (2861001000, r56), (2947698000, r48), (3076983000, r43),
  (3136350672, r35), (3294486000, r39), (3854682000, r45), (3956121000, r52)]
private def ns7 : List (ℕ × Move) := [
  (4101381648, r34), (4227923700, r51), (4308174000, r44), (4533106032, r45),
  (4612280400, r43), (4784945256, r9), (4835259000, r42), (4941729000, r39),
  (5119686000, r47), (5633766000, r46), (6153966000, r43), (6769362600, r51),
  (7247869200, r38), (7616851632, r7), (7912242000, r52), (8351811000, r53),
  (8362926000, r55), (8418625488, r36), (8843094000, r48), (9409052016, r35),
  (9569890512, r9), (9670518000, r42), (9883458000, r39), (11530701000, r43),
  (11564046000, r45), (12206493000, r49), (12304144944, r34), (12924522000, r44),
  (13836841200, r43), (16703622000, r53), (16901298000, r46), (17772653808, r11)]
private def ns8 : List (ℕ × Move) := [
  (18119673000, r42), (18373984200, r56), (21743607600, r38), (22850554896, r7),
  (23061402000, r43), (23924726280, r33), (24412986000, r49), (25055433000, r53),
  (26854284600, r55), (31736881800, r16), (33846813000, r51), (34592103000, r43),
  (36239346000, r38), (38084258160, r13), (43517331000, r54), (47849452560, r33),
  (50110866000, r53), (50735084400, r51), (53317961424, r11), (54359019000, r42),
  (56006262000, r37), (61971426000, r50), (67693626000, r51), (69184206000, r43),
  (73238958000, r49), (75166299000, r53), (87034662000, r54), (88863269040, r24),
  (91869921000, r56), (108718038000, r38), (114252774480, r13), (119623631400, r49)]
private def ns9 : List (ℕ × Move) := [
  (123213776400, r47), (126837711000, r51), (134271423000, r55), (150332598000, r53),
  (152205253200, r51), (158684409000, r4), (159953884272, r11), (168018786000, r37),
  (183739842000, r56), (185914278000, r50), (190421290800, r16), (219716874000, r49),
  (239247262800, r49), (253675422000, r51), (266589807120, r24), (268542846000, r55),
  (275609763000, r56), (317368818000, r4), (349105699800, r42), (369641329200, r47),
  (380513133000, r51), (444316345200, r43), (476053227000, r39), (551219526000, r56),
  (571263872400, r16), (616068882000, r47), (761026266000, r51), (799769421360, r24),
  (805628538000, r55), (826829289000, r56), (952106454000, r39), (1110790863000, r43)]
private def ns10 : List (ℕ × Move) := [
  (1315859945400, r55), (1332949035600, r43), (1428159681000, r39), (1653658578000, r56),
  (1745528499000, r42), (1848206646000, r47), (2094634198800, r42), (2221581726000, r43),
  (2416885614000, r55), (2443739898600, r51), (2631719890800, r55), (2856319362000, r39),
  (3332372589000, r43), (3491056998000, r42), (3998847106800, r43), (4887479797200, r51),
  (5236585497000, r42), (6283902596400, r42), (6664745178000, r43), (9997117767000, r43),
  (10473170994000, r42), (12218699493000, r51), (14662439391600, r51), (15709756491000, r42),
  (19994235534000, r43), (24437398986000, r51), (31419512982000, r42), (36656098479000, r51),
  (43987318174800, r51), (73312196958000, r51), (109968295437000, r51), (219936590874000, r51)]
private def nodes := ns0 ++ ns1 ++ ns2 ++ ns3 ++ ns4 ++ ns5 ++ ns6 ++ ns7 ++ ns8 ++ ns9 ++ ns10

private theorem certified : ∀ r ∈ rules, r.valid := by decide +kernel
private theorem step0 : ∀ v ∈ ns0, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step1 : ∀ v ∈ ns1, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step2 : ∀ v ∈ ns2, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step3 : ∀ v ∈ ns3, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step4 : ∀ v ∈ ns4, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step5 : ∀ v ∈ ns5, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step6 : ∀ v ∈ ns6, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step7 : ∀ v ∈ ns7, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step8 : ∀ v ∈ ns8, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step9 : ∀ v ∈ ns9, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem step10 : ∀ v ∈ ns10, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel
private theorem steps : ∀ v ∈ nodes, nodeOK goals (nodes.map Prod.fst) rules v := by
  intro v hv
  simp only [nodes,List.mem_append,or_assoc] at hv
  rcases hv with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10
  · exact step0 v h0
  · exact step1 v h1
  · exact step2 v h2
  · exact step3 v h3
  · exact step4 v h4
  · exact step5 v h5
  · exact step6 v h6
  · exact step7 v h7
  · exact step8 v h8
  · exact step9 v h9
  · exact step10 v h10

theorem input_divisors {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ y : ℕ, y.totient=n.totient → y=n ∨ y=m)
    {x : ℕ} (hit : x.totient=n.totient) :
    24200 ∣ x ∨ 36300 ∣ x ∨ 298116 ∣ x ∨ 1910412 ∣ x := by
  by_cases zero : x=0
  · simp [zero]
  have E : exceptional x := ⟨n,m,hn,hm,fun y hy => covers y (hy.trans hit)⟩
  have first := OMA.S_oeis_a271983.multiple_of_36_or_100 distinct same hn hm covers hit
  have root : ∃ a ∈ nodes.map Prod.fst, a∣x := by
    rcases first with h|h
    · exact ⟨36,by decide +kernel,h⟩
    · exact ⟨100,by decide +kernel,h⟩
  obtain ⟨g,hg,divides⟩ := climb goals rules nodes certified steps (Nat.pos_of_ne_zero zero) E root
  simp only [goals,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl <;> tauto

end Local19

namespace TotientLocal

/-- Each exceptional preimage is at least 24,200. -/
theorem input_lower_bound {n m : ℕ} (distinct : n ≠ m) (same : n.totient=m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ y : ℕ, y.totient=n.totient → y=n ∨ y=m)
    {x : ℕ} (hit : x.totient=n.totient) : 24200 ≤ x := by
  have hx : 0<x := by
    by_contra! z
    have zero : x=0 := by omega
    rw [zero,Nat.totient_zero] at hit
    exact distinct ((Nat.totient_eq_zero.mp hit.symm).trans (Nat.totient_eq_zero.mp (same.symm.trans hit.symm)).symm)
  rcases Local19.input_divisors distinct same hn hm covers hit with d|d|d|d
  all_goals have := Nat.le_of_dvd hx d; omega

/-- Any totient with exactly two positive even preimages is divisible by one of these three numbers. -/
theorem target_divisors {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ y : ℕ, y.totient=n.totient → y=n ∨ y=m) :
    8800 ∣ n.totient ∨ 78624 ∣ n.totient ∨ 517104 ∣ n.totient := by
  have eq₁ : Nat.totient 24200=8800 := by rw [Nat.totient_eq_div_primeFactors_mul]; decide +kernel
  have eq₂ : Nat.totient 36300=8800 := by rw [Nat.totient_eq_div_primeFactors_mul]; decide +kernel
  have eq₃ : Nat.totient 298116=78624 := by rw [Nat.totient_eq_div_primeFactors_mul]; decide +kernel
  have eq₄ : Nat.totient 1910412=517104 := by rw [Nat.totient_eq_div_primeFactors_mul]; decide +kernel
  rcases Local19.input_divisors distinct same hn hm covers rfl with d|d|d|d
  · exact Or.inl (eq₁ ▸ Nat.totient_dvd_of_dvd d)
  · exact Or.inl (eq₂ ▸ Nat.totient_dvd_of_dvd d)
  · exact Or.inr (Or.inl (eq₃ ▸ Nat.totient_dvd_of_dvd d))
  · exact Or.inr (Or.inr (eq₄ ▸ Nat.totient_dvd_of_dvd d))

/-- Away from the three residual progressions the odd solution and its double exhaust the fiber. -/
theorem doubling_outside_three_progressions {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (covers : ∀ y : ℕ, y.totient = n.totient → y = n ∨ y = m)
    (h₁ : ¬8800 ∣ n.totient) (h₂ : ¬78624 ∣ n.totient) (h₃ : ¬517104 ∣ n.totient) :
    (Odd n ∧ m=2*n) ∨ (Odd m ∧ n=2*m) := by
  have odd_side : Odd n ∨ Odd m := by
    rcases Nat.even_or_odd n with en|on
    · rcases Nat.even_or_odd m with em|om
      · rcases target_divisors distinct same en em covers with d|d|d
        · exact False.elim (h₁ d)
        · exact False.elim (h₂ d)
        · exact False.elim (h₃ d)
      · exact Or.inr om
    · exact Or.inl on
  rcases odd_side with hn|hm
  · rcases covers (2*n) (Nat.totient_two_mul_of_odd hn) with h|h
    · obtain ⟨i,hi⟩ := hn; omega
    · exact Or.inl ⟨hn,h.symm⟩
  · rcases covers (2*m) ((Nat.totient_two_mul_of_odd hm).trans same.symm) with h|h
    · exact Or.inr ⟨hm,h.symm⟩
    · obtain ⟨i,hi⟩ := hm; omega

end TotientLocal

namespace TotientLocal

/-- Count the integer residues in the three necessary progressions in a common period. -/
theorem possible_residue_count :
    ((Finset.Ioc 0 3697293600).filter (fun z : ℕ => 8800 ∣ z ∨ 78624 ∣ z ∨ 517104 ∣ z)).card
      = 473864 := by
  let S (p : ℕ) := (Finset.Ioc 0 3697293600).filter (fun z : ℕ => p ∣ z)
  have card (p : ℕ) : (S p).card = 3697293600 / p := Nat.Ioc_filter_dvd_card_eq_div _ _
  have inter (p q : ℕ) : S p ∩ S q = S (p.lcm q) := by
    ext z
    simp only [S,Finset.mem_inter,Finset.mem_filter,Nat.lcm_dvd_iff]
    tauto
  let a := 8800
  let b := 78624
  let c := 517104
  have hab := Finset.card_union_add_card_inter (S a) (S b)
  have hc := Finset.card_union_add_card_inter (S a ∪ S b) (S c)
  have hacbc := Finset.card_union_add_card_inter (S a ∩ S c) (S b ∩ S c)
  rw [Finset.union_inter_distrib_right] at hc
  simp only [inter,card] at hab hc hacbc
  have v0 : 3697293600 / (a) = 420147 := by decide +kernel
  have v1 : 3697293600 / (b) = 47025 := by decide +kernel
  have v2 : 3697293600 / (c) = 7150 := by decide +kernel
  have v3 : 3697293600 / (a.lcm b) = 171 := by decide +kernel
  have v4 : 3697293600 / (a.lcm c) = 13 := by decide +kernel
  have v5 : 3697293600 / (b.lcm c) = 275 := by decide +kernel
  have v6 : 3697293600 / ((a.lcm c).lcm (b.lcm c)) = 1 := by decide +kernel
  simp only [v0,v1,v2,v3,v4,v5,v6] at hab hc hacbc
  have eq : (Finset.Ioc 0 3697293600).filter (fun z : ℕ => 8800 ∣ z ∨ 78624 ∣ z ∨ 517104 ∣ z)
      = S a ∪ S b ∪ S c := by
    ext z
    simp only [S,a,b,c,Finset.mem_union,Finset.mem_filter]
    tauto
  rw [eq]
  omega

end TotientLocal

#print axioms OMA.S_oeis_a271983.multiple_of_36_or_100
#print axioms TotientLocal.scale_same
#print axioms TotientLocal.scaled_guard
#print axioms TotientLocal.Move.force
#print axioms TotientLocal.climb
#print axioms Local19.input_divisors
#print axioms TotientLocal.input_lower_bound
#print axioms TotientLocal.target_divisors
#print axioms TotientLocal.doubling_outside_three_progressions
#print axioms TotientLocal.possible_residue_count
