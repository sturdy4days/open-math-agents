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

namespace Noe30
open Noe

def terminalDivisors : List ℕ := [1055200883739222832492361203044, 1058890560926616308414947525452, 1179830890079573981778405706284, 1271258272067794446879895942476, 1451661752699461555593837357204, 1479745867667685017644303693956, 1486036959566541944389105192236, 1598505421861519832645114414004, 1650872731811702470716731169636, 1889342105289635073113470697004, 1922638410317304721147460313708, 1973104206613466841967663490796, 1992036191855780700610888984524, 2397536916985213388625484364652, 2434845193492703339526347499372, 2666989767728135373865076800764, 2775921211786005666491448619188, 2882140600727074089008609425548, 2972858471024586846834841983036, 3073643254124258874823489055436, 3292784157696002503699735365516, 3385394425829429445374048416212, 3907819101854833914982880121804, 4161863133778889960152905260052, 4588525764015337336464772610292, 5080652577984022936854378986124, 5173104671887362843182240404476, 5178943816179401991312766711836, 5483382343365111288901330819356, 5681305451482974458894810831868, 6439493491455015092352789166356, 6926856828066585941462162460684, 7586943734533645155105787617612, 8187149122921751983491706353684, 10389326640269258017377098913492, 10550995838468381137947505830612, 11747326207225448718949157752644, 12171346851677101768462505484132, 12489275936483987719037307510708, 12882386707773209669617648593156, 13804496697586353038845320772044, 16963351423588625204955993504156, 21299863087120434536243841088716, 27354733712983837404880160852628, 30859086972081655414726578479556, 35776839942479358005048500095396, 44018758857051198356899390701444, 59683791282086166022231812576252, 248662521813890844964695854862756, 274638933979869109856856355799388, 343353574394923119770881373898348, 381779349957490866396142792587804, 813278374151685449448794697048348, 878929866760331662292506693018284, 1452848272951361699731423002421356, 2016525536071090924175700628435092, 2368958960286696857736916574917812, 3915827717666671233104590946622708, 4383867929356961221541191599783276, 6090845383587001201912188904850604, 19486647341687624162928551844198084]

private theorem cons {α : Type} {P : α → Prop} {x : α} {xs : List α} (h : P x) (t : ∀ y ∈ xs, P y) : ∀ y ∈ x::xs, P y := List.forall_mem_cons.mpr ⟨h,t⟩
private theorem nil {α : Type} {P : α → Prop} : ∀ y ∈ ([] : List α), P y := List.forall_mem_nil _

private theorem pr2 : Nat.Prime 2 := by norm_num1
private theorem pr3 : Nat.Prime 3 := by norm_num1
private theorem pr7 : Nat.Prime 7 := by norm_num1
private theorem pr13 : Nat.Prime 13 := by norm_num1
private theorem pr19 : Nat.Prime 19 := by norm_num1
private theorem pr29 : Nat.Prime 29 := by norm_num1
private theorem pr43 : Nat.Prime 43 := by norm_num1
private theorem pr59 : Nat.Prime 59 := by norm_num1
private theorem pr127 : Nat.Prime 127 := by norm_num1
private theorem pr197 : Nat.Prime 197 := by norm_num1
private theorem pr883 : Nat.Prime 883 := by norm_num1
private theorem pr1373 : Nat.Prime 1373 := by norm_num1
private theorem pr3613 : Nat.Prime 3613 := by norm_num1
private theorem pr5419 : Nat.Prime 5419 := by norm_num1
private theorem pr8429 : Nat.Prime 8429 := by norm_num1
private theorem pr10267 : Nat.Prime 10267 := by norm_num1
private theorem pr10837 : Nat.Prime 10837 := by norm_num1
private theorem pr14407 : Nat.Prime 14407 := by norm_num1
private theorem pr22189 : Nat.Prime 22189 := by norm_num1
private theorem pr28813 : Nat.Prime 28813 := by norm_num1
private theorem pr77659 : Nat.Prime 77659 := by norm_num1
private theorem move0 {c : ℕ} (hx : Exceptional (36*c)) : ∃ p ∈ ([3, 13] : List ℕ), p ∣ c :=
  checked_guard 36 26 [3, 13] [2, 2, 3, 3] [2, 13] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr2 (cons pr13 nil)))))) (by decide +kernel) hx

private theorem move1 {c : ℕ} (hx : Exceptional (108*c)) : ∃ p ∈ ([19] : List ℕ), p ∣ c :=
  checked_guard 108 114 [19] [2, 2, 3, 3, 3] [2, 3, 19] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr3 (cons pr2 (cons pr3 (cons pr19 nil)))))))) (by decide +kernel) hx

private theorem move2 {c : ℕ} (hx : Exceptional (114*c)) : ∃ p ∈ ([19] : List ℕ), p ∣ c :=
  checked_guard 114 108 [19] [2, 3, 19] [2, 2, 3, 3, 3] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr19 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr3 nil)))))))) (by decide +kernel) hx

private theorem move3 {c : ℕ} (hx : Exceptional (406*c)) : ∃ p ∈ ([29] : List ℕ), p ∣ c :=
  checked_guard 406 392 [29] [2, 7, 29] [2, 2, 2, 7, 7] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr7 (cons pr29 (cons pr2 (cons pr2 (cons pr2 (cons pr7 (cons pr7 nil)))))))) (by decide +kernel) hx

private theorem move4 {c : ℕ} (hx : Exceptional (441*c)) : ∃ p ∈ ([7, 127] : List ℕ), p ∣ c :=
  checked_guard 441 381 [7, 127] [3, 3, 7, 7] [3, 127] (by decide +kernel) (by decide +kernel)
    (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr3 (cons pr127 nil)))))) (by decide +kernel) hx

private theorem move5 {c : ℕ} (hx : Exceptional (588*c)) : ∃ p ∈ ([7, 29] : List ℕ), p ∣ c :=
  checked_guard 588 522 [7, 29] [2, 2, 3, 7, 7] [2, 3, 3, 29] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr7 (cons pr7 (cons pr2 (cons pr3 (cons pr3 (cons pr29 nil))))))))) (by decide +kernel) hx

private theorem move6 {c : ℕ} (hx : Exceptional (2758*c)) : ∃ p ∈ ([197] : List ℕ), p ∣ c :=
  checked_guard 2758 2744 [197] [2, 7, 197] [2, 2, 2, 7, 7, 7] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr7 (cons pr197 (cons pr2 (cons pr2 (cons pr2 (cons pr7 (cons pr7 (cons pr7 nil))))))))) (by decide +kernel) hx

private theorem move7 {c : ℕ} (hx : Exceptional (3087*c)) : ∃ p ∈ ([7, 883] : List ℕ), p ∣ c :=
  checked_guard 3087 2649 [7, 883] [3, 3, 7, 7, 7] [3, 883] (by decide +kernel) (by decide +kernel)
    (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr3 (cons pr883 nil))))))) (by decide +kernel) hx

private theorem move8 {c : ℕ} (hx : Exceptional (3364*c)) : ∃ p ∈ ([59] : List ℕ), p ∣ c :=
  checked_guard 3364 3422 [59] [2, 2, 29, 29] [2, 29, 59] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr29 (cons pr29 (cons pr2 (cons pr29 (cons pr59 nil))))))) (by decide +kernel) hx

private theorem move9 {c : ℕ} (hx : Exceptional (3422*c)) : ∃ p ∈ ([59] : List ℕ), p ∣ c :=
  checked_guard 3422 3364 [59] [2, 29, 59] [2, 2, 29, 29] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr29 (cons pr59 (cons pr2 (cons pr2 (cons pr29 (cons pr29 nil))))))) (by decide +kernel) hx

private theorem move10 {c : ℕ} (hx : Exceptional (4116*c)) : ∃ p ∈ ([7, 197] : List ℕ), p ∣ c :=
  checked_guard 4116 3546 [7, 197] [2, 2, 3, 7, 7, 7] [2, 3, 3, 197] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr2 (cons pr3 (cons pr3 (cons pr197 nil)))))))))) (by decide +kernel) hx

private theorem move11 {c : ℕ} (hx : Exceptional (5292*c)) : ∃ p ∈ ([127] : List ℕ), p ∣ c :=
  checked_guard 5292 5334 [127] [2, 2, 3, 3, 3, 7, 7] [2, 3, 7, 127] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr2 (cons pr3 (cons pr7 (cons pr127 nil))))))))))) (by decide +kernel) hx

private theorem move12 {c : ℕ} (hx : Exceptional (5334*c)) : ∃ p ∈ ([127] : List ℕ), p ∣ c :=
  checked_guard 5334 5292 [127] [2, 3, 7, 127] [2, 2, 3, 3, 3, 7, 7] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr7 (cons pr127 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr3 (cons pr7 (cons pr7 nil))))))))))) (by decide +kernel) hx

private theorem move13 {c : ℕ} (hx : Exceptional (16641*c)) : ∃ p ∈ ([43, 5419] : List ℕ), p ∣ c :=
  checked_guard 16641 16257 [43, 5419] [3, 3, 43, 43] [3, 5419] (by decide +kernel) (by decide +kernel)
    (cons pr3 (cons pr3 (cons pr43 (cons pr43 (cons pr3 (cons pr5419 nil)))))) (by decide +kernel) hx

private theorem move14 {c : ℕ} (hx : Exceptional (19222*c)) : ∃ p ∈ ([1373] : List ℕ), p ∣ c :=
  checked_guard 19222 19208 [1373] [2, 7, 1373] [2, 2, 2, 7, 7, 7, 7] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr7 (cons pr1373 (cons pr2 (cons pr2 (cons pr2 (cons pr7 (cons pr7 (cons pr7 (cons pr7 nil)))))))))) (by decide +kernel) hx

private theorem move15 {c : ℕ} (hx : Exceptional (28812*c)) : ∃ p ∈ ([7, 1373] : List ℕ), p ∣ c :=
  checked_guard 28812 24714 [7, 1373] [2, 2, 3, 7, 7, 7, 7] [2, 3, 3, 1373] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr2 (cons pr3 (cons pr3 (cons pr1373 nil))))))))))) (by decide +kernel) hx

private theorem move16 {c : ℕ} (hx : Exceptional (31329*c)) : ∃ p ∈ ([59, 10267] : List ℕ), p ∣ c :=
  checked_guard 31329 30801 [59, 10267] [3, 3, 59, 59] [3, 10267] (by decide +kernel) (by decide +kernel)
    (cons pr3 (cons pr3 (cons pr59 (cons pr59 (cons pr3 (cons pr10267 nil)))))) (by decide +kernel) hx

private theorem move17 {c : ℕ} (hx : Exceptional (37044*c)) : ∃ p ∈ ([883] : List ℕ), p ∣ c :=
  checked_guard 37044 37086 [883] [2, 2, 3, 3, 3, 7, 7, 7] [2, 3, 7, 883] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr2 (cons pr3 (cons pr7 (cons pr883 nil)))))))))))) (by decide +kernel) hx

private theorem move18 {c : ℕ} (hx : Exceptional (37086*c)) : ∃ p ∈ ([883] : List ℕ), p ∣ c :=
  checked_guard 37086 37044 [883] [2, 3, 7, 883] [2, 2, 3, 3, 3, 7, 7, 7] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr7 (cons pr883 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr7 nil)))))))))))) (by decide +kernel) hx

private theorem move19 {c : ℕ} (hx : Exceptional (65028*c)) : ∃ p ∈ ([3613, 5419] : List ℕ), p ∣ c :=
  checked_guard 65028 65034 [3613, 5419] [2, 2, 3, 5419] [2, 3, 3, 3613] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr5419 (cons pr2 (cons pr3 (cons pr3 (cons pr3613 nil)))))))) (by decide +kernel) hx

private theorem move20 {c : ℕ} (hx : Exceptional (66564*c)) : ∃ p ∈ ([43, 10837] : List ℕ), p ∣ c :=
  checked_guard 66564 65022 [43, 10837] [2, 2, 3, 3, 43, 43] [2, 3, 10837] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr43 (cons pr43 (cons pr2 (cons pr3 (cons pr10837 nil))))))))) (by decide +kernel) hx

private theorem move21 {c : ℕ} (hx : Exceptional (67228*c)) : ∃ p ∈ ([7, 28813] : List ℕ), p ∣ c :=
  checked_guard 67228 57626 [7, 28813] [2, 2, 7, 7, 7, 7, 7] [2, 28813] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr2 (cons pr28813 nil))))))))) (by decide +kernel) hx

private theorem move22 {c : ℕ} (hx : Exceptional (79507*c)) : ∃ p ∈ ([43, 77659] : List ℕ), p ∣ c :=
  checked_guard 79507 77659 [43, 77659] [43, 43, 43] [77659] (by decide +kernel) (by decide +kernel)
    (cons pr43 (cons pr43 (cons pr43 (cons pr77659 nil)))) (by decide +kernel) hx

private theorem move23 {c : ℕ} (hx : Exceptional (605052*c)) : ∃ p ∈ ([14407] : List ℕ), p ∣ c :=
  checked_guard 605052 605094 [14407] [2, 2, 3, 3, 7, 7, 7, 7, 7] [2, 3, 7, 14407] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr2 (cons pr3 (cons pr7 (cons pr14407 nil))))))))))))) (by decide +kernel) hx

private theorem move24 {c : ℕ} (hx : Exceptional (605094*c)) : ∃ p ∈ ([14407] : List ℕ), p ∣ c :=
  checked_guard 605094 605052 [14407] [2, 3, 7, 14407] [2, 2, 3, 3, 7, 7, 7, 7, 7] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr7 (cons pr14407 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr7 (cons pr7 nil))))))))))))) (by decide +kernel) hx

private theorem move25 {c : ℕ} (hx : Exceptional (1087212*c)) : ∃ p ∈ ([43, 8429] : List ℕ), p ∣ c :=
  checked_guard 1087212 1062054 [43, 8429] [2, 2, 3, 7, 7, 43, 43] [2, 3, 3, 7, 8429] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr7 (cons pr7 (cons pr43 (cons pr43 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr8429 nil)))))))))))) (by decide +kernel) hx

private theorem move26 {c : ℕ} (hx : Exceptional (2226196*c)) : ∃ p ∈ ([43, 22189] : List ℕ), p ∣ c :=
  checked_guard 2226196 2174522 [43, 22189] [2, 2, 7, 43, 43, 43] [2, 7, 7, 22189] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr7 (cons pr43 (cons pr43 (cons pr43 (cons pr2 (cons pr7 (cons pr7 (cons pr22189 nil)))))))))) (by decide +kernel) hx

private theorem move27 {c : ℕ} (hx : Exceptional (2862252*c)) : ∃ p ∈ ([3, 22189] : List ℕ), p ∣ c :=
  checked_guard 2862252 1908254 [3, 22189] [2, 2, 3, 3, 43, 43, 43] [2, 43, 22189] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr43 (cons pr43 (cons pr43 (cons pr2 (cons pr43 (cons pr22189 nil)))))))))) (by decide +kernel) hx

private theorem move28 {c : ℕ} (hx : Exceptional (3261636*c)) : ∃ p ∈ ([3, 3613] : List ℕ), p ∣ c :=
  checked_guard 3261636 2175026 [3, 3613] [2, 2, 3, 3, 7, 7, 43, 43] [2, 7, 43, 3613] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr43 (cons pr43 (cons pr2 (cons pr7 (cons pr43 (cons pr3613 nil)))))))))))) (by decide +kernel) hx

private theorem move29 {c : ℕ} (hx : Exceptional (3261636*c)) : ∃ p ∈ ([7, 10837] : List ℕ), p ∣ c :=
  checked_guard 3261636 2795946 [7, 10837] [2, 2, 3, 3, 7, 7, 43, 43] [2, 3, 43, 10837] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr43 (cons pr43 (cons pr2 (cons pr3 (cons pr43 (cons pr10837 nil)))))))))))) (by decide +kernel) hx

private theorem move30 {c : ℕ} (hx : Exceptional (5074258*c)) : ∃ p ∈ ([8429] : List ℕ), p ∣ c :=
  checked_guard 5074258 5073656 [8429] [2, 7, 43, 8429] [2, 2, 2, 7, 7, 7, 43, 43] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr7 (cons pr43 (cons pr8429 (cons pr2 (cons pr2 (cons pr2 (cons pr7 (cons pr7 (cons pr7 (cons pr43 (cons pr43 nil)))))))))))) (by decide +kernel) hx

private theorem move31 {c : ℕ} (hx : Exceptional (5724762*c)) : ∃ p ∈ ([22189] : List ℕ), p ∣ c :=
  checked_guard 5724762 5724504 [22189] [2, 3, 43, 22189] [2, 2, 2, 3, 3, 43, 43, 43] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr43 (cons pr22189 (cons pr2 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr43 (cons pr43 (cons pr43 nil)))))))))))) (by decide +kernel) hx

private theorem move32 {c : ℕ} (hx : Exceptional (7610484*c)) : ∃ p ∈ ([7, 8429] : List ℕ), p ∣ c :=
  checked_guard 7610484 6524046 [7, 8429] [2, 2, 3, 7, 7, 7, 43, 43] [2, 3, 3, 43, 8429] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr2 (cons pr3 (cons pr7 (cons pr7 (cons pr7 (cons pr43 (cons pr43 (cons pr2 (cons pr3 (cons pr3 (cons pr43 (cons pr8429 nil))))))))))))) (by decide +kernel) hx

private theorem move33 {c : ℕ} (hx : Exceptional (19571622*c)) : ∃ p ∈ ([10837] : List ℕ), p ∣ c :=
  checked_guard 19571622 19569816 [10837] [2, 3, 7, 43, 10837] [2, 2, 2, 3, 3, 3, 7, 7, 43, 43] (by decide +kernel) (by decide +kernel)
    (cons pr2 (cons pr3 (cons pr7 (cons pr43 (cons pr10837 (cons pr2 (cons pr2 (cons pr2 (cons pr3 (cons pr3 (cons pr3 (cons pr7 (cons pr7 (cons pr43 (cons pr43 nil))))))))))))))) (by decide +kernel) hx

private theorem node1055200883739222832492361203044 : Covered terminalDivisors 1055200883739222832492361203044 := terminal (by decide +kernel)
private theorem node1058890560926616308414947525452 : Covered terminalDivisors 1058890560926616308414947525452 := terminal (by decide +kernel)
private theorem node1179830890079573981778405706284 : Covered terminalDivisors 1179830890079573981778405706284 := terminal (by decide +kernel)
private theorem node1271258272067794446879895942476 : Covered terminalDivisors 1271258272067794446879895942476 := terminal (by decide +kernel)
private theorem node1451661752699461555593837357204 : Covered terminalDivisors 1451661752699461555593837357204 := terminal (by decide +kernel)
private theorem node1479745867667685017644303693956 : Covered terminalDivisors 1479745867667685017644303693956 := terminal (by decide +kernel)
private theorem node1486036959566541944389105192236 : Covered terminalDivisors 1486036959566541944389105192236 := terminal (by decide +kernel)
private theorem node1598505421861519832645114414004 : Covered terminalDivisors 1598505421861519832645114414004 := terminal (by decide +kernel)
private theorem node1650872731811702470716731169636 : Covered terminalDivisors 1650872731811702470716731169636 := terminal (by decide +kernel)
private theorem node1889342105289635073113470697004 : Covered terminalDivisors 1889342105289635073113470697004 := terminal (by decide +kernel)
private theorem node1922638410317304721147460313708 : Covered terminalDivisors 1922638410317304721147460313708 := terminal (by decide +kernel)
private theorem node1973104206613466841967663490796 : Covered terminalDivisors 1973104206613466841967663490796 := terminal (by decide +kernel)
private theorem node1992036191855780700610888984524 : Covered terminalDivisors 1992036191855780700610888984524 := terminal (by decide +kernel)
private theorem node2397536916985213388625484364652 : Covered terminalDivisors 2397536916985213388625484364652 := terminal (by decide +kernel)
private theorem node2434845193492703339526347499372 : Covered terminalDivisors 2434845193492703339526347499372 := terminal (by decide +kernel)
private theorem node2666989767728135373865076800764 : Covered terminalDivisors 2666989767728135373865076800764 := terminal (by decide +kernel)
private theorem node2775921211786005666491448619188 : Covered terminalDivisors 2775921211786005666491448619188 := terminal (by decide +kernel)
private theorem node2882140600727074089008609425548 : Covered terminalDivisors 2882140600727074089008609425548 := terminal (by decide +kernel)
private theorem node2972858471024586846834841983036 : Covered terminalDivisors 2972858471024586846834841983036 := terminal (by decide +kernel)
private theorem node3073643254124258874823489055436 : Covered terminalDivisors 3073643254124258874823489055436 := terminal (by decide +kernel)
private theorem node3292784157696002503699735365516 : Covered terminalDivisors 3292784157696002503699735365516 := terminal (by decide +kernel)
private theorem node3385394425829429445374048416212 : Covered terminalDivisors 3385394425829429445374048416212 := terminal (by decide +kernel)
private theorem node3907819101854833914982880121804 : Covered terminalDivisors 3907819101854833914982880121804 := terminal (by decide +kernel)
private theorem node4161863133778889960152905260052 : Covered terminalDivisors 4161863133778889960152905260052 := terminal (by decide +kernel)
private theorem node4588525764015337336464772610292 : Covered terminalDivisors 4588525764015337336464772610292 := terminal (by decide +kernel)
private theorem node5080652577984022936854378986124 : Covered terminalDivisors 5080652577984022936854378986124 := terminal (by decide +kernel)
private theorem node5173104671887362843182240404476 : Covered terminalDivisors 5173104671887362843182240404476 := terminal (by decide +kernel)
private theorem node5178943816179401991312766711836 : Covered terminalDivisors 5178943816179401991312766711836 := terminal (by decide +kernel)
private theorem node5483382343365111288901330819356 : Covered terminalDivisors 5483382343365111288901330819356 := terminal (by decide +kernel)
private theorem node5681305451482974458894810831868 : Covered terminalDivisors 5681305451482974458894810831868 := terminal (by decide +kernel)
private theorem node6439493491455015092352789166356 : Covered terminalDivisors 6439493491455015092352789166356 := terminal (by decide +kernel)
private theorem node6926856828066585941462162460684 : Covered terminalDivisors 6926856828066585941462162460684 := terminal (by decide +kernel)
private theorem node7586943734533645155105787617612 : Covered terminalDivisors 7586943734533645155105787617612 := terminal (by decide +kernel)
private theorem node8187149122921751983491706353684 : Covered terminalDivisors 8187149122921751983491706353684 := terminal (by decide +kernel)
private theorem node10389326640269258017377098913492 : Covered terminalDivisors 10389326640269258017377098913492 := terminal (by decide +kernel)
private theorem node10550995838468381137947505830612 : Covered terminalDivisors 10550995838468381137947505830612 := terminal (by decide +kernel)
private theorem node11747326207225448718949157752644 : Covered terminalDivisors 11747326207225448718949157752644 := terminal (by decide +kernel)
private theorem node12171346851677101768462505484132 : Covered terminalDivisors 12171346851677101768462505484132 := terminal (by decide +kernel)
private theorem node12489275936483987719037307510708 : Covered terminalDivisors 12489275936483987719037307510708 := terminal (by decide +kernel)
private theorem node12882386707773209669617648593156 : Covered terminalDivisors 12882386707773209669617648593156 := terminal (by decide +kernel)
private theorem node13804496697586353038845320772044 : Covered terminalDivisors 13804496697586353038845320772044 := terminal (by decide +kernel)
private theorem node16963351423588625204955993504156 : Covered terminalDivisors 16963351423588625204955993504156 := terminal (by decide +kernel)
private theorem node21299863087120434536243841088716 : Covered terminalDivisors 21299863087120434536243841088716 := terminal (by decide +kernel)
private theorem node27354733712983837404880160852628 : Covered terminalDivisors 27354733712983837404880160852628 := terminal (by decide +kernel)
private theorem node30859086972081655414726578479556 : Covered terminalDivisors 30859086972081655414726578479556 := terminal (by decide +kernel)
private theorem node35776839942479358005048500095396 : Covered terminalDivisors 35776839942479358005048500095396 := terminal (by decide +kernel)
private theorem node44018758857051198356899390701444 : Covered terminalDivisors 44018758857051198356899390701444 := terminal (by decide +kernel)
private theorem node59683791282086166022231812576252 : Covered terminalDivisors 59683791282086166022231812576252 := terminal (by decide +kernel)
private theorem node248662521813890844964695854862756 : Covered terminalDivisors 248662521813890844964695854862756 := terminal (by decide +kernel)
private theorem node274638933979869109856856355799388 : Covered terminalDivisors 274638933979869109856856355799388 := terminal (by decide +kernel)
private theorem node343353574394923119770881373898348 : Covered terminalDivisors 343353574394923119770881373898348 := terminal (by decide +kernel)
private theorem node381779349957490866396142792587804 : Covered terminalDivisors 381779349957490866396142792587804 := terminal (by decide +kernel)
private theorem node813278374151685449448794697048348 : Covered terminalDivisors 813278374151685449448794697048348 := terminal (by decide +kernel)
private theorem node878929866760331662292506693018284 : Covered terminalDivisors 878929866760331662292506693018284 := terminal (by decide +kernel)
private theorem node1452848272951361699731423002421356 : Covered terminalDivisors 1452848272951361699731423002421356 := terminal (by decide +kernel)
private theorem node2016525536071090924175700628435092 : Covered terminalDivisors 2016525536071090924175700628435092 := terminal (by decide +kernel)
private theorem node2368958960286696857736916574917812 : Covered terminalDivisors 2368958960286696857736916574917812 := terminal (by decide +kernel)
private theorem node3915827717666671233104590946622708 : Covered terminalDivisors 3915827717666671233104590946622708 := terminal (by decide +kernel)
private theorem node4383867929356961221541191599783276 : Covered terminalDivisors 4383867929356961221541191599783276 := terminal (by decide +kernel)
private theorem node6090845383587001201912188904850604 : Covered terminalDivisors 6090845383587001201912188904850604 := terminal (by decide +kernel)
private theorem node19486647341687624162928551844198084 : Covered terminalDivisors 19486647341687624162928551844198084 := terminal (by decide +kernel)
private theorem node990952823674862282278280661012 : Covered terminalDivisors 990952823674862282278280661012 :=
  ascend (q:=27526467324301730063285573917) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node2972858471024586846834841983036⟩ (cons ⟨by decide +kernel, node12882386707773209669617648593156⟩ nil))
private theorem node960713533575691363002869808516 : Covered terminalDivisors 960713533575691363002869808516 :=
  ascend (q:=26686487043769204527857494681) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node2882140600727074089008609425548⟩ (cons ⟨by decide +kernel, node12489275936483987719037307510708⟩ nil))
private theorem node892807969662559221313473342324 : Covered terminalDivisors 892807969662559221313473342324 :=
  ascend (q:=8266740459838511308458086503) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node16963351423588625204955993504156⟩ nil)
private theorem node878212057401758716613121449556 : Covered terminalDivisors 878212057401758716613121449556 :=
  ascend (q:=153405863405633058040338) (@move31) (by decide +kernel) (cons ⟨by decide +kernel, node19486647341687624162928551844198084⟩ nil)
private theorem node811615064497567779842115833124 : Covered terminalDivisors 811615064497567779842115833124 :=
  ascend (q:=22544862902710216106725439809) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node2434845193492703339526347499372⟩ (cons ⟨by decide +kernel, node10550995838468381137947505830612⟩ nil))
private theorem node799178972328404462875161454884 : Covered terminalDivisors 799178972328404462875161454884 :=
  ascend (q:=22199415898011235079865595969) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node2397536916985213388625484364652⟩ (cons ⟨by decide +kernel, node10389326640269258017377098913492⟩ nil))
private theorem node746080658594088107744057469516 : Covered terminalDivisors 746080658594088107744057469516 :=
  ascend (q:=221783786740216441065415419) (@move8) (by decide +kernel) (cons ⟨by decide +kernel, node44018758857051198356899390701444⟩ nil)
private theorem node726552457767702791518174777476 : Covered terminalDivisors 726552457767702791518174777476 :=
  ascend (q:=6727337571923173995538655347) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node13804496697586353038845320772044⟩ nil)
private theorem node640597202719847461498026604428 : Covered terminalDivisors 640597202719847461498026604428 :=
  ascend (q:=5931455580739328347203950041) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node12171346851677101768462505484132⟩ nil)
private theorem node629780701763211691037823565668 : Covered terminalDivisors 629780701763211691037823565668 :=
  ascend (q:=17493908382311435862161765713) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node1889342105289635073113470697004⟩ (cons ⟨by decide +kernel, node8187149122921751983491706353684⟩ nil))
private theorem node618280326696076248365745144876 : Covered terminalDivisors 618280326696076248365745144876 :=
  ascend (q:=5724817839778483781164306897) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node11747326207225448718949157752644⟩ nil)
private theorem node532835140620506610881704804668 : Covered terminalDivisors 532835140620506610881704804668 :=
  ascend (q:=14800976128347405857825133463) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node1598505421861519832645114414004⟩ (cons ⟨by decide +kernel, node6926856828066585941462162460684⟩ nil))
private theorem node495345653188847314796368397412 : Covered terminalDivisors 495345653188847314796368397412 :=
  ascend (q:=13759601477467980966565788817) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node1486036959566541944389105192236⟩ (cons ⟨by decide +kernel, node6439493491455015092352789166356⟩ nil))
private theorem node399312828133349745005567769348 : Covered terminalDivisors 399312828133349745005567769348 :=
  ascend (q:=3502744106432892500048840082) (@move2) (by decide +kernel) (cons ⟨by decide +kernel, node7586943734533645155105787617612⟩ nil)
private theorem node352963520308872102804982508484 : Covered terminalDivisors 352963520308872102804982508484 :=
  ascend (q:=9804542230802002855693958569) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node1058890560926616308414947525452⟩ (cons ⟨by decide +kernel, node4588525764015337336464772610292⟩ nil))
private theorem node311029370305627530981717277236 : Covered terminalDivisors 311029370305627530981717277236 :=
  ascend (q:=8386705773219746831195526) (@move18) (by decide +kernel) (cons ⟨by decide +kernel, node274638933979869109856856355799388⟩ nil)
private theorem node304287355407576957141749954868 : Covered terminalDivisors 304287355407576957141749954868 :=
  ascend (q:=502911081043574696293459) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node4383867929356961221541191599783276⟩ nil)
private theorem node274498417395421208793194326236 : Covered terminalDivisors 274498417395421208793194326236 :=
  ascend (q:=47949315167236857845478) (@move31) (by decide +kernel) (cons ⟨by decide +kernel, node6090845383587001201912188904850604⟩ nil)
private theorem node272268666941440149641170547604 : Covered terminalDivisors 272268666941440149641170547604 :=
  ascend (q:=2521006175383705089270097663) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node5173104671887362843182240404476⟩ nil)
private theorem node271800355220842037419628718444 : Covered terminalDivisors 271800355220842037419628718444 :=
  ascend (q:=449186994451840602319026) (@move24) (by decide +kernel) (cons ⟨by decide +kernel, node3915827717666671233104590946622708⟩ nil)
private theorem node213532400906615820499342201476 : Covered terminalDivisors 213532400906615820499342201476 :=
  ascend (q:=5931455580739328347203950041) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node640597202719847461498026604428⟩ (cons ⟨by decide +kernel, node2775921211786005666491448619188⟩ nil))
private theorem node181608324581113492411413706068 : Covered terminalDivisors 181608324581113492411413706068 :=
  ascend (q:=44122527837977038972646673) (@move10) (by decide +kernel) (cons ⟨by decide +kernel, node1271258272067794446879895942476⟩ (cons ⟨by decide +kernel, node35776839942479358005048500095396⟩ nil))
private theorem node173304429352421184405249229764 : Covered terminalDivisors 173304429352421184405249229764 :=
  ascend (q:=1604670642152048003752307683) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node3292784157696002503699735365516⟩ nil)
private theorem node164431107120614760723045503916 : Covered terminalDivisors 164431107120614760723045503916 :=
  ascend (q:=271744732422755407792914) (@move24) (by decide +kernel) (cons ⟨by decide +kernel, node2368958960286696857736916574917812⟩ nil)
private theorem node104844010097672668453204683396 : Covered terminalDivisors 104844010097672668453204683396 :=
  ascend (q:=970777871274746930122265587) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node1992036191855780700610888984524⟩ nil)
private theorem node101191495279858143218287384932 : Covered terminalDivisors 101191495279858143218287384932 :=
  ascend (q:=936958289628316140910068379) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node1922638410317304721147460313708⟩ nil)
private theorem node90879513996624044534485584228 : Covered terminalDivisors 90879513996624044534485584228 :=
  ascend (q:=40822781999708940513093) (@move26) (by decide +kernel) (cons ⟨by decide +kernel, node3907819101854833914982880121804⟩ (cons ⟨by decide +kernel, node2016525536071090924175700628435092⟩ nil))
private theorem node90756222313813383213723515868 : Covered terminalDivisors 90756222313813383213723515868 :=
  ascend (q:=2521006175383705089270097663) (@move0) (by decide +kernel) (cons ⟨by decide +kernel, node272268666941440149641170547604⟩ (cons ⟨by decide +kernel, node1179830890079573981778405706284⟩ nil))
private theorem node56450223790635486183715880964 : Covered terminalDivisors 56450223790635486183715880964 :=
  ascend (q:=93291660123279170151606) (@move24) (by decide +kernel) (cons ⟨by decide +kernel, node813278374151685449448794697048348⟩ nil)
private theorem node50423360044124586114997501212 : Covered terminalDivisors 50423360044124586114997501212 :=
  ascend (q:=750035105077119445989729) (@move21) (by decide +kernel) (cons ⟨by decide +kernel, node352963520308872102804982508484⟩ (cons ⟨by decide +kernel, node1452848272951361699731423002421356⟩ nil))
private theorem node43469622201082422448821422124 : Covered terminalDivisors 43469622201082422448821422124 :=
  ascend (q:=1508733243130724088880377) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node304287355407576957141749954868⟩ (cons ⟨by decide +kernel, node59683791282086166022231812576252⟩ nil))
private theorem node33442444179889268507926499844 : Covered terminalDivisors 33442444179889268507926499844 :=
  ascend (q:=1067459675696296355068036) (@move16) (by decide +kernel) (cons ⟨by decide +kernel, node1973104206613466841967663490796⟩ (cons ⟨by decide +kernel, node343353574394923119770881373898348⟩ nil))
private theorem node32770575856526692599629175276 : Covered terminalDivisors 32770575856526692599629175276 :=
  ascend (q:=6192474651649034882771953) (@move11) (by decide +kernel) (cons ⟨by decide +kernel, node4161863133778889960152905260052⟩ nil)
private theorem node30504628700945117214191743068 : Covered terminalDivisors 30504628700945117214191743068 :=
  ascend (q:=453748865070284958859281) (@move21) (by decide +kernel) (cons ⟨by decide +kernel, node213532400906615820499342201476⟩ (cons ⟨by decide +kernel, node878929866760331662292506693018284⟩ nil))
private theorem node26499573121225159047417421572 : Covered terminalDivisors 26499573121225159047417421572 :=
  ascend (q:=43794142928578301962038) (@move24) (by decide +kernel) (cons ⟨by decide +kernel, node381779349957490866396142792587804⟩ nil)
private theorem node25726919261865107163588188604 : Covered terminalDivisors 25726919261865107163588188604 :=
  ascend (q:=63366796211490411732975834) (@move3) (by decide +kernel) (cons ⟨by decide +kernel, node746080658594088107744057469516⟩ nil)
private theorem node22475664218559108095212365972 : Covered terminalDivisors 22475664218559108095212365972 :=
  ascend (q:=1169267725447877853252126) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node30859086972081655414726578479556⟩ nil)
private theorem node21016464638597355000293040492 : Covered terminalDivisors 21016464638597355000293040492 :=
  ascend (q:=194596894801827361113824449) (@move1) (by decide +kernel) (cons ⟨by decide +kernel, node399312828133349745005567769348⟩ nil)
private theorem node17259840481286238978600392508 : Covered terminalDivisors 17259840481286238978600392508 :=
  ascend (q:=28526210112992336160529) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node248662521813890844964695854862756⟩ nil)
private theorem node7029984013091017490657270412 : Covered terminalDivisors 7029984013091017490657270412 :=
  ascend (q:=1328417236033827946080361) (@move11) (by decide +kernel) (cons ⟨by decide +kernel, node892807969662559221313473342324⟩ nil)
private theorem node6390669799193447085370990812 : Covered terminalDivisors 6390669799193447085370990812 :=
  ascend (q:=1198100824745678118742218) (@move12) (by decide +kernel) (cons ⟨by decide +kernel, node811615064497567779842115833124⟩ nil)
private theorem node6209946028726060349831631732 : Covered terminalDivisors 6209946028726060349831631732 :=
  ascend (q:=2011644324174298785173836) (@move7) (by decide +kernel) (cons ⟨by decide +kernel, node43469622201082422448821422124⟩ (cons ⟨by decide +kernel, node5483382343365111288901330819356⟩ nil))
private theorem node3700402460294262881904136188 : Covered terminalDivisors 3700402460294262881904136188 :=
  ascend (q:=192508711907931686708154) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node5080652577984022936854378986124⟩ nil)
private theorem node3245311865343912374526060132 : Covered terminalDivisors 3245311865343912374526060132 :=
  ascend (q:=639563826936650121954) (@move30) (by decide +kernel) (cons ⟨by decide +kernel, node27354733712983837404880160852628⟩ nil)
private theorem node2465691497326605568371484644 : Covered terminalDivisors 2465691497326605568371484644 :=
  ascend (q:=85578630338977008481587) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node17259840481286238978600392508⟩ (cons ⟨by decide +kernel, node3385394425829429445374048416212⟩ nil))
private theorem node2238633105698659049398025532 : Covered terminalDivisors 2238633105698659049398025532 :=
  ascend (q:=116462028181180889054106) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node3073643254124258874823489055436⟩ nil)
private theorem node959928932674768332788491644 : Covered terminalDivisors 959928932674768332788491644 :=
  ascend (q:=167680146820910342262) (@move31) (by decide +kernel) (cons ⟨by decide +kernel, node21299863087120434536243841088716⟩ nil)
private theorem node887135146960865764261661676 : Covered terminalDivisors 887135146960865764261661676 :=
  ascend (q:=1508733243130724088880377) (@move5) (by decide +kernel) (cons ⟨by decide +kernel, node6209946028726060349831631732⟩ (cons ⟨by decide +kernel, node25726919261865107163588188604⟩ nil))
private theorem node822822715478712108174603372 : Covered terminalDivisors 822822715478712108174603372 :=
  ascend (q:=22212037454883708783463) (@move17) (by decide +kernel) (cons ⟨by decide +kernel, node726552457767702791518174777476⟩ nil)
private theorem node768536696095573803708930228 : Covered terminalDivisors 768536696095573803708930228 :=
  ascend (q:=39982140052833930064974) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node1055200883739222832492361203044⟩ nil)
private theorem node700204220493857585918171172 : Covered terminalDivisors 700204220493857585918171172 :=
  ascend (q:=18901960384781815838413) (@move17) (by decide +kernel) (cons ⟨by decide +kernel, node618280326696076248365745144876⟩ nil)
private theorem node674018917010674393035331692 : Covered terminalDivisors 674018917010674393035331692 :=
  ascend (q:=132831030075860232774) (@move30) (by decide +kernel) (cons ⟨by decide +kernel, node5681305451482974458894810831868⟩ nil)
private theorem node566821087794733364541127116 : Covered terminalDivisors 566821087794733364541127116 :=
  ascend (q:=165640294504597710269178) (@move9) (by decide +kernel) (cons ⟨by decide +kernel, node33442444179889268507926499844⟩ nil)
private theorem node460691483826463874181337644 : Covered terminalDivisors 460691483826463874181337644 :=
  ascend (q:=167038246492553979036018) (@move6) (by decide +kernel) (cons ⟨by decide +kernel, node90756222313813383213723515868⟩ nil)
private theorem node360776149445628051563269044 : Covered terminalDivisors 360776149445628051563269044 :=
  ascend (q:=18768918397962129412302) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node495345653188847314796368397412⟩ nil)
private theorem node352241642475229366910212092 : Covered terminalDivisors 352241642475229366910212092 :=
  ascend (q:=114104840451969344642116) (@move7) (by decide +kernel) (cons ⟨by decide +kernel, node2465691497326605568371484644⟩ (cons ⟨by decide +kernel, node311029370305627530981717277236⟩ nil))
private theorem node316406426352845577632587116 : Covered terminalDivisors 316406426352845577632587116 :=
  ascend (q:=62355210624458901702) (@move30) (by decide +kernel) (cons ⟨by decide +kernel, node2666989767728135373865076800764⟩ nil)
private theorem node274274238492904036058201124 : Covered terminalDivisors 274274238492904036058201124 :=
  ascend (q:=84091001722112472409) (@move28) (by decide +kernel) (cons ⟨by decide +kernel, node822822715478712108174603372⟩ (cons ⟨by decide +kernel, node990952823674862282278280661012⟩ nil))
private theorem node233401406831285861972723724 : Covered terminalDivisors 233401406831285861972723724 :=
  ascend (q:=81544674204537497737) (@move27) (by decide +kernel) (cons ⟨by decide +kernel, node700204220493857585918171172⟩ (cons ⟨by decide +kernel, node5178943816179401991312766711836⟩ nil))
private theorem node205671941767965450069551196 : Covered terminalDivisors 205671941767965450069551196 :=
  ascend (q:=5545810865770518526386) (@move18) (by decide +kernel) (cons ⟨by decide +kernel, node181608324581113492411413706068⟩ nil)
private theorem node196267756911009268862116908 : Covered terminalDivisors 196267756911009268862116908 :=
  ascend (q:=5298233368723930160407) (@move17) (by decide +kernel) (cons ⟨by decide +kernel, node173304429352421184405249229764⟩ nil)
private theorem node165483973532262637797582996 : Covered terminalDivisors 165483973532262637797582996 :=
  ascend (q:=31024366991425316422494) (@move12) (by decide +kernel) (cons ⟨by decide +kernel, node21016464638597355000293040492⟩ nil)
private theorem node147477204710906894791504236 : Covered terminalDivisors 147477204710906894791504236 :=
  ascend (q:=2267903129588898548187) (@move19) (by decide +kernel) (cons ⟨by decide +kernel, node532835140620506610881704804668⟩ (cons ⟨by decide +kernel, node799178972328404462875161454884⟩ nil))
private theorem node118736138275959986923221612 : Covered terminalDivisors 118736138275959986923221612 :=
  ascend (q:=3205273142100204808423) (@move17) (by decide +kernel) (cons ⟨by decide +kernel, node104844010097672668453204683396⟩ nil)
private theorem node114599654903576606136225804 : Covered terminalDivisors 114599654903576606136225804 :=
  ascend (q:=3090105562842490593114) (@move18) (by decide +kernel) (cons ⟨by decide +kernel, node101191495279858143218287384932⟩ nil)
private theorem node114588237093892029618708348 : Covered terminalDivisors 114588237093892029618708348 :=
  ascend (q:=189385766998360520449) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node1650872731811702470716731169636⟩ nil)
private theorem node66688262998228176918486804 : Covered terminalDivisors 66688262998228176918486804 :=
  ascend (q:=11649089167065491442) (@move31) (by decide +kernel) (cons ⟨by decide +kernel, node1479745867667685017644303693956⟩ nil)
private theorem node65422585637003089620705636 : Covered terminalDivisors 65422585637003089620705636 :=
  ascend (q:=22857032028278114443) (@move27) (by decide +kernel) (cons ⟨by decide +kernel, node196267756911009268862116908⟩ (cons ⟨by decide +kernel, node1451661752699461555593837357204⟩ nil))
private theorem node58113933908204456126033364 : Covered terminalDivisors 58113933908204456126033364 :=
  ascend (q:=2969295744021852462) (@move33) (by decide +kernel) (cons ⟨by decide +kernel, node629780701763211691037823565668⟩ nil)
private theorem node50320234639318480987173156 : Covered terminalDivisors 50320234639318480987173156 :=
  ascend (q:=114104840451969344642116) (@move4) (by decide +kernel) (cons ⟨by decide +kernel, node352241642475229366910212092⟩ (cons ⟨by decide +kernel, node6390669799193447085370990812⟩ nil))
private theorem node39578712758653328974407204 : Covered terminalDivisors 39578712758653328974407204 :=
  ascend (q:=13827822553238963227) (@move27) (by decide +kernel) (cons ⟨by decide +kernel, node118736138275959986923221612⟩ (cons ⟨by decide +kernel, node878212057401758716613121449556⟩ nil))
private theorem node37112769939441327972399972 : Covered terminalDivisors 37112769939441327972399972 :=
  ascend (q:=1001856439354317243613) (@move17) (by decide +kernel) (cons ⟨by decide +kernel, node32770575856526692599629175276⟩ nil)
private theorem node33343058118755123138960532 : Covered terminalDivisors 33343058118755123138960532 :=
  ascend (q:=495969806014683214419) (@move21) (by decide +kernel) (cons ⟨by decide +kernel, node233401406831285861972723724⟩ (cons ⟨by decide +kernel, node960713533575691363002869808516⟩ nil))
private theorem node28382563511794659112074612 : Covered terminalDivisors 28382563511794659112074612 :=
  ascend (q:=4957859123539923426) (@move31) (by decide +kernel) (cons ⟨by decide +kernel, node629780701763211691037823565668⟩ nil)
private theorem node18865853766977305297399092 : Covered terminalDivisors 18865853766977305297399092 :=
  ascend (q:=31180549385800402771) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node271800355220842037419628718444⟩ nil)
private theorem node16369748156270289945529764 : Covered terminalDivisors 16369748156270289945529764 :=
  ascend (q:=568157300995081561347) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node114588237093892029618708348⟩ (cons ⟨by decide +kernel, node22475664218559108095212365972⟩ nil))
private theorem node12370923313147109324133324 : Covered terminalDivisors 12370923313147109324133324 :=
  ascend (q:=4322094390412552537) (@move27) (by decide +kernel) (cons ⟨by decide +kernel, node37112769939441327972399972⟩ (cons ⟨by decide +kernel, node274498417395421208793194326236⟩ nil))
private theorem node11413278761755727127302388 : Covered terminalDivisors 11413278761755727127302388 :=
  ascend (q:=18863302264525573219) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node164431107120614760723045503916⟩ nil)
private theorem node9607137081266667195612324 : Covered terminalDivisors 9607137081266667195612324 :=
  ascend (q:=2855867146630995004641) (@move8) (by decide +kernel) (cons ⟨by decide +kernel, node566821087794733364541127116⟩ nil)
private theorem node7961476798517573602103364 : Covered terminalDivisors 7961476798517573602103364 :=
  ascend (q:=214676071793064056574) (@move18) (by decide +kernel) (cons ⟨by decide +kernel, node7029984013091017490657270412⟩ nil)
private theorem node6985316117802092631981588 : Covered terminalDivisors 6985316117802092631981588 :=
  ascend (q:=1309583074203616916382) (@move12) (by decide +kernel) (cons ⟨by decide +kernel, node887135146960865764261661676⟩ nil)
private theorem node3918249725177725146367452 : Covered terminalDivisors 3918249725177725146367452 :=
  ascend (q:=6475889221385476201) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node56450223790635486183715880964⟩ nil)
private theorem node3499920874861149865690116 : Covered terminalDivisors 3499920874861149865690116 :=
  ascend (q:=5784094495832300214) (@move24) (by decide +kernel) (cons ⟨by decide +kernel, node50423360044124586114997501212⟩ nil)
private theorem node2695121966711043613914156 : Covered terminalDivisors 2695121966711043613914156 :=
  ascend (q:=93541648157401208313) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node18865853766977305297399092⟩ (cons ⟨by decide +kernel, node3700402460294262881904136188⟩ nil))
private theorem node2338535450895755706504252 : Covered terminalDivisors 2338535450895755706504252 :=
  ascend (q:=568157300995081561347) (@move10) (by decide +kernel) (cons ⟨by decide +kernel, node16369748156270289945529764⟩ (cons ⟨by decide +kernel, node460691483826463874181337644⟩ nil))
private theorem node2117347726865073729033924 : Covered terminalDivisors 2117347726865073729033924 :=
  ascend (q:=3499204630793023446) (@move24) (by decide +kernel) (cons ⟨by decide +kernel, node30504628700945117214191743068⟩ nil)
private theorem node1839354003000288682405596 : Covered terminalDivisors 1839354003000288682405596 :=
  ascend (q:=3039993261736658473) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node26499573121225159047417421572⟩ nil)
private theorem node1630468394536532446757484 : Covered terminalDivisors 1630468394536532446757484 :=
  ascend (q:=56589906793576719657) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node11413278761755727127302388⟩ (cons ⟨by decide +kernel, node2238633105698659049398025532⟩ nil))
private theorem node1303023413639863289744748 : Covered terminalDivisors 1303023413639863289744748 :=
  ascend (q:=246225134852581876369) (@move11) (by decide +kernel) (cons ⟨by decide +kernel, node165483973532262637797582996⟩ nil)
private theorem node1170238014867871650864492 : Covered terminalDivisors 1170238014867871650864492 :=
  ascend (q:=14718679045466080356) (@move22) (by decide +kernel) (cons ⟨by decide +kernel, node50320234639318480987173156⟩ (cons ⟨by decide +kernel, node90879513996624044534485584228⟩ nil))
private theorem node559749960739675020909636 : Covered terminalDivisors 559749960739675020909636 :=
  ascend (q:=19427667664156428603) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node3918249725177725146367452⟩ (cons ⟨by decide +kernel, node768536696095573803708930228⟩ nil))
private theorem node385017423815863373416308 : Covered terminalDivisors 385017423815863373416308 :=
  ascend (q:=50590399219795137) (@move32) (by decide +kernel) (cons ⟨by decide +kernel, node2695121966711043613914156⟩ (cons ⟨by decide +kernel, node3245311865343912374526060132⟩ nil))
private theorem node331280589009195420538356 : Covered terminalDivisors 331280589009195420538356 :=
  ascend (q:=815962041894570001326) (@move3) (by decide +kernel) (cons ⟨by decide +kernel, node9607137081266667195612324⟩ nil)
private theorem node262764857571469811772228 : Covered terminalDivisors 262764857571469811772228 :=
  ascend (q:=9119979785209975419) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node1839354003000288682405596⟩ (cons ⟨by decide +kernel, node360776149445628051563269044⟩ nil))
private theorem node232924056362361778108212 : Covered terminalDivisors 232924056362361778108212 :=
  ascend (q:=75453209058102292876) (@move7) (by decide +kernel) (cons ⟨by decide +kernel, node1630468394536532446757484⟩ (cons ⟨by decide +kernel, node205671941767965450069551196⟩ nil))
private theorem node129784433639384604910788 : Covered terminalDivisors 129784433639384604910788 :=
  ascend (q:=3503521046306678677) (@move17) (by decide +kernel) (cons ⟨by decide +kernel, node114599654903576606136225804⟩ nil)
private theorem node79964280105667860129948 : Covered terminalDivisors 79964280105667860129948 :=
  ascend (q:=10507121505763347) (@move32) (by decide +kernel) (cons ⟨by decide +kernel, node559749960739675020909636⟩ (cons ⟨by decide +kernel, node674018917010674393035331692⟩ nil))
private theorem node55002489116551910488044 : Covered terminalDivisors 55002489116551910488044 :=
  ascend (q:=124722197543201611084) (@move4) (by decide +kernel) (cons ⟨by decide +kernel, node385017423815863373416308⟩ (cons ⟨by decide +kernel, node6985316117802092631981588⟩ nil))
private theorem node47649370456666489162932 : Covered terminalDivisors 47649370456666489162932 :=
  ascend (q:=2478897641070985806) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node65422585637003089620705636⟩ nil)
private theorem node43261477879794868303596 : Covered terminalDivisors 43261477879794868303596 :=
  ascend (q:=15114489527754673) (@move27) (by decide +kernel) (cons ⟨by decide +kernel, node129784433639384604910788⟩ (cons ⟨by decide +kernel, node959928932674768332788491644⟩ nil))
private theorem node41789256433174678717548 : Covered terminalDivisors 41789256433174678717548 :=
  ascend (q:=8235540335784006) (@move30) (by decide +kernel) (cons ⟨by decide +kernel, node352241642475229366910212092⟩ nil)
private theorem node37537836795924258824604 : Covered terminalDivisors 37537836795924258824604 :=
  ascend (q:=4932384956846931) (@move32) (by decide +kernel) (cons ⟨by decide +kernel, node262764857571469811772228⟩ (cons ⟨by decide +kernel, node316406426352845577632587116⟩ nil))
private theorem node28826447748472927148148 : Covered terminalDivisors 28826447748472927148148 :=
  ascend (q:=1499659127482724334) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node39578712758653328974407204⟩ nil)
private theorem node27214837555066782578244 : Covered terminalDivisors 27214837555066782578244 :=
  ascend (q:=1635408782829564484) (@move13) (by decide +kernel) (cons ⟨by decide +kernel, node1170238014867871650864492⟩ (cons ⟨by decide +kernel, node147477204710906894791504236⟩ nil))
private theorem node12360820158317366084916 : Covered terminalDivisors 12360820158317366084916 :=
  ascend (q:=2159184985911618) (@move31) (by decide +kernel) (cons ⟨by decide +kernel, node274274238492904036058201124⟩ nil)
private theorem node11423468586523980018564 : Covered terminalDivisors 11423468586523980018564 :=
  ascend (q:=19427667664156428603) (@move5) (by decide +kernel) (cons ⟨by decide +kernel, node79964280105667860129948⟩ (cons ⟨by decide +kernel, node331280589009195420538356⟩ nil))
private theorem node9016395015308690376108 : Covered terminalDivisors 9016395015308690376108 :=
  ascend (q:=243396906794857207) (@move17) (by decide +kernel) (cons ⟨by decide +kernel, node7961476798517573602103364⟩ nil)
private theorem node5362548113703465546372 : Covered terminalDivisors 5362548113703465546372 :=
  ascend (q:=1644128318948977) (@move29) (by decide +kernel) (cons ⟨by decide +kernel, node37537836795924258824604⟩ (cons ⟨by decide +kernel, node58113933908204456126033364⟩ nil))
private theorem node3005465005102896792036 : Covered terminalDivisors 3005465005102896792036 :=
  ascend (q:=1050035079057643) (@move27) (by decide +kernel) (cons ⟨by decide +kernel, node9016395015308690376108⟩ (cons ⟨by decide +kernel, node66688262998228176918486804⟩ nil))
private theorem node2648398019134491173844 : Covered terminalDivisors 2648398019134491173844 :=
  ascend (q:=71412339403939254) (@move18) (by decide +kernel) (cons ⟨by decide +kernel, node2338535450895755706504252⟩ nil)
private theorem node2314365108541342620876 : Covered terminalDivisors 2314365108541342620876 :=
  ascend (q:=3824802606770754) (@move24) (by decide +kernel) (cons ⟨by decide +kernel, node33343058118755123138960532⟩ nil)
private theorem node1475677705141408029156 : Covered terminalDivisors 1475677705141408029156 :=
  ascend (q:=39790694740371246) (@move18) (by decide +kernel) (cons ⟨by decide +kernel, node1303023413639863289744748⟩ nil)
private theorem node1279127653873300243908 : Covered terminalDivisors 1279127653873300243908 :=
  ascend (q:=574579980322173) (@move26) (by decide +kernel) (cons ⟨by decide +kernel, node55002489116551910488044⟩ (cons ⟨by decide +kernel, node28382563511794659112074612⟩ nil))
private theorem node429352143586128113148 : Covered terminalDivisors 429352143586128113148 :=
  ascend (q:=6386507758465641) (@move21) (by decide +kernel) (cons ⟨by decide +kernel, node3005465005102896792036⟩ (cons ⟨by decide +kernel, node12370923313147109324133324⟩ nil))
private theorem node242931968824956608988 : Covered terminalDivisors 242931968824956608988 :=
  ascend (q:=401505934737769) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node3499920874861149865690116⟩ nil)
private theorem node146966594493306984732 : Covered terminalDivisors 146966594493306984732 :=
  ascend (q:=242899113618841) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node2117347726865073729033924⟩ nil)
private theorem node89948571547432913532 : Covered terminalDivisors 89948571547432913532 :=
  ascend (q:=16863249258986298) (@move12) (by decide +kernel) (cons ⟨by decide +kernel, node11423468586523980018564⟩ nil)
private theorem node34704566974993801284 : Covered terminalDivisors 34704566974993801284 :=
  ascend (q:=1204517804213307) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node242931968824956608988⟩ (cons ⟨by decide +kernel, node47649370456666489162932⟩ nil))
private theorem node31508723874577471452 : Covered terminalDivisors 31508723874577471452 :=
  ascend (q:=1639201117187466) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node43261477879794868303596⟩ nil)
private theorem node27633652433546301828 : Covered terminalDivisors 27633652433546301828 :=
  ascend (q:=5445850887666) (@move30) (by decide +kernel) (cons ⟨by decide +kernel, node232924056362361778108212⟩ nil)
private theorem node20995227784758140676 : Covered terminalDivisors 20995227784758140676 :=
  ascend (q:=728697340856523) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node146966594493306984732⟩ (cons ⟨by decide +kernel, node28826447748472927148148⟩ nil))
private theorem node5075435001988734012 : Covered terminalDivisors 5075435001988734012 :=
  ascend (q:=259326232746) (@move33) (by decide +kernel) (cons ⟨by decide +kernel, node55002489116551910488044⟩ nil)
private theorem node4957795282141971612 : Covered terminalDivisors 4957795282141971612 :=
  ascend (q:=651442836243) (@move32) (by decide +kernel) (cons ⟨by decide +kernel, node34704566974993801284⟩ (cons ⟨by decide +kernel, node41789256433174678717548⟩ nil))
private theorem node3228714860015041236 : Covered terminalDivisors 3228714860015041236 :=
  ascend (q:=636293002842) (@move30) (by decide +kernel) (cons ⟨by decide +kernel, node27214837555066782578244⟩ nil)
private theorem node2999318254965448668 : Covered terminalDivisors 2999318254965448668 :=
  ascend (q:=971596454475364) (@move7) (by decide +kernel) (cons ⟨by decide +kernel, node20995227784758140676⟩ (cons ⟨by decide +kernel, node2648398019134491173844⟩ nil))
private theorem node1671209179095592332 : Covered terminalDivisors 1671209179095592332 :=
  ascend (q:=45114166372303) (@move17) (by decide +kernel) (cons ⟨by decide +kernel, node1475677705141408029156⟩ nil)
private theorem node708256468877424516 : Covered terminalDivisors 708256468877424516 :=
  ascend (q:=1606023738951076) (@move4) (by decide +kernel) (cons ⟨by decide +kernel, node4957795282141971612⟩ (cons ⟨by decide +kernel, node89948571547432913532⟩ nil))
private theorem node557069726365197444 : Covered terminalDivisors 557069726365197444 :=
  ascend (q:=194626373347) (@move27) (by decide +kernel) (cons ⟨by decide +kernel, node1671209179095592332⟩ (cons ⟨by decide +kernel, node12360820158317366084916⟩ nil))
private theorem node241675970692841748 : Covered terminalDivisors 241675970692841748 :=
  ascend (q:=42215898354) (@move31) (by decide +kernel) (cons ⟨by decide +kernel, node5362548113703465546372⟩ nil)
private theorem node160641709484371668 : Covered terminalDivisors 160641709484371668 :=
  ascend (q:=265500666859) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node2314365108541342620876⟩ nil)
private theorem node29801634176867364 : Covered terminalDivisors 29801634176867364 :=
  ascend (q:=49251247206) (@move24) (by decide +kernel) (cons ⟨by decide +kernel, node429352143586128113148⟩ nil)
private theorem node22948815640624524 : Covered terminalDivisors 22948815640624524 :=
  ascend (q:=796502000577) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node160641709484371668⟩ (cons ⟨by decide +kernel, node31508723874577471452⟩ nil))
private theorem node16471080671568012 : Covered terminalDivisors 16471080671568012 :=
  ascend (q:=207165163716) (@move22) (by decide +kernel) (cons ⟨by decide +kernel, node708256468877424516⟩ (cons ⟨by decide +kernel, node1279127653873300243908⟩ nil))
private theorem node3278402234374932 : Covered terminalDivisors 3278402234374932 :=
  ascend (q:=430774473) (@move32) (by decide +kernel) (cons ⟨by decide +kernel, node22948815640624524⟩ (cons ⟨by decide +kernel, node27633652433546301828⟩ nil))
private theorem node468343176339276 : Covered terminalDivisors 468343176339276 :=
  ascend (q:=143591491) (@move29) (by decide +kernel) (cons ⟨by decide +kernel, node3278402234374932⟩ (cons ⟨by decide +kernel, node5075435001988734012⟩ nil))
private theorem node405731774483028 : Covered terminalDivisors 405731774483028 :=
  ascend (q:=21107677374) (@move14) (by decide +kernel) (cons ⟨by decide +kernel, node557069726365197444⟩ nil)
private theorem node383048387710884 : Covered terminalDivisors 383048387710884 :=
  ascend (q:=352321707) (@move25) (by decide +kernel) (cons ⟨by decide +kernel, node16471080671568012⟩ (cons ⟨by decide +kernel, node3228714860015041236⟩ nil))
private theorem node355833225170892 : Covered terminalDivisors 355833225170892 :=
  ascend (q:=70125174) (@move30) (by decide +kernel) (cons ⟨by decide +kernel, node2999318254965448668⟩ nil)
private theorem node65355399914868 : Covered terminalDivisors 65355399914868 :=
  ascend (q:=3339294) (@move33) (by decide +kernel) (cons ⟨by decide +kernel, node708256468877424516⟩ nil)
private theorem node10891701775332 : Covered terminalDivisors 10891701775332 :=
  ascend (q:=4892517) (@move26) (by decide +kernel) (cons ⟨by decide +kernel, node468343176339276⟩ (cons ⟨by decide +kernel, node241675970692841748⟩ nil))
private theorem node2068552382652 : Covered terminalDivisors 2068552382652 :=
  ascend (q:=3418801) (@move23) (by decide +kernel) (cons ⟨by decide +kernel, node29801634176867364⟩ nil)
private theorem node295507483236 : Covered terminalDivisors 295507483236 :=
  ascend (q:=10256403) (@move15) (by decide +kernel) (cons ⟨by decide +kernel, node2068552382652⟩ (cons ⟨by decide +kernel, node405731774483028⟩ nil))
private theorem node42215354748 : Covered terminalDivisors 42215354748 :=
  ascend (q:=5547) (@move32) (by decide +kernel) (cons ⟨by decide +kernel, node295507483236⟩ (cons ⟨by decide +kernel, node355833225170892⟩ nil))
private theorem node35346349332 : Covered terminalDivisors 35346349332 :=
  ascend (q:=1806) (@move33) (by decide +kernel) (cons ⟨by decide +kernel, node383048387710884⟩ nil)
private theorem node6030764964 : Covered terminalDivisors 6030764964 :=
  ascend (q:=1849) (@move29) (by decide +kernel) (cons ⟨by decide +kernel, node42215354748⟩ (cons ⟨by decide +kernel, node65355399914868⟩ nil))
private theorem node140250348 : Covered terminalDivisors 140250348 :=
  ascend (q:=1764) (@move22) (by decide +kernel) (cons ⟨by decide +kernel, node6030764964⟩ (cons ⟨by decide +kernel, node10891701775332⟩ nil))
private theorem node3261636 : Covered terminalDivisors 3261636 :=
  ascend (q:=49) (@move20) (by decide +kernel) (cons ⟨by decide +kernel, node140250348⟩ (cons ⟨by decide +kernel, node35346349332⟩ nil))

theorem covered {n : ℕ} (h : Exceptional n) : ∃ d ∈ terminalDivisors, d ∣ n :=
  node3261636 h (sylvester_divisor h)
theorem terminal_floor : ∀ d ∈ terminalDivisors, 1055200883739222832492361203044 ≤ d := by decide +kernel
theorem exceptional_lower {n : ℕ} (h : Exceptional n) : 1055200883739222832492361203044 ≤ n := by
  obtain ⟨d,mem,div⟩ := covered h
  exact (terminal_floor d mem).trans (Nat.le_of_dvd h.1 div)
theorem bounded {n : ℕ} (h : 0 < n) (limit : n < 1055200883739222832492361203044) :
    ∃ m, m ≠ n ∧ m ≤ 2*n ∧ m.totient = n.totient := witness_below h limit exceptional_lower

end Noe30

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

namespace Noe30

/-- A uniform count, at every scale, for a set of failures of Noe's bound. -/
theorem exceptional_count {N : ℕ} (S : Finset ℕ)
    (fail : ∀ x ∈ S, Noe.Exceptional x ∧ x ≤ N) :
    S.card ≤ 61 * (N / 1055200883739222832492361203044) := by
  have bound := TotientDensity.count_covered (N:=N) (B:=1055200883739222832492361203044) terminalDivisors.toFinset S
    (by decide) (fun x hx => ⟨(fail x hx).1.1,(fail x hx).2⟩)
    (fun x hx => by simpa only [List.mem_toFinset] using covered (fail x hx).1)
    (fun d hd => terminal_floor d (List.mem_toFinset.mp hd))
  have length : terminalDivisors.toFinset.card = 61 := by decide +kernel
  rwa [length] at bound

end Noe30
