import LocalObstruction

/-!
# Numerical and prime-power cases of the two-preimage totient conjecture

The supporting LocalObstruction module is published in the same directory.
Every numerical substitution and terminal branch is verified by the Lean kernel.
-/


namespace TotientLocal

/-- If two distinct odd primes divide a power of two times a prime power,
they must both equal the odd prime, an impossibility. -/
private theorem exclude_prime_pair {q r p a b : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hp : p.Prime) (nq : q ≠ 2) (nr : r ≠ 2) (diff : q ≠ r)
    (dq : q ∣ 2^a*p^b) (dr : r ∣ 2^a*p^b) : False := by
  have unique {s : ℕ} (hs : s.Prime) (ns : s ≠ 2) (d : s ∣ 2^a*p^b) : s = p := by
    rcases hs.dvd_mul.mp d with h | h
    · exact False.elim (ns ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h)))
    · exact (Nat.prime_dvd_prime_iff_eq hs hp).mp (hs.dvd_of_dvd_pow h)
  exact diff ((unique hq nq dq).trans (unique hr nr dr).symm)

/-- The doubling conjecture holds whenever the odd part of the common totient
is a prime power, including the power-of-two case. -/
theorem doubling_for_one_odd_prime {n m p a b : ℕ} (distinct : n ≠ m)
    (same : n.totient = m.totient)
    (covers : ∀ y : ℕ, y.totient = n.totient → y=n ∨ y=m)
    (hp : p.Prime) (form : n.totient = 2^a*p^b) :
    (Odd n ∧ m=2*n) ∨ (Odd m ∧ n=2*m) := by
  apply doubling_outside_three_progressions distinct same covers
  · intro div
    rw [form] at div
    exact exclude_prime_pair (by decide : Nat.Prime 5) (by decide : Nat.Prime 11) hp
      (by decide) (by decide) (by decide) ((by decide : 5 ∣ 8800).trans div)
      ((by decide : 11 ∣ 8800).trans div)
  · intro div
    rw [form] at div
    exact exclude_prime_pair (by decide : Nat.Prime 3) (by decide : Nat.Prime 7) hp
      (by decide) (by decide) (by decide) ((by decide : 3 ∣ 78624).trans div)
      ((by decide : 7 ∣ 78624).trans div)
  · intro div
    rw [form] at div
    exact exclude_prime_pair (by decide : Nat.Prime 3) (by decide : Nat.Prime 7) hp
      (by decide) (by decide) (by decide) ((by decide : 3 ∣ 517104).trans div)
      ((by decide : 7 ∣ 517104).trans div)

end TotientLocal


namespace TrillionBound
open TotientLocal

section
set_option maxRecDepth 27000
set_option maxHeartbeats 6000000

private def r0 : Move := ⟨2024, 1936, 1958, [23, 89]⟩
private def r1 : Move := ⟨2116, 1081, 0, [2, 47]⟩
private def r2 : Move := ⟨2420, 2530, 2300, [11, 23]⟩
private def r3 : Move := ⟨5292, 5334, 5418, [43, 127]⟩
private def r4 : Move := ⟨45034, 43076, 44528, [23, 89]⟩
private def r5 : Move := ⟨58564, 58586, 61226, [23, 2663]⟩
private def r6 : Move := ⟨58586, 58564, 61226, [23, 2663]⟩
private def r7 : Move := ⟨61226, 58564, 58586, [23, 2663]⟩
private def r8 : Move := ⟨97900, 96800, 96910, [89, 881]⟩
private def r9 : Move := ⟨133100, 139150, 121010, [11, 23, 12101]⟩
private def r10 : Move := ⟨139150, 133100, 121010, [11, 23, 12101]⟩
private def r11 : Move := ⟨234344, 234256, 236918, [89, 2663]⟩
private def r12 : Move := ⟨298116, 298662, 301938, [79, 547]⟩
private def r13 : Move := ⟨1347478, 1288892, 1346972, [23, 2663]⟩
private def r14 : Move := ⟨1347478, 1346972, 1288892, [23, 2663]⟩
private def r15 : Move := ⟨5214154, 5155568, 5212196, [89, 2663]⟩
private def r16 : Move := ⟨6400900, 3201715, 0, [2, 2531]⟩
private def r17 : Move := ⟨6400900, 6403430, 6540050, [47, 2531]⟩
private def r18 : Move := ⟨12801800, 12806860, 12814450, [1013, 2531]⟩
private def r19 : Move := ⟨23551164, 23253048, 23253594, [79, 42589]⟩
private def r20 : Move := ⟨73211050, 73205000, 73205110, [12101, 665501]⟩
private def r21 : Move := ⟨80874108, 80237304, 80238102, [127, 100549]⟩
private def r22 : Move := ⟨81534726, 81385668, 81386214, [547, 149059]⟩
private def r23 : Move := ⟨82147716, 80237304, 80238102, [43, 100549]⟩
private def r24 : Move := ⟨140819800, 140822330, 140875460, [2531, 55661]⟩
private def r25 : Move := ⟨161064310, 161051000, 161051110, [12101, 1464101]⟩
private def r26 : Move := ⟨191688200, 191707780, 191737150, [3917, 9791]⟩
private def r27 : Move := ⟨294557780, 294441400, 294443930, [2531, 116381]⟩
private def r28 : Move := ⟨300842300, 294441400, 294443930, [47, 116381]⟩
private def r29 : Move := ⟨614764700, 614883610, 601800980, [47, 5171]⟩
private def r30 : Move := ⟨644257240, 644204000, 644204110, [12101, 5856401]⟩
private def r31 : Move := ⟨774508900, 774799850, 774815030, [2531, 2663]⟩
private def r32 : Move := ⟨1549017800, 1549030450, 1549045630, [55661, 122453]⟩
private def r33 : Move := ⟨1820387556, 1820430222, 1680397128, [13, 42667]⟩
private def r34 : Move := ⟨1860541956, 1860843894, 1861102698, [3319, 6163]⟩
private def r35 : Move := ⟨3532351788, 3533003754, 3533072382, [4903, 5419]⟩
private def r36 : Move := ⟨6480271160, 6477710800, 6477713330, [2531, 2560361]⟩
private def r37 : Move := ⟨6484111700, 6477710800, 6477713330, [1013, 2560361]⟩
private def r38 : Move := ⟨30813035148, 30813136494, 30570513372, [127, 304039]⟩
private def r39 : Move := ⟨233303203650, 155535469100, 155535588010, [3, 1308011]⟩
private def r40 : Move := ⟨356414913800, 356274094000, 356274096530, [2531, 140819801]⟩

private def rules : List Move := [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40]
private def goals : List ℕ := [1003020523596, 1003776336200, 1069244741400, 1125009382200, 1159586873172, 1399819221900, 1451099058200, 1993681922100, 3884177996600, 3913255463796, 4125034401400, 5880846077700, 6175138751964, 6187551602100, 7838170887800, 8259870696084, 11466520074828, 13136810304200, 17269381626200, 17319120816564, 19141814339172, 20765532345800, 24306969445668, 24395432055876, 25127251422900, 31148298518700, 38980784306200, 43166840822600, 43418840359400, 58471176459300, 61766346868600, 65128260539100, 82007831529800, 86219879765800, 105036983148900, 122257914414900, 123011747294700, 189681876663400, 219347430195300, 477607243953400, 716410865930100, 902086146827800, 1155406814637900, 1423699373174100, 1848132378776200, 3805853316740748, 5656353284039700, 6723639724074900, 7074432520059300, 9368364393362772, 18865143722966200, 33203333432647400, 82959167737443800, 610326313418880300, 50190277234748153800]
private def nodes : List (ℕ × Move) := [(24200,r2),
  (36300,r2),
  (266200,r9),
  (298116,r12),
  (399300,r9),
  (556600,r0),
  (834900,r10),
  (1910412,r3),
  (2928200,r5),
  (4392300,r5),
  (6122600,r7),
  (9183900,r7),
  (12801800,r18),
  (19202700,r17),
  (23551164,r19),
  (49537400,r8),
  (67348600,r7),
  (82147716,r23),
  (101022900,r7),
  (140819800,r24),
  (163069452,r22),
  (211229700,r17),
  (242622324,r21),
  (902526900,r28),
  (1549017800,r32),
  (1860541956,r34),
  (2323526700,r31),
  (3221286200,r30),
  (3532351788,r35),
  (4408828600,r26),
  (4831929300,r25),
  (7797796600,r11),
  (9927795900,r28),
  (10103124900,r20),
  (11696694900,r6),
  (12968223400,r37),
  (16304483800,r11),
  (24456725700,r14),
  (30813035148,r38),
  (32401355800,r36),
  (42418764300,r29),
  (43642449400,r4),
  (48602033700,r27),
  (89198990244,r33),
  (179349321800,r13),
  (269023982700,r13),
  (356414913800,r40),
  (466606407300,r39),
  (534622370700,r1),
  (562504691100,r16),
  (694003897400,r15)]

private theorem s0 : r0.valid := by decide +kernel
private theorem s1 : r1.valid := by decide +kernel
private theorem s2 : r2.valid := by decide +kernel
private theorem s3 : r3.valid := by decide +kernel
private theorem s4 : r4.valid := by decide +kernel
private theorem s5 : r5.valid := by decide +kernel
private theorem s6 : r6.valid := by decide +kernel
private theorem s7 : r7.valid := by decide +kernel
private theorem s8 : r8.valid := by decide +kernel
private theorem s9 : r9.valid := by decide +kernel
private theorem s10 : r10.valid := by decide +kernel
private theorem s11 : r11.valid := by decide +kernel
private theorem s12 : r12.valid := by decide +kernel
private theorem s13 : r13.valid := by decide +kernel
private theorem s14 : r14.valid := by decide +kernel
private theorem s15 : r15.valid := by decide +kernel
private theorem s16 : r16.valid := by decide +kernel
private theorem s17 : r17.valid := by decide +kernel
private theorem s18 : r18.valid := by decide +kernel
private theorem s19 : r19.valid := by decide +kernel
private theorem s20 : r20.valid := by decide +kernel
private theorem s21 : r21.valid := by decide +kernel
private theorem s22 : r22.valid := by decide +kernel
private theorem s23 : r23.valid := by decide +kernel
private theorem s24 : r24.valid := by decide +kernel
private theorem s25 : r25.valid := by decide +kernel
private theorem s26 : r26.valid := by decide +kernel
private theorem s27 : r27.valid := by decide +kernel
private theorem s28 : r28.valid := by decide +kernel
private theorem s29 : r29.valid := by decide +kernel
private theorem s30 : r30.valid := by decide +kernel
private theorem s31 : r31.valid := by decide +kernel
private theorem s32 : r32.valid := by decide +kernel
private theorem s33 : r33.valid := by decide +kernel
private theorem s34 : r34.valid := by decide +kernel
private theorem s35 : r35.valid := by decide +kernel
private theorem s36 : r36.valid := by decide +kernel
private theorem s37 : r37.valid := by decide +kernel
private theorem s38 : r38.valid := by decide +kernel
private theorem s39 : r39.valid := by decide +kernel
private theorem s40 : r40.valid := by decide +kernel
private theorem sound : ∀ r ∈ rules, r.valid := by
  intro r hr
  simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact s0
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact s5
  · exact s6
  · exact s7
  · exact s8
  · exact s9
  · exact s10
  · exact s11
  · exact s12
  · exact s13
  · exact s14
  · exact s15
  · exact s16
  · exact s17
  · exact s18
  · exact s19
  · exact s20
  · exact s21
  · exact s22
  · exact s23
  · exact s24
  · exact s25
  · exact s26
  · exact s27
  · exact s28
  · exact s29
  · exact s30
  · exact s31
  · exact s32
  · exact s33
  · exact s34
  · exact s35
  · exact s36
  · exact s37
  · exact s38
  · exact s39
  · exact s40
private theorem links : ∀ v ∈ nodes, nodeOK goals (nodes.map Prod.fst) rules v := by decide +kernel

/-- Each member of an exceptional all-even two-element fiber meets this numerical bound. -/
private theorem terminal_divisor {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ y : ℕ, y.totient=n.totient → y=n ∨ y=m)
    {x : ℕ} (hit : x.totient=n.totient) : ∃ g ∈ goals, g ∣ x := by
  have xpos : 0 < x := lt_of_lt_of_le (by decide : 0<24200)
    (TotientLocal.input_lower_bound distinct same hn hm covers hit)
  have E : exceptional x := ⟨n,m,hn,hm,fun y hy => covers y (hy.trans hit)⟩
  have start := Local19.input_divisors distinct same hn hm covers hit
  have entry : ∃ a ∈ nodes.map Prod.fst, a ∣ x := by
    rcases start with h|h|h|h
    · exact ⟨24200,by decide +kernel,h⟩
    · exact ⟨36300,by decide +kernel,h⟩
    · exact ⟨298116,by decide +kernel,h⟩
    · exact ⟨1910412,by decide +kernel,h⟩
  exact climb goals rules nodes sound links xpos E entry

theorem lower_bound {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ y : ℕ, y.totient=n.totient → y=n ∨ y=m) {x : ℕ} (hit : x.totient=n.totient) : 1000000000000 ≤ x := by
  obtain ⟨g,mem,dv⟩ := terminal_divisor distinct same hn hm covers hit
  have xpos : 0 < x := lt_of_lt_of_le (by decide : 0<24200) (TotientLocal.input_lower_bound distinct same hn hm covers hit)
  have enough : goals.all (fun g => decide (1000000000000 ≤ g)) = true := by decide +kernel
  exact (of_decide_eq_true ((List.all_eq_true.mp enough) g mem)).trans (Nat.le_of_dvd xpos dv)

theorem target_lower {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (hn : Even n) (hm : Even m) (covers : ∀ y : ℕ, y.totient=n.totient → y=n ∨ y=m) : 247842848000 ≤ n.totient := by
  obtain ⟨g,mem,dv⟩ := terminal_divisor distinct same hn hm covers (x:=n) rfl
  have enough : goals.all (fun g => decide (247842848000 ≤ fastPhi g)) = true := by decide +kernel
  have le : 247842848000 ≤ g.totient := by simpa only [Nat.totient_eq_div_primeFactors_mul,fastPhi] using (of_decide_eq_true ((List.all_eq_true.mp enough) g mem))
  have npos : 0 < n := lt_of_lt_of_le (by decide : 0<24200) (TotientLocal.input_lower_bound distinct same hn hm covers (x:=n) rfl)
  exact le.trans (Nat.le_of_dvd (Nat.totient_pos.mpr npos) (Nat.totient_dvd_of_dvd dv))

end
end TrillionBound

namespace TrillionBound

/-- Below either certified bound a two-element fiber is an odd integer and its double. -/
theorem doubling_below_bound {n m : ℕ} (distinct : n ≠ m) (same : n.totient = m.totient)
    (covers : ∀ y : ℕ, y.totient = n.totient → y=n ∨ y=m)
    (small : min n m < 1000000000000 ∨ n.totient < 247842848000) :
    (Odd n ∧ m=2*n) ∨ (Odd m ∧ n=2*m) := by
  by_cases on : Odd n
  · rcases covers (2*n) (Nat.totient_two_mul_of_odd on) with e|e
    · obtain ⟨i,hi⟩ := on; omega
    · exact Or.inl ⟨on,e.symm⟩
  by_cases om : Odd m
  · rcases covers (2*m) ((Nat.totient_two_mul_of_odd om).trans same.symm) with e|e
    · exact Or.inr ⟨om,e.symm⟩
    · obtain ⟨i,hi⟩ := om; omega
  have en := Nat.not_odd_iff_even.mp on
  have em := Nat.not_odd_iff_even.mp om
  have a := lower_bound distinct same en em covers (x:=n) rfl
  have b := lower_bound distinct same en em covers (x:=m) same.symm
  have c := target_lower distinct same en em covers
  omega

end TrillionBound
#print axioms TotientLocal.doubling_for_one_odd_prime
#print axioms TrillionBound.lower_bound
#print axioms TrillionBound.target_lower
#print axioms TrillionBound.doubling_below_bound
