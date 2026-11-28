import OMAStatements.S_oeis_a367175

namespace OMA367175
open OMA.S_oeis_a367175

lemma a_eq_sum_divisors_sub (n : ℕ) :
    a n = ((∑ d ∈ n.divisors, d : ℕ) : ℤ) - 2 * ((∑ p ∈ n.primeFactors, p : ℕ) : ℤ) := by
  rw [Nat.primeFactors_eq_to_filter_divisors_prime]
  push_cast
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold a
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d.Prime
  · simp only [if_pos hd]
    ring
  · simp [hd]

lemma a_dvd_sum_divisors_iff (n : ℕ) :
    a n ∣ ((∑ d ∈ n.divisors, d : ℕ) : ℤ) ↔
      a n ∣ 2 * ((∑ p ∈ n.primeFactors, p : ℕ) : ℤ) := by
  have h : ((∑ d ∈ n.divisors, d : ℕ) : ℤ) - a n =
      2 * ((∑ p ∈ n.primeFactors, p : ℕ) : ℤ) := by
    rw [a_eq_sum_divisors_sub]
    ring
  rw [← h, dvd_sub_self_right]

end OMA367175

namespace OMA367175
open OMA.S_oeis_a367175

lemma a_gt_mul_of_composite (p m : ℕ) (hp : p.Prime) (hm : 1 < m) (hmnp : ¬ m.Prime) :
    ((p * m : ℕ) : ℤ) < a (p * m) := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm0
  let C := (p * m).divisors.filter (fun d => ¬ d.Prime)
  let S := ∑ q ∈ m.primeFactors, q
  let P := m.primeFactors.map ⟨(p * ·), fun _ _ h => Nat.mul_left_cancel hp.pos h⟩
  have hS : 2 ≤ S := by
    obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr hm
    exact (Nat.prime_of_mem_primeFactors hq).two_le.trans
      (Finset.single_le_sum (fun d _ => Nat.zero_le d) hq)
  have hS_mul : p + S ≤ p * S := by
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hs2 : (2 : ℤ) ≤ S := by exact_mod_cast hS
    have := mul_nonneg (sub_nonneg.mpr hp2) (sub_nonneg.mpr hs2)
    have hm' : (p : ℤ) + (S : ℤ) ≤ (p : ℤ) * (S : ℤ) := by nlinarith
    exact_mod_cast hm'
  have hS_bound : (∑ q ∈ (p * m).primeFactors, q) ≤ p + S := by
    rw [Nat.primeFactors_mul hp.ne_zero hm0, hp.primeFactors, Finset.singleton_union]
    by_cases h : p ∈ m.primeFactors
    · rw [Finset.insert_eq_of_mem h]
      change S ≤ p + S
      omega
    · rw [Finset.sum_insert h]
  have hP_sum : (∑ d ∈ P, d) = p * S := by
    simp only [P, Finset.sum_map]
    change (∑ q ∈ m.primeFactors, p * q) = p * (∑ q ∈ m.primeFactors, q)
    rw [Finset.mul_sum]
  have hPn : p * m ∉ P := by
    intro h
    obtain ⟨q, hq, heq⟩ := Finset.mem_map.mp h
    change p * q = p * m at heq
    have hqm := Nat.mul_left_cancel hp.pos heq
    exact hmnp (hqm ▸ Nat.prime_of_mem_primeFactors hq)
  have hP1 : 1 ∉ P := by
    intro h
    obtain ⟨q, hq, heq⟩ := Finset.mem_map.mp h
    change p * q = 1 at heq
    have h4 : 4 ≤ p * q := Nat.mul_le_mul hp.two_le (Nat.prime_of_mem_primeFactors hq).two_le
    omega
  have hN1 : 1 ∉ insert (p * m) P := by
    rw [Finset.mem_insert, not_or]
    have hm2 : 2 ≤ m := by omega
    have h4 : 4 ≤ p * m := Nat.mul_le_mul hp.two_le hm2
    exact ⟨by omega, hP1⟩
  have hsub : insert 1 (insert (p * m) P) ⊆ C := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _, hn0⟩, Nat.not_prime_one⟩
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors_self _ hn0, Nat.not_prime_mul hp.ne_one (by omega)⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hd
      change p * q ∈ C
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_primeFactors hq), hn0⟩,
        Nat.not_prime_mul hp.ne_one (Nat.prime_of_mem_primeFactors hq).ne_one⟩
  have hsumC : 1 + (p * m) + p * S ≤ ∑ d ∈ C, d := by
    calc
      _ = ∑ d ∈ insert 1 (insert (p * m) P), d := by
        rw [Finset.sum_insert hN1, Finset.sum_insert hPn, hP_sum]
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => Nat.zero_le d)
  have hσ : ((∑ d ∈ (p * m).divisors, d : ℕ) : ℤ) =
      ((∑ q ∈ (p * m).primeFactors, q : ℕ) : ℤ) + ((∑ d ∈ C, d : ℕ) : ℤ) := by
    rw [Nat.primeFactors_eq_to_filter_divisors_prime, ← Nat.cast_add]
    exact congrArg (fun n : ℕ => (n : ℤ))
      (Finset.sum_filter_add_sum_filter_not (p * m).divisors Nat.Prime (fun d => d)).symm
  have hbig : p * m + (∑ q ∈ (p * m).primeFactors, q) < ∑ d ∈ C, d := by omega
  have hbig' : ((p * m : ℕ) : ℤ) + ((∑ q ∈ (p * m).primeFactors, q : ℕ) : ℤ) <
      ((∑ d ∈ C, d : ℕ) : ℤ) := by exact_mod_cast hbig
  rw [a_eq_sum_divisors_sub, hσ]
  omega

end OMA367175

namespace OMA367175

lemma semiprime_of_dvd (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hd : ((p : ℤ) - 1) * ((q : ℤ) - 1) ∣ 2 * ((p : ℤ) + (q : ℤ))) :
    p * q = 6 ∨ p * q = 14 ∨ p * q = 15 ∨ p * q = 35 := by
  by_cases h2 : p = 2
  · subst p
    norm_num at hd
    have h6 : (q : ℤ) - 1 ∣ 6 := by
      have h := dvd_sub hd (dvd_mul_right ((q : ℤ) - 1) 2)
      rwa [show 2 * (2 + (q : ℤ)) - ((q : ℤ) - 1) * 2 = 6 by ring] at h
    have hq_le : q ≤ 7 := by
      have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 6) h6
      omega
    interval_cases q <;> norm_num at *
  by_cases h3 : p = 3
  · subst p
    have hd' : (2 : ℤ) * ((q : ℤ) - 1) ∣ 2 * (3 + (q : ℤ)) := by
      norm_num at hd ⊢
      exact hd
    have hd'' := (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hd'
    have h4 : (q : ℤ) - 1 ∣ 4 := by
      have h := dvd_sub hd'' (dvd_refl ((q : ℤ) - 1))
      rwa [show 3 + (q : ℤ) - ((q : ℤ) - 1) = 4 by ring] at h
    have hq_le : q ≤ 5 := by
      have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 4) h4
      omega
    interval_cases q <;> norm_num at *
  have hp2 := hp.two_le
  have hp4 : p ≠ 4 := by
    intro h
    subst p
    norm_num at hp
  have hp5 : 5 ≤ p := by omega
  have hq6 : q ≠ 6 := by
    intro h
    subst q
    norm_num at hq
  have hq7 : 7 ≤ q := by omega
  have hbound := Int.le_of_dvd (by positivity : 0 < 2 * ((p : ℤ) + (q : ℤ))) hd
  have hprod : ((p : ℤ) - 3) * ((q : ℤ) - 3) ≤ 8 := by nlinarith
  have hple : p ≤ 5 := by
    have hm := mul_nonneg (by omega : 0 ≤ (p : ℤ) - 3) (by omega : 0 ≤ (q : ℤ) - 7)
    have : (p : ℤ) ≤ 5 := by nlinarith
    omega
  have hqle : q ≤ 7 := by
    have hm := mul_nonneg (by omega : 0 ≤ (p : ℤ) - 5) (by omega : 0 ≤ (q : ℤ) - 3)
    have : (q : ℤ) ≤ 7 := by nlinarith
    omega
  have hp_eq : p = 5 := by omega
  have hq_eq : q = 7 := by omega
  simp [hp_eq, hq_eq]

end OMA367175

namespace A367175Large

open Finset

private def primeSum (n : ℕ) : ℕ := ∑ q ∈ n.primeFactors, q

private theorem primeSum_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primeSum (a * b) ≤ primeSum a + primeSum b := by
  unfold primeSum
  rw [Nat.primeFactors_mul ha hb]
  have h := Finset.sum_union_inter (s₁ := a.primeFactors) (s₂ := b.primeFactors) (f := fun x => x)
  omega

private theorem sum_le_prod_of_two_le (s : Finset ℕ) (hs : ∀ q ∈ s, 2 ≤ q) :
    (∑ q ∈ s, q) ≤ ∏ q ∈ s, q := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha2 := hs a (mem_insert_self _ _)
    have hs2 (x) (hx : x ∈ s) := hs x (mem_insert_of_mem hx)
    rw [sum_insert ha, prod_insert ha]
    by_cases hempty : s = ∅
    · simp [hempty]
    obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr hempty
    have hp : 2 ≤ ∏ x ∈ s, x :=
      (hs2 b hb).trans
        (Nat.le_of_dvd (Finset.prod_pos fun q hq => by have := hs2 q hq; omega)
          (Finset.dvd_prod_of_mem (fun (x : ℕ) => x) hb))
    refine (Nat.add_le_add_left (ih hs2) a).trans ?_
    obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le ha2
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hp
    rw [hi, hj]
    nlinarith [Nat.zero_le (i * j)]

private theorem primeSum_le (n : ℕ) : primeSum n ≤ n := by
  by_cases h : n = 0
  · simp [h, primeSum]
  exact (sum_le_prod_of_two_le _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (Nat.prod_primeFactors_dvd n))

private theorem two_mul_sum_le_mul_mul {a b c : ℕ} (ha : 2 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) :
    2 * (a + b + c) ≤ a * b * c := by
  have hbc : b + c + 2 ≤ b * c := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hb
    have hi : i ≤ i * c := by
      simpa using Nat.mul_le_mul_left i (show 1 ≤ c by omega)
    rw [Nat.add_mul]
    omega
  have hsum := Nat.mul_le_mul_right (b + c) ha
  rw [Nat.mul_assoc]
  calc
    2 * (a + b + c) = 2 * (b + c) + a * 2 := by omega
    _ ≤ a * (b + c) + a * 2 := Nat.add_le_add_right hsum _
    _ = a * (b + c + 2) := (Nat.mul_add a (b + c) 2).symm
    _ ≤ a * (b * c) := Nat.mul_le_mul_left a hbc

private theorem two_mul_primeSum_four_mul {t : ℕ} (ht : 2 ≤ t) :
    2 * primeSum (4 * t) ≤ 4 * t := by
  have h := primeSum_mul_le (by decide : (4 : ℕ) ≠ 0) (show t ≠ 0 by omega)
  have h4 : primeSum 4 = 2 := by
    change primeSum (2 * 2) = 2
    simp [primeSum, Nat.primeFactors_mul (by decide : (2 : ℕ) ≠ 0)
      (by decide : (2 : ℕ) ≠ 0), Nat.prime_two]
  have h' := primeSum_le t
  omega

private theorem two_mul_primeSum_le_mul_mul {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : 2 ≤ c) : 2 * primeSum (a * b * c) ≤ a * b * c := by
  have hsum : primeSum (a * b * c) ≤ a + b + c := by
    have h₁ := primeSum_mul_le (show a * b ≠ 0 by positivity) (show c ≠ 0 by omega)
    have h₂ := primeSum_mul_le (show a ≠ 0 by omega) (show b ≠ 0 by omega)
    have h₃ := primeSum_le a
    have h₄ := primeSum_le b
    have h₅ := primeSum_le c
    omega
  by_cases ha2 : a = 2
  · by_cases hb2 : b = 2
    · simpa [ha2, hb2] using two_mul_primeSum_four_mul hc
    by_cases hc2 : c = 2
    · simpa [ha2, hc2, mul_assoc, mul_left_comm, mul_comm] using two_mul_primeSum_four_mul hb
    exact (Nat.mul_le_mul_left 2 hsum).trans
      (two_mul_sum_le_mul_mul ha (by omega) (by omega))
  by_cases hb2 : b = 2
  · by_cases hc2 : c = 2
    · simpa [hb2, hc2, mul_assoc, mul_left_comm, mul_comm] using two_mul_primeSum_four_mul ha
    have h := two_mul_sum_le_mul_mul hb (show 3 ≤ a by omega) (show 3 ≤ c by omega)
    exact (Nat.mul_le_mul_left 2 hsum).trans
      (by simpa only [add_left_comm, add_assoc, add_comm, mul_left_comm, mul_assoc, mul_comm] using h)
  have h := two_mul_sum_le_mul_mul hc (show 3 ≤ a by omega) (show 3 ≤ b by omega)
  exact (Nat.mul_le_mul_left 2 hsum).trans
    (by simpa only [add_left_comm, add_assoc, add_comm, mul_left_comm, mul_assoc, mul_comm] using h)

private theorem two_mul_primeSum_of_prime_mul_composite (p m : ℕ) (hp : p.Prime)
    (hm : 1 < m) (hnp : ¬ m.Prime) : 2 * primeSum (p * m) ≤ p * m := by
  obtain ⟨q, hqm, hq, hlt⟩ := Nat.exists_dvd_of_not_prime2 (show 2 ≤ m by omega) hnp
  obtain ⟨r, hr⟩ := hqm
  have hr2 : 2 ≤ r := by
    by_contra! h
    interval_cases r <;> simp_all
  rw [hr, ← mul_assoc]
  exact two_mul_primeSum_le_mul_mul hp.two_le hq hr2

theorem not_dvd_two_mul_sum_primeFactors_of_bound (p m : ℕ) (hp : p.Prime) (hm : 1 < m)
    (hnp : ¬ m.Prime) (a : ℤ) (ha : (↑(p * m) : ℤ) < a) :
    ¬ a ∣ 2 * ((∑ q ∈ (p * m).primeFactors, q : ℕ) : ℤ) := by
  have hp_mem : p ∈ (p * m).primeFactors :=
    hp.mem_primeFactors (dvd_mul_right p m) (by have hp_pos := hp.pos; positivity)
  have hsum_pos : 0 < primeSum (p * m) :=
    hp.pos.trans_le (Finset.single_le_sum (fun x _ => Nat.zero_le x) hp_mem)
  have hpos : 0 < 2 * ((∑ q ∈ (p * m).primeFactors, q : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < (2 : ℕ)) hsum_pos
  have hle : 2 * ((∑ q ∈ (p * m).primeFactors, q : ℕ) : ℤ) ≤ (↑(p * m) : ℤ) := by
    exact_mod_cast two_mul_primeSum_of_prime_mul_composite p m hp hm hnp
  intro hdvd
  exact (not_lt_of_ge (Int.le_of_dvd hpos hdvd)) (hle.trans_lt ha)

end A367175Large

namespace A367175Large

open OMA.S_oeis_a367175

theorem not_dvd_of_prime_mul_composite (p m : ℕ) (hp : p.Prime) (hm : 1 < m)
    (hnp : ¬ m.Prime) :
    ¬ (∑ d ∈ (p * m).divisors, if d.Prime then -(d : ℤ) else (d : ℤ)) ∣
      ((∑ d ∈ (p * m).divisors, d : ℕ) : ℤ) := by
  change ¬ a (p * m) ∣ _
  rw [OMA367175.a_dvd_sum_divisors_iff]
  exact not_dvd_two_mul_sum_primeFactors_of_bound p m hp hm hnp (a (p * m))
    (OMA367175.a_gt_mul_of_composite p m hp hm hnp)

end A367175Large


namespace A367175Small

open OMA.S_oeis_a367175 (a)
open scoped Pointwise

abbrev sigma (n : ℕ) : ℤ := ((∑ d ∈ n.divisors, d : ℕ) : ℤ)

private theorem prime_formulas (p : ℕ) (hp : p.Prime) :
    a p = 1 - (p : ℤ) ∧ sigma p = 1 + (p : ℤ) := by
  have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by simpa [eq_comm] using hp.ne_one
  constructor
  · simp [a, hp.divisors, Finset.sum_insert h1, hp, Nat.not_prime_one, sub_eq_add_neg]
  · simp [sigma, hp.divisors, Finset.sum_insert h1]

theorem prime_cases (p : ℕ) (hp : p.Prime) (hd : a p ∣ sigma p) : p = 2 ∨ p = 3 := by
  obtain ⟨ha, hs⟩ := prime_formulas p hp
  rw [ha, hs, show (1 : ℤ) - p = -((p : ℤ) - 1) by ring, neg_dvd] at hd
  have ht : (p : ℤ) - 1 ∣ (2 : ℤ) := by
    rw [show (2 : ℤ) = (1 + (p : ℤ)) - ((p : ℤ) - 1) by ring]
    exact dvd_sub hd (dvd_refl _)
  have hle := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) ht
  have hmin := hp.two_le
  omega

private theorem square_formulas (p : ℕ) (hp : p.Prime) :
    a (p ^ 2) = (p : ℤ) ^ 2 - p + 1 ∧ sigma (p ^ 2) = (p : ℤ) ^ 2 + p + 1 := by
  have hsmall : p < p ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
  have hp1 : p ∉ ({1} : Finset ℕ) := by simpa using hp.ne_one
  have hmin := hp.two_le
  have hs : p ^ 2 ∉ ({p, 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have hnot : ¬ (p ^ 2).Prime := by
    simpa [pow_two] using Nat.not_prime_mul hp.ne_one hp.ne_one
  constructor
  · simp [a, hp.divisors_sq, Finset.sum_insert hs, Finset.sum_insert hp1, hp, hnot, Nat.not_prime_one]
    ring
  · simp [sigma, hp.divisors_sq, Finset.sum_insert hs, Finset.sum_insert hp1]
    ring

theorem square_no_dvd (p : ℕ) (hp : p.Prime) : ¬ a (p ^ 2) ∣ sigma (p ^ 2) := by
  intro hd
  obtain ⟨ha, hs⟩ := square_formulas p hp
  rw [ha, hs] at hd
  have ht : (p : ℤ) ^ 2 - p + 1 ∣ 2 * (p : ℤ) := by
    rw [show 2 * (p : ℤ) = ((p : ℤ) ^ 2 + p + 1) - ((p : ℤ) ^ 2 - p + 1) by ring]
    exact dvd_sub hd (dvd_refl _)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hle := Int.le_of_dvd (by positivity : (0 : ℤ) < 2 * (p : ℤ)) ht
  by_cases hp2 : p = 2
  · subst p
    norm_num at ht
  · have hmin := hp.two_le
    have hp3 : (3 : ℤ) ≤ p := by omega
    nlinarith [sq_nonneg ((p : ℤ) - 3)]

private theorem divisors_two_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (p * q).divisors = {p * q, p, q, 1} := by
  ext d
  rw [Nat.divisors_mul, hp.divisors, hq.divisors]
  simp only [Finset.mem_mul, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, rfl | rfl, y, rfl | rfl, rfl⟩ <;> simp
  · rintro (hd | hd | hd | hd) <;> subst d
    · exact ⟨p, Or.inr rfl, q, Or.inr rfl, rfl⟩
    · exact ⟨p, Or.inr rfl, 1, Or.inl rfl, mul_one _⟩
    · exact ⟨1, Or.inl rfl, q, Or.inr rfl, one_mul _⟩
    · exact ⟨1, Or.inl rfl, 1, Or.inl rfl, one_mul _⟩

private theorem distinct_formulas (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    a (p * q) = ((p : ℤ) - 1) * ((q : ℤ) - 1) ∧
      sigma (p * q) = ((p : ℤ) + 1) * ((q : ℤ) + 1) := by
  have hltp : p < p * q := by
    simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hp.pos
  have hltq : q < p * q := by
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hp.one_lt hq.pos
  have hp1 : p ∉ ({q, 1} : Finset ℕ) := by simp [hpq, hp.ne_one]
  have hq1 : q ∉ ({1} : Finset ℕ) := by simpa using hq.ne_one
  have hpq1 : p * q ∉ ({p, q, 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    have hmin := hp.two_le
    omega
  have hnot := Nat.not_prime_mul hp.ne_one hq.ne_one
  constructor
  · simp [a, divisors_two_primes p q hp hq, Finset.sum_insert hpq1, Finset.sum_insert hp1,
      Finset.sum_insert hq1, hp, hq, hnot, Nat.not_prime_one]
    ring
  · simp [sigma, divisors_two_primes p q hp hq, Finset.sum_insert hpq1, Finset.sum_insert hp1,
      Finset.sum_insert hq1]
    ring

theorem distinct_dvd_diff (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hd : a (p * q) ∣ sigma (p * q)) :
    ((p : ℤ) - 1) * ((q : ℤ) - 1) ∣ 2 * ((p : ℤ) + (q : ℤ)) := by
  obtain ⟨ha, hs⟩ := distinct_formulas p q hp hq hpq
  rw [ha, hs] at hd
  rw [show 2 * ((p : ℤ) + (q : ℤ)) =
    ((p : ℤ) + 1) * ((q : ℤ) + 1) - ((p : ℤ) - 1) * ((q : ℤ) - 1) by ring]
  exact dvd_sub hd (dvd_refl _)

end A367175Small

namespace A367175Small

open OMA.S_oeis_a367175 (a)

private theorem classification
    (large : ∀ p m : ℕ, p.Prime → 1 < m → ¬ m.Prime → ¬ (a (p * m) ∣ sigma (p * m))) :
    type_of% @OMA.S_oeis_a367175.main := by
  intro k hk
  change a k ∣ sigma k ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hd
    by_cases hone : k = 1
    · exact Or.inl hone
    by_cases hkp : k.Prime
    · rcases prime_cases k hkp hd with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hone
    have hm : 1 < m := by
      by_contra! hm
      have hm' : m = 0 ∨ m = 1 := by omega
      rcases hm' with rfl | rfl <;> simp_all
    by_cases hmq : m.Prime
    · right
      right
      right
      rcases lt_trichotomy p m with hpq | heq | hqp
      · exact OMA367175.semiprime_of_dvd p m hp hmq hpq
          (distinct_dvd_diff p m hp hmq hpq.ne hd)
      · subst m
        exact (square_no_dvd p hp (by simpa [pow_two] using hd)).elim
      · rw [Nat.mul_comm p m] at hd ⊢
        exact OMA367175.semiprime_of_dvd m p hmq hp hqp
          (distinct_dvd_diff m p hmq hp hqp.ne hd)
    · exact (large p m hp hm hmq hd).elim
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide +kernel

end A367175Small

theorem OMA.solution : type_of% @OMA.S_oeis_a367175.main := by
  apply A367175Small.classification
  intro p m hp hm hmp
  exact A367175Large.not_dvd_of_prime_mul_composite p m hp hm hmp
