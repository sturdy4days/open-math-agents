import Lead

/-!
# Finite sums of returns for polynomial binary digit weights

The one-step recurrence is due to @connoranderson, PR #28795 on OEIS A230496.
Its module and exact commit are documented in README.md.
-/

/-!
A finite-pattern recurrence principle gives one infinite sequence all of whose
finite sums are returns. Increasing each new term beyond the total of the older
terms lets each finite set of indices represent a different sum.
-/

namespace OMA.FiniteSums

private structure Stage (good : ℕ → Prop) where
  values : Finset ℕ
  valid : ∀ b ∈ values, good b

/-- Turn simultaneous returns of every finite set of good shifts into an
infinite sequence with every finite subsum good and superincreasing terms. -/
theorem exists_sequence (good : ℕ → Prop) (hz : good 0)
    (extend : ∀ (s : Finset ℕ) (L : ℕ), (∀ b ∈ s, good b) →
      ∃ t : ℕ, L < t ∧ ∀ b ∈ s, good (b+t)) :
    ∃ u : ℕ → ℕ, (∀ n, (∑ j ∈ Finset.range n, u j) < u n) ∧
      ∀ F : Finset ℕ, good (∑ j ∈ F, u j) := by
  classical
  let gain (s : Stage good) := (extend s.values (s.values.sup id) s.valid).choose
  have spec (s : Stage good) : s.values.sup id < gain s ∧
      ∀ b ∈ s.values, good (b + gain s) := (extend _ _ s.valid).choose_spec
  let next (s : Stage good) : Stage good := {
    values := s.values ∪ s.values.image (· + gain s)
    valid := by
      intro x hx
      obtain hx | hx := Finset.mem_union.mp hx
      · exact s.valid _ hx
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        exact (spec s).2 b hb }
  let init : Stage good := ⟨{0}, by simpa using hz⟩
  let stages (n : ℕ) : Stage good := Nat.rec init (fun _ => next) n
  let u (n : ℕ) := gain (stages n)
  have mem (n : ℕ) (F : Finset ℕ) (hF : F ⊆ Finset.range n) :
      ∑ j ∈ F, u j ∈ (stages n).values := by
    induction n generalizing F with
    | zero =>
      have hf : F = ∅ := by simpa using hF
      simp [hf, stages, init]
    | succ n ih =>
      change _ ∈ (stages n).values ∪ (stages n).values.image (· + u n)
      by_cases hn : n ∈ F
      · have hsub : F.erase n ⊆ Finset.range n := by
          intro j hj
          have hl := Finset.mem_range.mp (hF (Finset.mem_of_mem_erase hj))
          have hne := (Finset.mem_erase.mp hj).1
          exact Finset.mem_range.mpr (by omega)
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨_, ih _ hsub, Finset.sum_erase_add _ _ hn⟩
      · apply Finset.mem_union_left
        apply ih F
        intro j hj
        have hl := Finset.mem_range.mp (hF hj)
        have hne : j ≠ n := fun h => hn (h ▸ hj)
        exact Finset.mem_range.mpr (by omega)
  refine ⟨u, ?_, ?_⟩
  · intro n
    exact lt_of_le_of_lt (Finset.le_sup (f := id) (mem n (Finset.range n) fun _ h => h)) (spec _).1
  · intro F
    apply (stages (F.sup id+1)).valid
    apply mem (F.sup id + 1) F
    intro j hj
    have hle : j ≤ F.sup id := Finset.le_sup (f := id) hj
    exact Finset.mem_range.mpr (by omega)

end OMA.FiniteSums

namespace OMA.FiniteSums

/-- Superincreasing sequences assign different sums to different finite index sets. -/
theorem subsum_injective (u : ℕ → ℕ) (hu : ∀ n, (∑ j ∈ Finset.range n, u j) < u n) :
    Function.Injective (fun F : Finset ℕ => ∑ j ∈ F, u j) := by
  have bounded (n : ℕ) (F G : Finset ℕ) (hF : F ⊆ Finset.range n) (hG : G ⊆ Finset.range n)
      (he : ∑ j ∈ F, u j = ∑ j ∈ G, u j) : F = G := by
    induction n generalizing F G with
    | zero =>
      have hf : F = ∅ := by simpa using hF
      have hg : G = ∅ := by simpa using hG
      exact hf.trans hg.symm
    | succ n ih =>
      have erase_sub (S : Finset ℕ) (h : S ⊆ Finset.range (n+1)) : S.erase n ⊆ Finset.range n := by
        intro j hj
        have hle := Finset.mem_range.mp (h (Finset.mem_of_mem_erase hj))
        have hne := (Finset.mem_erase.mp hj).1
        exact Finset.mem_range.mpr (by omega)
      have detect (S : Finset ℕ) (h : S ⊆ Finset.range (n+1)) : n ∈ S ↔ u n ≤ ∑ j ∈ S, u j := by
        constructor
        · exact fun hn => Finset.single_le_sum (f := u) (fun _ _ => Nat.zero_le _) hn
        · contrapose!
          intro hn
          have hsub := erase_sub S h
          rw [Finset.erase_eq_of_notMem hn] at hsub
          exact (Finset.sum_le_sum_of_subset hsub).trans_lt (hu n)
      have hn : n ∈ F ↔ n ∈ G := (detect F hF).trans (he ▸ (detect G hG).symm)
      by_cases hf : n ∈ F
      · have hg := hn.mp hf
        have eqf := Finset.sum_erase_add F u hf
        have eqg := Finset.sum_erase_add G u hg
        have eqs := ih _ _ (erase_sub F hF) (erase_sub G hG) (by omega)
        rw [← Finset.insert_erase hf, eqs, Finset.insert_erase hg]
      · have hg : n ∉ G := fun h => hf (hn.mpr h)
        refine ih _ _ ?_ ?_ he
        · simpa [Finset.erase_eq_of_notMem hf] using erase_sub F hF
        · simpa [Finset.erase_eq_of_notMem hg] using erase_sub G hG
  intro F G he
  let n := max (F.sup id) (G.sup id) + 1
  apply bounded n F G _ _ he
  · intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.le_sup (f := id) hx).trans (le_max_left _ _)))
  · intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.le_sup (f := id) hx).trans (le_max_right _ _)))

end OMA.FiniteSums

namespace OMA.OdiousIP

/-- Each pattern of binary digit-weight residues contains all finite sums of a
superincreasing sequence of shifts, within any given progression through its seed. -/
theorem polynomial_ip_returns {ι : Type*} [Fintype ι] (P : ι → Polynomial ℕ)
    (d q H : ℕ) (hq : 0 < q) (hH : 0 < H) :
    ∃ u : ℕ → ℕ, (∀ n, (∑ j ∈ Finset.range n, u j) < u n) ∧
      ∀ F : Finset ℕ, q ∣ ∑ j ∈ F, u j ∧ ∀ v : ι,
        (Nat.digits 2 ((P v).eval (d + ∑ j ∈ F, u j))).count 1 % H =
          (Nat.digits 2 ((P v).eval d)).count 1 % H := by
  classical
  let good (b : ℕ) := q ∣ b ∧ ∀ v : ι,
    (Nat.digits 2 ((P v).eval (d + b))).count 1 % H =
      (Nat.digits 2 ((P v).eval d)).count 1 % H
  apply OMA.FiniteSums.exists_sequence good (by simp [good])
  intro s L hs
  let poly (v : ι × ↥s) := (P v.1).comp (Polynomial.X + Polynomial.C v.2.val)
  obtain ⟨x, large, cong, same⟩ :=
    Odious230.polynomial_weight_recurrence poly d q (d+L) H hq hH
  have order : d ≤ x := by omega
  have div : q ∣ x - d := (Nat.modEq_iff_dvd' order).mp cong.symm
  refine ⟨x-d, by omega, ?_⟩
  intro b hb
  refine ⟨dvd_add (hs b hb).1 div, ?_⟩
  intro v
  have h := same (v, ⟨b,hb⟩)
  simp [poly, Polynomial.eval_comp, add_comm] at h
  rw [show d + (b + (x-d)) = x+b by omega]
  exact h.trans (by simpa [add_comm] using (hs b hb).2 v)

end OMA.OdiousIP

/-! A translated set of finite sums giving distinct odd witnesses to A230496. -/

namespace OMA.OdiousIP

/-- For a fixed power cutoff one sequence gives an odd witness for every
nonempty finite set of indices, and these witnesses are all distinct. -/
theorem odious_family (n : ℕ) :
    ∃ a : ℕ → ℕ, Function.Injective (fun F : Finset ℕ => 1 + ∑ j ∈ F, a j) ∧
      ∀ F : Finset ℕ, F.Nonempty →
        1 < 1 + ∑ j ∈ F, a j ∧ Odd (1 + ∑ j ∈ F, a j) ∧
          ∀ i ≤ n, Odd ((Nat.digits 2 ((1 + ∑ j ∈ F, a j) ^ i)).count 1) := by
  let P (j : Fin (n+1)) : Polynomial ℕ := Polynomial.X ^ j.val
  obtain ⟨a, hg, hr⟩ := polynomial_ip_returns P 1 2 2 (by decide) (by decide)
  refine ⟨a, fun F G he => OMA.FiniteSums.subsum_injective a hg (Nat.add_left_cancel he), ?_⟩
  intro F hF
  obtain ⟨j, hj⟩ := hF
  have hpos : 0 < ∑ i ∈ F, a i := lt_of_lt_of_le ((Nat.zero_le _).trans_lt (hg j))
    (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) hj)
  obtain ⟨hdiv, hp⟩ := hr F
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.odd_iff]
    omega
  · intro i hi
    have h := hp (⟨i, by omega⟩ : Fin (n+1))
    rw [Nat.odd_iff]
    simpa [P] using h

end OMA.OdiousIP
