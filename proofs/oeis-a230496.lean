import OMAStatements.S_oeis_a230496

/-!
# Odd integers whose first powers all have odd binary digit sum

Vladimir Shevelev and Peter J. C. Moses posed the conjecture in OEIS A230496
(2013). @niclorusso formalized its statement in open-math-agents PR #7262.
@connoranderson and @sturdy4days independently proposed the separated-power
construction on the project desk (notes #130443 and #130464). This proof and
its auxiliary lemmas were implemented by @sturdy4days as checker.
-/

namespace OMA.BinaryBlocks

/-- Appending a binary block above all digits of `lo` adds its number of ones. -/
theorem count_append {lo hi offset : ℕ} (h : lo < 2 ^ offset) :
    (Nat.digits 2 (lo + hi * 2 ^ offset)).count 1 =
      (Nat.digits 2 lo).count 1 + (Nat.digits 2 hi).count 1 := by
  by_cases hz : hi = 0
  · simp [hz]
  have hlen := (Nat.digits_length_le_iff (b := 2) (by decide) lo).mpr h
  have hcat := Nat.digits_append_zeroes_append_digits (b := 2) (n := lo)
    (k := offset - (Nat.digits 2 lo).length) (by decide) (Nat.pos_of_ne_zero hz)
  rw [Nat.add_sub_of_le hlen, Nat.mul_comm _ hi] at hcat
  rw [← hcat]
  simp [List.count_replicate]

/-- A sum of disjoint blocks fits below the next block and has additive binary weight. -/
theorem sum_blocks {ι : Type*} (s : Finset ι) (e w : ι → ℕ)
    (he : Function.Injective e) (B : ℕ) (hw : ∀ i, w i < 2 ^ B) :
    (∀ k, (∀ i ∈ s, e i < k) → (∑ i ∈ s, w i * 2 ^ (B * e i)) < 2 ^ (B * k)) ∧
      (Nat.digits 2 (∑ i ∈ s, w i * 2 ^ (B * e i))).count 1 =
        ∑ i ∈ s, (Nat.digits 2 (w i)).count 1 := by
  classical
  induction s using Finset.induction_on_max_value e with
  | empty => simp
  | insert a s ha hmax ih =>
    obtain ⟨hb, hcount⟩ := ih
    have hlt (i) (hi : i ∈ s) : e i < e a :=
      lt_of_le_of_ne (hmax i hi) (fun eq => ha (he eq ▸ hi))
    have hlow := hb (e a) hlt
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    constructor
    · intro k hk
      have hak := hk a (Finset.mem_insert_self _ _)
      calc
        w a * 2 ^ (B * e a) + ∑ i ∈ s, w i * 2 ^ (B * e i)
          < (w a + 1) * 2 ^ (B * e a) := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ 2 ^ B * 2 ^ (B * e a) := Nat.mul_le_mul_right _ (hw a)
        _ = 2 ^ (B * (e a + 1)) := by rw [← pow_add]; congr 1; ring
        _ ≤ 2 ^ (B * k) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hak)
    · rw [Nat.add_comm (w a * _), count_append hlow, hcount, add_comm]

/-- Total number of one digits in blocks at arbitrary distinct indexed positions. -/
theorem count_separated {ι : Type*} [Fintype ι] (e w : ι → ℕ)
    (he : Function.Injective e) (B : ℕ) (hw : ∀ i, w i < 2 ^ B) :
    (Nat.digits 2 (∑ i, w i * 2 ^ (B * e i))).count 1 =
      ∑ i, (Nat.digits 2 (w i)).count 1 :=
  (sum_blocks Finset.univ e w he B hw).2

end OMA.BinaryBlocks

namespace OMA.BinaryBlocks

/-- Natural place value as the ordinary bounded-length expansion. -/
theorem sum_places_eq {q : ℕ} (D : ℕ) (f : Fin q → ℕ) :
    Nat.ofDigits D (List.ofFn f) = ∑ j, f j * D ^ j.val := by
  rw [Nat.ofDigits_eq_sum_mapIdx, ← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Bounded digits in a fixed number of positions are uniquely recoverable. -/
theorem places_injective {D q : ℕ} (hD : 2 ≤ D) (f g : Fin q → ℕ)
    (hf : ∀ i, f i < D) (hg : ∀ i, g i < D)
    (h : (∑ i, f i * D ^ i.val) = ∑ i, g i * D ^ i.val) : f = g := by
  apply List.ofFn_injective
  apply Nat.injOn_ofDigits hD q
  · exact ⟨by simp, by simpa using hf⟩
  · exact ⟨by simp, by simpa using hg⟩
  · simpa only [sum_places_eq] using h

/-- The same uniqueness in a finite alphabet indexed by an arbitrary equivalence. -/
theorem places_injective_of_equiv {ι : Type*} [Fintype ι] {D q : ℕ}
    (e : ι ≃ Fin q) (hD : 2 ≤ D) (f g : ι → ℕ)
    (hf : ∀ i, f i < D) (hg : ∀ i, g i < D)
    (h : (∑ i, f i * D ^ (e i).val) = ∑ i, g i * D ^ (e i).val) : f = g := by
  have cv (u : ι → ℕ) : (∑ j : Fin q, u (e.symm j) * D ^ j.val) =
      ∑ k, u k * D ^ (e k).val := by
    simpa using e.symm.sum_comp (fun k => u k * D ^ (e k).val)
  have hfg := places_injective hD (fun j => f (e.symm j)) (fun j => g (e.symm j))
    (fun j => hf _) (fun j => hg _) (by rw [cv, cv, h])
  funext i
  simpa using congrFun hfg (e i)

end OMA.BinaryBlocks

open Finset MulAction

namespace OdiousPowers

/-- Counting binary digits with weights invariant under a finite 2-group. -/
theorem weighted_parity {G X : Type*} [Group G] (hg : IsPGroup 2 G) [Fintype X]
    [MulAction G X] (w : X → ℕ) (inv : ∀ (g : G) (x : X), w (g • x) = w x)
    (a : X) (fa : ∀ g : G, g • a = a) (wa : w a = 1)
    (uniq : ∀ x : X, (∀ g : G, g • x = x) → x = a) : Odd (∑ x, w x) := by
  classical
  let T := Σ x : X, Fin (w x)
  let _ : MulAction G T := {
    smul := fun g z => ⟨g • z.1, ⟨z.2.val, (inv g z.1).symm ▸ z.2.isLt⟩⟩
    one_smul := fun z => by
      apply Sigma.ext (one_smul G z.1)
      exact (Fin.heq_ext_iff (congrArg w (one_smul G z.1))).mpr rfl
    mul_smul := fun g h z => by
      apply Sigma.ext (mul_smul g h z.1)
      exact (Fin.heq_ext_iff (congrArg w (mul_smul g h z.1))).mpr rfl }
  let z : T := ⟨a, ⟨0, by omega⟩⟩
  have zfix : z ∈ fixedPoints G T := by
    intro g
    apply Sigma.ext (fa g)
    exact (Fin.heq_ext_iff (congrArg w (fa g))).mpr rfl
  have sub : Subsingleton (fixedPoints G T) := by
    refine ⟨fun u v => ?_⟩
    have only : ∀ t : fixedPoints G T, t.val = z := by
      intro t
      have h : t.val.1 = a := uniq _ fun g => congrArg Sigma.fst (t.property g)
      apply Sigma.ext h
      apply (Fin.heq_ext_iff (congrArg w h)).mpr
      have lim := t.val.2.isLt
      have ww := (congrArg w h).trans wa
      change t.val.2.val = 0
      omega
    exact Subtype.ext ((only u).trans (only v).symm)
  let _ := sub
  let _ : Nonempty (fixedPoints G T) := ⟨⟨z,zfix⟩⟩
  have h := hg.card_modEq_card_fixedPoints T
  rw [Nat.card_unique (α := fixedPoints G T), Nat.card_eq_fintype_card] at h
  have c : Fintype.card T = ∑ x, w x := by simp [T, Fintype.card_sigma]
  rw [c] at h
  simpa [Nat.odd_iff, Nat.ModEq] using h

end OdiousPowers

open Finset
namespace OdiousPowers

theorem profile_parity {G : Type*} [Group G] [Fintype G] [DecidableEq G] (hg : IsPGroup 2 G)
    (i : ℕ) (hi : i < Fintype.card G) :
    Odd (∑ x ∈ piAntidiag (univ : Finset (Option G)) i,
      (Nat.digits 2 (Nat.multinomial univ x)).count 1) := by
  classical
  let X := ↥(piAntidiag (univ : Finset (Option G)) i)
  let tr (g : G) := (Equiv.mulLeft g⁻¹).optionCongr
  have total (x : X) : ∑ j, x.val j = i := (mem_piAntidiag.mp x.property).1
  let _ : MulAction G X := {
    smul := fun g x => ⟨fun j => x.val (tr g j), mem_piAntidiag.mpr
      ⟨((tr g).sum_comp x.val).trans (total x), by simp⟩⟩
    one_smul := fun x => by
      apply Subtype.ext
      funext j
      change x.val (tr 1 j) = x.val j
      cases j <;> simp [tr]
    mul_smul := fun g h x => by
      apply Subtype.ext
      funext j
      change x.val (tr (g*h) j) = x.val (tr h (tr g j))
      cases j <;> simp [tr, mul_assoc] }
  let unit : X := ⟨Pi.single none i, by simp [mem_piAntidiag]⟩
  have equivariance (g : G) (x : X) :
      Nat.multinomial univ (g • x).val = Nat.multinomial univ x.val := by
    unfold Nat.multinomial
    change (∑ j, x.val (tr g j)).factorial / (∏ j, (x.val (tr g j)).factorial) = _
    rw [(tr g).sum_comp, (tr g).prod_comp (fun j => (x.val j).factorial)]
  have fixed_unit (g : G) : g • unit = unit := by
    apply Subtype.ext
    funext j
    change (Pi.single none i : Option G → ℕ) (tr g j) = (Pi.single none i : Option G → ℕ) j
    cases j <;> simp [tr]
  have only (x : X) (fixed : ∀ g : G, g • x = x) : x = unit := by
    have same (j : G) : x.val (some j) = x.val (some 1) := by
      have z := congrArg (fun z : X => z.val (some j)) (fixed j)
      change x.val (some (j⁻¹ * j)) = x.val (some j) at z
      simpa using z.symm
    have t := total x
    rw [Fintype.sum_option] at t
    simp_rw [same] at t
    simp only [sum_const, card_univ, smul_eq_mul] at t
    have zero : x.val (some 1) = 0 := by
      by_contra! hz
      have h := Nat.le_mul_of_pos_right (Fintype.card G) (Nat.pos_of_ne_zero hz)
      omega
    have valnone : x.val none = i := by simpa [zero] using t
    apply Subtype.ext
    funext j
    cases j with
    | none => simpa [unit] using valnone
    | some j => simpa [unit] using (same j).trans zero
  have odd := weighted_parity hg (fun x : X => (Nat.digits 2
      (Nat.multinomial univ x.val)).count 1)
    (fun g x => by rw [equivariance]) unit fixed_unit (by
      change (Nat.digits 2 (Nat.multinomial univ (Pi.single none i))).count 1 = 1
      rw [Nat.multinomial_single]
      decide) only
  change Odd (∑ x ∈ _, _)
  rwa [← Finset.sum_attach (f := fun x => (Nat.digits 2 (Nat.multinomial univ x)).count 1)]

end OdiousPowers

open Finset
namespace OdiousPowers

theorem construct {G : Type*} [Group G] [Fintype G] [DecidableEq G] (hg : IsPGroup 2 G)
    (n : ℕ) (hn : 1 ≤ n) (big : n < Fintype.card G) :
    ∃ k : ℕ, Odd k ∧ 1 < k ∧ ∀ i ≤ n, Odd ((Nat.digits 2 (k ^ i)).count 1) := by
  classical
  let D := n + 1
  let B := n.factorial + 1
  let e := Fintype.equivFin G
  let m : Option G → ℕ := Option.elim' 0 (fun j => D ^ (e j).val)
  let t (j : Option G) : ℕ := 2 ^ (B * m j)
  let k := ∑ j, t j
  have split : k = 1 + ∑ j : G, t (some j) := by simp [k, Fintype.sum_option, t, m]
  have dpos : 0 < D := by dsimp [D]; omega
  have bpos : 0 < B := by dsimp [B]; omega
  have pos (j : G) : 0 < m (some j) := pow_pos dpos _
  have even : Even (∑ j : G, t (some j)) :=
    Finset.even_sum _ fun j _ => even_two.pow_of_ne_zero (Nat.mul_pos bpos (pos j)).ne'
  have large : 0 < ∑ j : G, t (some j) := by
    apply lt_of_lt_of_le (pow_pos (by decide : 0 < 2) (B * m (some (1:G))))
    exact single_le_sum (f := fun j : G => t (some j)) (fun _ _ => Nat.zero_le _) (mem_univ (1 : G))
  refine ⟨k, split ▸ odd_one.add_even even, by omega, ?_⟩
  intro i hi
  let s := piAntidiag (univ : Finset (Option G)) i
  let E (x : ↥s) := ∑ j : G, x.val (some j) * D ^ (e j).val
  let W (x : ↥s) := Nat.multinomial univ x.val
  have total (x : ↥s) : ∑ j, x.val j = i := (mem_piAntidiag.mp x.property).1
  have bound (x : ↥s) (v : Option G) : x.val v < D := by
    have z := single_le_sum (s := (univ : Finset (Option G))) (f := x.val)
      (fun _ _ => Nat.zero_le _) (mem_univ v)
    rw [total] at z
    dsimp [D]
    omega
  have inj : Function.Injective E := by
    intro x y h
    have same := OMA.BinaryBlocks.places_injective_of_equiv e
      (by dsimp [D]; omega : 2 ≤ D) (fun j => x.val (some j)) (fun j => y.val (some j))
      (fun j => bound x _) (fun j => bound y _) h
    have other : x.val none = y.val none := by
      have u := total x
      have v := total y
      rw [Fintype.sum_option] at u v
      rw [same] at u
      omega
    apply Subtype.ext
    funext a
    cases a with
    | none => exact other
    | some a => exact congrFun same a
  have width (x : ↥s) : W x < 2 ^ B := by
    have h := Nat.div_le_self (∑ j, x.val j).factorial (∏ j, (x.val j).factorial)
    rw [total] at h
    unfold W Nat.multinomial
    rw [total]
    exact lt_of_le_of_lt (h.trans (Nat.factorial_le hi))
      (lt_trans (by dsimp [B]; omega : n.factorial < B) B.lt_two_pow_self)
  have value (x : ↥s) : ∏ a, t a ^ x.val a = 2 ^ (B * E x) := by
    simp only [t, ← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Fintype.sum_option, m, E, Finset.mul_sum, mul_comm, mul_left_comm]
  have expand : k ^ i = ∑ x : ↥s, W x * 2 ^ (B * E x) := by
    change (∑ j, t j) ^ i = _
    rw [sum_pow_eq_sum_piAntidiag]
    change ∑ x ∈ s, _ = _
    rw [← Finset.sum_attach s]
    apply sum_congr rfl
    intro x _
    rw [value x]
    rfl
  rw [expand, OMA.BinaryBlocks.count_separated E W inj B width]
  have pp := profile_parity hg i (lt_of_le_of_lt hi big)
  rwa [← Finset.sum_attach (f := fun x => (Nat.digits 2 (Nat.multinomial univ x)).count 1)] at pp

end OdiousPowers

/-- Shevelev and Moses's odious-power conjecture, using cyclic symmetry of
the separated binary blocks in the multinomial expansion. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a230496.main := by
  classical
  intro n hn
  let G := Multiplicative (ZMod (2 ^ n))
  have c : Fintype.card G = 2 ^ n := by
    exact (Fintype.card_congr (Multiplicative.toAdd : G ≃ ZMod (2 ^ n))).trans (ZMod.card _)
  have hG : IsPGroup 2 G := IsPGroup.of_card ((Nat.card_eq_fintype_card (α := G)).trans c)
  obtain ⟨k, odd, large, ok⟩ := OdiousPowers.construct hG n hn (by rw [c]; exact n.lt_two_pow_self)
  exact ⟨k, odd, large, fun i _ lim => ok i lim⟩
