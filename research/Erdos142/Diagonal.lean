import FormalConjectures.ErdosProblems.«142»
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-!
# Exact diagonal bands for interval sets avoiding a long arithmetic progression

The interval decomposition bounds the number of selected points by the interval size
minus the number of disjoint length-`k` blocks. Deleting multiples of a modulus just
below `k` realizes this bound in full diagonal bands. The cutoff uses the product of the
primes up to the block count. At `a*k-1` a hole outside the multiples of `k` forces an
additional hole by packing blocks on both sides. Thus equality at the boundary depends
on the least prime factor of `k`.

These finite identities concern growing progression lengths in Erdős problem 142.
The registered fixed-length asymptotic remains open. The corresponding mixed van der
Waerden numbers were studied by Landman, Robertson and Culver, *Some New Exact van der
Waerden Numbers*, Integers 5(2) (2005), A10, section 3 (arXiv:math/0507019).
-/

namespace Erdos142Diagonal
open Finset

private lemma omitted {k : ℕ} (hk : 2 ≤ k) {S : Finset ℕ} (hf : (S : Set ℕ).IsAPOfLengthFree k)
    (a d : ℕ) (hd : 0 < d) : ∃ i < k, a + i*d ∉ S := by
  by_contra! all
  let T := (range k).image fun i => a+i*d
  have inj : Function.Injective (fun i : ℕ => a+i*d) := by
    intro i j h
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
  have card : T.card = k := by simp [T,card_image_of_injective _ inj]
  have sub : (T : Set ℕ) ⊆ S := by
    rintro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.1 hx
    exact all i (mem_range.1 hi)
  have ap : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a,d,by simp [card],?_⟩
    ext x
    simp [T]
  obtain le : k ≤ 1 := by exact_mod_cast hf _ sub ap
  omega

private theorem packed_holes {k N m : ℕ} (hk : 2 ≤ k) {S : Finset ℕ}
    (hf : (S : Set ℕ).IsAPOfLengthFree k) (b : Fin m → ℕ)
    (inside : ∀ i, 0 < b i ∧ b i+k ≤ N+1)
    (apart : ∀ i j, i < j → b i+k ≤ b j) :
    ∃ F : Finset ℕ, F ⊆ Icc 1 N \ S ∧ F.card=m ∧
      ∀ x∈F, ∃ i, b i ≤ x ∧ x < b i+k := by
  classical
  choose j hj missed using fun i => omitted hk hf (b i) 1 (by decide)
  let f (i : Fin m) := b i + j i
  have strict : StrictMono f := by
    intro i h ih
    have := apart i h ih
    dsimp [f]; have := hj i; omega
  refine ⟨univ.image f, ?_, by simp [card_image_of_injective _ strict.injective], ?_⟩
  · rintro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.1 hx
    refine mem_sdiff.2 ⟨mem_Icc.2 ?_, by simpa [f] using missed i⟩
    have := inside i; have := hj i; dsimp [f]; omega
  · rintro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.1 hx
    refine ⟨i,?_,?_⟩ <;> dsimp [f] <;> have := hj i <;> omega

private theorem extremal_bound {k N B : ℕ} (hk : 2 ≤ k)
    (bound : ∀ S : Finset ℕ, S ⊆ Icc 1 N → (S : Set ℕ).IsAPOfLengthFree k → S.card ≤ B) :
    Erdos142.r k N ≤ B := by
  apply csSup_le
  · refine ⟨0,∅,by simp,?_,rfl⟩
    intro T inc ap
    have eq : T=∅ := Set.subset_empty_iff.mp (by simpa using inc)
    exact ((Set.not_isAPOfLength_empty (show 0 < (k:ℕ∞) by exact_mod_cast (show 0<k by omega))) (eq ▸ ap)).elim
  · rintro _ ⟨S,hs,hf,rfl⟩
    exact bound S hs hf

theorem blocks_upper {k N : ℕ} (hk : 2 ≤ k) :
    Erdos142.r k N ≤ N - N/k := by
  apply extremal_bound hk
  intro S hs hf
  obtain ⟨F,sub,cf,_⟩ := packed_holes (N := N) hk hf (fun i : Fin (N/k) => 1+i.val*k) (by
    intro i; refine ⟨by omega,?_⟩
    have l := (Nat.mul_le_mul_right k (show i.val+1 ≤ N/k from i.isLt)).trans (Nat.div_mul_le_self N k)
    simp only [Nat.add_mul,one_mul] at l
    omega) (by
    intro i j ij
    have l := Nat.mul_le_mul_right k (show i.val+1 ≤ j.val from ij)
    simp only [Nat.add_mul,one_mul] at l
    omega)
  have l := card_le_card sub
  rw [cf,card_sdiff_of_subset hs,Nat.card_Icc] at l
  have := (card_le_card hs).trans_eq (Nat.card_Icc 1 N)
  omega

/-- At the upper end of a block, equality forces the deleted sites to be precisely the
multiples of k. A prime factor of k then supplies an entire surviving progression. -/
theorem strict_boundary {a k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (pk : p ∣ k) (pa : p ≤ a) :
    Erdos142.r k (a*k-1) ≤ a*k-1-a := by
  classical
  apply extremal_bound hk
  intro S hs hf
  obtain ⟨t,ht,miss⟩ := omitted hk hf 1 p hp.pos
  let x := 1+t*p
  have size : x < a*k := by
    dsimp [x]
    have h := Nat.mul_le_mul_right p (show t+1 ≤ k by omega)
    have h' := Nat.mul_le_mul_right k pa
    have := hp.two_le
    nlinarith only [h,h',this]
  have notDiv : ¬ k ∣ x := by
    intro div
    have divp := pk.trans div
    have := (Nat.dvd_add_iff_left (dvd_mul_left p t)).2 divp
    exact hp.not_dvd_one this
  have posRem : 0 < x%k := Nat.pos_of_ne_zero (fun h => notDiv (Nat.dvd_of_mod_eq_zero h))
  let b (i : Fin (a-1)) := if i.val < x/k then 1+i.val*k else (i.val+1)*k
  have hlast : 1 ≤ a*k := Nat.mul_pos (hp.pos.trans_le pa) (by omega)
  have normalize : a*k-1+1=a*k := by omega
  obtain ⟨F,sub,card,inside⟩ := packed_holes (N := a*k-1) hk hf b (by
    intro i
    have i1 : i.val+1 < a := by have := i.isLt; omega
    have le := Nat.mul_le_mul_right k (show i.val+2 ≤ a by omega)
    simp only [Nat.succ_mul] at le
    rw [normalize]; dsimp [b]; split <;> constructor <;> nlinarith) (by
    intro i j ij
    have l := Nat.mul_le_mul_right k (show i.val+1 ≤ j.val from ij)
    dsimp [b]; split <;> split <;> simp only [Nat.add_mul,one_mul] at * <;> omega)
  have notIn : x ∉ F := by
    intro h
    obtain ⟨i,il,iu⟩ := inside x h
    dsimp [b] at il iu
    have splitX := Nat.mod_add_div x k
    have remLT := Nat.mod_lt x (show 0 < k by omega)
    split at il
    · rename_i less
      rw [if_pos less] at iu
      have le := Nat.mul_le_mul_right k (show i.val+1 ≤ x/k from less)
      rw [Nat.add_mul,one_mul, Nat.mul_comm (x/k)] at le
      omega
    · rename_i greater
      have le := Nat.mul_le_mul_right k (show x/k ≤ i.val by omega)
      rw [Nat.mul_comm (x/k)] at le
      rw [Nat.add_mul,one_mul] at il
      omega
  have sub' : insert x F ⊆ Icc 1 (a*k-1) \ S := insert_subset (mem_sdiff.2
    ⟨mem_Icc.2 ⟨by dsimp [x]; omega,by omega⟩,miss⟩) sub
  have l := card_le_card sub'
  rw [card_insert_of_notMem notIn,card,card_sdiff_of_subset hs,Nat.card_Icc] at l
  have bound := (card_le_card hs).trans_eq (Nat.card_Icc 1 (a*k-1))
  have := hp.two_le
  omega

end Erdos142Diagonal

namespace Erdos142Diagonal
open Finset

theorem hits_multiple {s d : ℕ} (hs : 0 < s) (hd : d.Coprime s) (a : ℕ) :
    ∃ i < s, s ∣ a + i * d := by
  let : NeZero s := ⟨hs.ne'⟩
  let u : ZMod s := -(a : ZMod s) * (d : ZMod s)⁻¹
  refine ⟨u.val, u.val_lt, (ZMod.natCast_eq_zero_iff _ _).1 ?_⟩
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, u]
  rw [mul_assoc, mul_comm (d : ZMod s)⁻¹, ZMod.coe_mul_inv_eq_one d hd]
  simp

/-- Deleting positive multiples of a rough modulus hits every allowable common difference. -/
theorem transversals_lower {k N s : ℕ} (hk : 2 ≤ k) (hs : 0 < s) (hsk : s ≤ k)
    (rough : ∀ d : ℕ, 0 < d → (k-1)*d < N → d.Coprime s) :
    N - N / s ≤ Erdos142.r k N := by
  classical
  let I := Icc 1 N
  let S := I.filter fun x => ¬s ∣ x
  have sub : S ⊆ Icc 1 N := filter_subset _ _
  have free : (S : Set ℕ).IsAPOfLengthFree k := by
    rintro T inc ⟨a,d,hcard,ht⟩
    have mem (i : ℕ) (hi : i < k) : a + i*d ∈ S := by
      apply inc
      rw [ht]
      exact ⟨i, by exact_mod_cast hi, rfl⟩
    have a0 : 1 ≤ a := by simpa using (mem_Icc.mp (sub (mem 0 (by omega)))).1
    have last := (mem_Icc.mp (sub (mem (k-1) (by omega)))).2
    by_cases hd : d = 0
    · subst d
      have ts : T = {a} := by
        rw [ht]
        ext x
        simp [show ∃ i : ℕ, i < k from ⟨0, by omega⟩, eq_comm]
      simpa [ts] using hcard.ge
    · obtain ⟨i,hi,hit⟩ := hits_multiple hs (rough d (by omega) (by omega)) a
      exact ((mem_filter.mp (mem i (hi.trans_le hsk))).2 hit).elim
  have count : (I.filter fun x => s ∣ x).card = N/s := by
    rw [← Nat.card_multiples' N s]
    congr 1
    ext x
    simp only [I, mem_filter, mem_Icc, mem_range]
    omega
  have cardS : S.card = N-N/s := by
    have h := card_filter_add_card_filter_not (s := I) (fun x => s ∣ x)
    rw [count, show I.card = N from Nat.card_Icc 1 N] at h
    dsimp [S]
    omega
  rw [← cardS]
  unfold Erdos142.r Set.IsAPOfLengthFree.maxCard
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro _ ⟨U, hU, _, rfl⟩
    exact (card_mono hU).trans_eq (Nat.card_Icc 1 N)
  · exact ⟨S,sub,free,rfl⟩

/-- Every residue in the interior of a diagonal band realizes the disjoint-block bound. -/
theorem primorial_lower {k N h : ℕ} (hk : 2 ≤ k)
    (hi : N+(h+1)*primorial h ≤ (h+1)*k) :
    N-h ≤ Erdos142.r k N := by
  let P := primorial h
  let s := 1 + ((k-1)/P)*P
  have hP : 0 < P := primorial_pos h
  have eqk := Nat.mod_add_div (k-1) P
  have rem := Nat.mod_lt (k-1) hP
  have sk : s ≤ k := by dsimp [s]; rw [Nat.mul_comm ((k-1)/P)]; omega
  have close : k < s + P := by dsimp [s]; rw [Nat.mul_comm ((k-1)/P)]; omega
  have ps : P.Coprime s := (Nat.coprime_add_mul_right_right P 1 ((k-1)/P)).2 (by simp)
  have hN : N < (h+1)*s := by
    change N+(h+1)*P ≤ (h+1)*k at hi
    have z : (h+1)*k < (h+1)*(s+P) := Nat.mul_lt_mul_of_pos_left close (by omega)
    rw [Nat.mul_add] at z
    omega
  have less : N/s ≤ h := by
    have hs : 0 < s := by dsimp [s]; omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hs).2 hN)
  apply (Nat.sub_le_sub_left less N).trans
  apply transversals_lower hk (by dsimp [s]; omega) sk
  intro d hd bound
  have dk : d ≤ h := by
    by_contra! bigger
    have lb := Nat.mul_le_mul_left (k-1) bigger
    have pos : k-1+1=k := by omega
    have upper : N+(h+1) ≤ (h+1)*k := by
      exact le_trans (Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left (h+1) hP) N) hi
    nlinarith [Nat.mul_comm (k-1) (h+1)]
  by_contra notCop
  obtain ⟨p,prime,divd,divs⟩ := Nat.Prime.not_coprime_iff_dvd.1 notCop
  have divP : p ∣ P := prime.dvd_primorial_iff.2 ((Nat.le_of_dvd hd divd).trans dk)
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,prime,divP,divs⟩) ps

end Erdos142Diagonal

namespace Erdos142Diagonal
open Finset

/-- Uniform exact range, including every prime length k and N ≤ k(k-1). -/
theorem exact_below_minFac {k N : ℕ} (hk : 2 ≤ k) (hN : N ≤ (k-1)*k.minFac) :
    Erdos142.r k N = N - N/k := by
  apply le_antisymm (blocks_upper hk)
  apply transversals_lower hk (by omega) le_rfl
  intro d hd bound
  exact (Nat.coprime_of_lt_minFac hd.ne' (Nat.lt_of_mul_lt_mul_left (bound.trans_le hN))).symm

private theorem div_boundary {a k : ℕ} (ha : 1 ≤ a) (hk : 2 ≤ k) :
    (a*k-1)/k = a-1 := by
  have prod : 0 < a*k := Nat.mul_pos ha (by omega)
  have hi : (a*k-1)/k < a := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  have suc : a-1+1 = a := by omega
  have eq := congrArg (· * k) suc
  change (a-1+1)*k = a*k at eq
  rw [Nat.add_mul,one_mul] at eq
  have lo : a-1 ≤ (a*k-1)/k := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  omega

/-- Equality in the partition bound at the endpoint is governed by the least prime factor. -/
theorem boundary_iff {k a : ℕ} (hk : 2 ≤ k) (ha : 0 < a) :
    Erdos142.r k (a*k-1) = (a*k-1)-(a-1) ↔ a < k.minFac := by
  refine ⟨fun eq => ?_,fun small => ?_⟩
  · by_contra! big
    have upper := strict_boundary hk (Nat.minFac_prime (show k≠1 by omega)) (Nat.minFac_dvd k) big
    have l := Nat.mul_le_mul_left a hk
    rw [eq] at upper
    omega
  · have l := Nat.mul_le_mul_right k (show a+1 ≤ k.minFac from small)
    have pk := Nat.minFac_le (show 0<k by omega)
    have kk : k-1+1=k := by omega
    have hN : a*k-1 ≤ (k-1)*k.minFac := by
      have z := congrArg (· * k.minFac) kk
      change (k-1+1)*k.minFac = k*k.minFac at z
      rw [Nat.add_mul,one_mul] at z
      rw [Nat.add_mul,one_mul,Nat.mul_comm k.minFac k] at l
      omega
    rw [exact_below_minFac hk hN,div_boundary ha hk]

/-- A broad quantitative interval in each diagonal band attains the disjoint-block upper bound. -/
theorem diagonal_band {k h N : ℕ} (hk : 2 ≤ k) (lo : h*k ≤ N)
    (hi : N+(h+1)*primorial h ≤ (h+1)*k) :
    Erdos142.r k N = N-h := by
  have hP := primorial_pos h
  have less : N < (h+1)*k := by nlinarith [Nat.mul_pos (show 0<h+1 by omega) hP]
  have dh : N/k = h := by
    have x := (Nat.div_lt_iff_lt_mul (show 0<k by omega)).2 less
    have y := (Nat.le_div_iff_mul_le (show 0<k by omega)).2 lo
    omega
  exact le_antisymm (by simpa only [dh] using (blocks_upper (N := N) hk)) (primorial_lower hk hi)

/-- At the very end of each band, there is an arithmetic correction of exactly zero or one. -/
theorem exact_boundary {k a : ℕ} (hk : 2 ≤ k) (ha : 0<a) (scale : (a+1)*primorial a ≤ k) :
    Erdos142.r k (a*k-1) =
      if a < k.minFac then (a*k-1)-(a-1) else (a*k-1)-a := by
  split
  · exact (boundary_iff hk ha).2 ‹_›
  · have upper := strict_boundary hk (Nat.minFac_prime (show k≠1 by omega)) (Nat.minFac_dvd k)
        (show k.minFac≤a by omega)
    refine le_antisymm upper (primorial_lower hk ?_)
    rw [Nat.add_mul a 1 k,one_mul]
    omega

/-- The same conclusion has an elementary sufficient threshold with no primorial. -/
theorem exact_multiple {k h : ℕ} (hk : 2 ≤ k) (scale : (h+1)*4^h ≤ k) :
    Erdos142.r k (h*k) = h*(k-1) := by
  have cut := (Nat.mul_le_mul_left (h+1) (primorial_le_four_pow h)).trans scale
  have r := diagonal_band hk (N := h*k) (h := h) le_rfl (by rw [Nat.add_mul h 1 k,one_mul]; omega)
  rw [r,Nat.mul_sub,Nat.mul_one]

end Erdos142Diagonal
