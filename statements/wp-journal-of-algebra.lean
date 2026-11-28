import Mathlib

/-!
# Guralnick–Thompson conjecture on composition factors of monodromy groups

Proof: Daniel Frohardt and Kay Magaard, Composition factors of monodromy groups,
Annals of Mathematics 154 (2001), 327–345. https://annals.math.princeton.edu/articles/11017
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Guralnick–Thompson conjecture: for each genus `g`, only
finitely many nonabelian simple groups other than alternating groups occur as composition factors
of monodromy groups of genus-`g` systems (in particular of genus-0 systems).

Conventions (Guralnick–Thompson, J. Algebra 131 (1990)):
* A genus-`g` system of degree `n` is a tuple `x₁, …, x_r` of nonidentity permutations of
  `Fin n` with `x₁ ⋯ x_r = 1`, generating a transitive group `G` (its monodromy group), and
  satisfying the Riemann–Hurwitz formula `∑ ind(xᵢ) = 2(n + g - 1)`, where
  `ind(x) = n - #cycles(x)` (cycles counted with fixed points) equals `∑ (ℓ - 1)` over the
  nontrivial cycle lengths `ℓ` of `x`.
* `S` is a composition factor of `G` iff `S ≅ K/L` for some subnormal `K ≤ G` and normal
  `L ⊴ K` with `K/L` simple (Jordan–Hölder).
* Finitely many isomorphism types of finite groups is the same as a bound on their orders, so
  finiteness is stated as a bound `N(g)` on `|S|`.
-/

namespace OMA.S_wp_journal_of_algebra

/-- `S` is (isomorphic to) a composition factor of `G`. -/
def IsCompositionFactor (S : Type) [Group S] {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∃ (K : Subgroup G) (L : Subgroup K) (_ : L.Normal), K ≤ H ∧ (K.subgroupOf H).IsSubnormal ∧
    IsSimpleGroup (K ⧸ L) ∧ Nonempty ((K ⧸ L) ≃* S)

/-- `ind(x) = n - #cycles(x)`. -/
def ind {n : ℕ} (x : Equiv.Perm (Fin n)) : ℕ := x.cycleType.sum - Multiset.card x.cycleType

/-- `x` is a genus-`g` system of degree `n` (with `r` branch points). -/
def IsGenusSystem (g n r : ℕ) (x : Fin r → Equiv.Perm (Fin n)) : Prop :=
  (∀ i, x i ≠ 1) ∧ (List.ofFn x).prod = 1 ∧
    (∀ a b : Fin n, ∃ σ ∈ Subgroup.closure (Set.range x), σ a = b) ∧
    ∑ i, ind (x i) = 2 * (n + g - 1)

theorem main :
    ∀ g : ℕ, ∃ N : ℕ, ∀ (n r : ℕ) (x : Fin r → Equiv.Perm (Fin n)), IsGenusSystem g n r x →
      ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
        (∃ a b : S, a * b ≠ b * a) → (∀ m : ℕ, IsEmpty (S ≃* alternatingGroup (Fin m))) →
        IsCompositionFactor S (Subgroup.closure (Set.range x)) → Nat.card S ≤ N := by
  sorry

end OMA.S_wp_journal_of_algebra
