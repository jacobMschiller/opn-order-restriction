import Consequences
import Mathlib.NumberTheory.Multiplicity

/-!
# A 3-adic refinement of the largest-prime order bound

The public bounds are implications from `Nat.Perfect`, `Odd`, and the
largest-prime hypotheses. The Euler-prime parameter is a prime divisor
with odd factorization exponent; its existence and uniqueness are proved below.
-/

namespace LargestPrimeOrders

open Finset

noncomputable def highWeight (N P : ℕ) : ℕ :=
  ∑ q ∈ high N P, padicValNat P (component N q)

noncomputable def lowWeight (N P : ℕ) : ℕ :=
  (∑ q ∈ sources N P 3, padicValNat P (component N q)) +
  (∑ q ∈ sources N P 6, padicValNat P (component N q))

def threeAllowance (b t : ℕ) : ℕ := if b < t then 0 else if b = t then 1 else 2

noncomputable def eulerThreeDelta (N e : ℕ) : ℕ :=
  if e % 3 = 2 then padicValNat 3 (e+1) + padicValNat 3 (N.factorization e+1) else 0

lemma geom_three_valuation_one {q n : ℕ} (hq : 1 < q) (hn : 0 < n)
    (hm : q % 3 = 1) : padicValNat 3 (geom q n) = padicValNat 3 n := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hqd : 3 ∣ q-1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hqn : ¬3 ∣ q := by intro h; have := Nat.mod_eq_zero_of_dvd h; omega
  have h := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3)
    (x := q) (y := 1) hq hqd hqn hn.ne'
  simp only [one_pow] at h
  rw [← geom_identity q n hq.le,
    padicValNat.mul (geom_pos q hn).ne' (by omega : q-1 ≠ 0)] at h
  omega

lemma geom_three_valuation_two {q n : ℕ} (hq : 1 < q) (hn : 0 < n)
    (hm : q % 3 = 2) (heven : 2 ∣ n) :
    padicValNat 3 (geom q n) = padicValNat 3 (q+1) + padicValNat 3 n := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨m, rfl⟩ := heven
  have hmpos : 0 < m := by omega
  have hq2 : 1 < q^2 := one_lt_pow₀ hq (by decide)
  have hmod : q^2 % 3 = 1 := by norm_num [Nat.pow_mod, hm]
  have hshort := geom_three_valuation_one hq2 hmpos hmod
  have hg2 : geom q 2 = q+1 := by simp [geom, Finset.sum_range_succ]; omega
  rw [geom_mul, padicValNat.mul (geom_pos q (by decide)).ne'
    (geom_pos (q^2) hmpos).ne', hg2, hshort,
    padicValNat.mul (by decide : (2:ℕ) ≠ 0) hmpos.ne']
  norm_num

lemma three_valuation_balance {N : ℕ} (hN : Nat.Perfect N) :
    (∑ q ∈ N.primeFactors, padicValNat 3 (component N q)) = padicValNat 3 N := by
  have h := valuation_balance hN (by decide : Nat.Prime 3) (by decide : 3 ≠ 2)
  rwa [Nat.factorization_def N (by decide : Nat.Prime 3)] at h

lemma component_three_le {N q : ℕ} (hN : Nat.Perfect N) (hq : q ∈ N.primeFactors) :
    padicValNat 3 (component N q) ≤ padicValNat 3 N := by
  have h := Finset.single_le_sum
    (fun r (_ : r ∈ N.primeFactors) => Nat.zero_le (padicValNat 3 (component N r))) hq
  rwa [three_valuation_balance hN] at h

lemma pair_three_le {N u v : ℕ} (hN : Nat.Perfect N)
    (hu : u ∈ N.primeFactors) (hv : v ∈ N.primeFactors) (hne : u ≠ v) :
    padicValNat 3 (component N u) + padicValNat 3 (component N v) ≤ padicValNat 3 N := by
  have hsub : ({u,v} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have h := Finset.sum_le_sum_of_subset hsub (f := fun q => padicValNat 3 (component N q))
  rwa [Finset.sum_pair hne, three_valuation_balance hN] at h

lemma triple_three_le {N u v w : ℕ} (hN : Nat.Perfect N)
    (hu : u ∈ N.primeFactors) (hv : v ∈ N.primeFactors) (hw : w ∈ N.primeFactors)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    padicValNat 3 (component N u) + padicValNat 3 (component N v) +
      padicValNat 3 (component N w) ≤ padicValNat 3 N := by
  have hsub : ({u,v,w} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h := Finset.sum_le_sum_of_subset hsub (f := fun q => padicValNat 3 (component N q))
  simpa [Finset.sum_insert, huv, huw, hvw, Nat.add_assoc, three_valuation_balance hN] using h

lemma source_prime_mod_three {N P d q : ℕ} (hP : P.Prime)
    (hq : q ∈ sources N P d) (hd : 3 ∣ d) : P % 3 = 1 := by
  letI : Fact P.Prime := ⟨hP⟩
  obtain ⟨hqm, hqP, hqd, _⟩ := mem_sources.mp hq
  have hqn : (q : ZMod P) ≠ 0 := by
    intro h
    have hdiv := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
    have := Nat.le_of_dvd (Nat.prime_of_mem_primeFactors hqm).pos hdiv
    omega
  have hord := ZMod.orderOf_dvd_card_sub_one hqn
  change ord P q ∣ P-1 at hord
  rw [hqd] at hord
  have hmod := Nat.mod_eq_zero_of_dvd (hd.trans hord)
  have := hP.two_le
  omega

lemma low_positive_mod_three {N P : ℕ} (hP : P.Prime) (hL : 0 < lowWeight N P) :
    P % 3 = 1 := by
  classical
  by_cases h3 : sources N P 3 = ∅
  · have h6 : sources N P 6 ≠ ∅ := by
      intro h
      simp [lowWeight, h3, h] at hL
    obtain ⟨q,hq⟩ := Finset.nonempty_iff_ne_empty.mpr h6
    exact source_prime_mod_three hP hq (by decide)
  · obtain ⟨q,hq⟩ := Finset.nonempty_iff_ne_empty.mpr h3
    exact source_prime_mod_three hP hq (by decide)

lemma three_pair_extra_component {N P : ℕ} (hP : P.Prime)
    (hc : 1 < (sources N P 3).card) :
    ∃ q ∈ N.primeFactors, q < P ∧ q % 3 = 1 ∧ 1 ≤ padicValNat 3 (component N q) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨u,hu,v,hv,hne⟩ := Finset.one_lt_card.mp hc
  have hu' := mem_sources.mp hu
  have hv' := mem_sources.mp hv
  have hsum := three_pair_sum hP hu'.2.1 hv'.2.1 hne hu'.2.2.1 hv'.2.2.1
  have hPmod := source_prime_mod_three hP hu (by decide)
  have hunz : u % 3 ≠ 0 := by
    intro hu0
    have hv0 : v % 3 = 0 := by omega
    have hu3 := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3)
      (Nat.prime_of_mem_primeFactors hu'.1)).mp (Nat.dvd_of_mod_eq_zero hu0)
    have hv3 := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3)
      (Nat.prime_of_mem_primeFactors hv'.1)).mp (Nat.dvd_of_mod_eq_zero hv0)
    omega
  have hmods : u % 3 = 1 ∨ v % 3 = 1 := by omega
  have hlocal : ∀ q ∈ sources N P 3, q % 3 = 1 →
      ∃ r ∈ N.primeFactors, r < P ∧ r % 3 = 1 ∧ 1 ≤ padicValNat 3 (component N r) := by
    intro q hq hmod
    obtain ⟨hqm,hqP,hq3,hqd⟩ := mem_sources.mp hq
    have hlen := order_dvd_of_component_dvd hqd
    rw [hq3] at hlen
    have hc : (q : ZMod 3) = 1 := by
      apply (ZMod.natCast_eq_natCast_iff' q 1 3).mpr
      simpa using hmod
    have hgc : (component N q : ZMod 3) = 0 := by
      change (geom q (N.factorization q+1) : ZMod 3) = 0
      rw [geom_cast_of_one hc]
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hlen
    exact ⟨q,hqm,hqP,hmod,one_le_padicValNat_of_dvd (component_pos N q)
      ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hgc)⟩
  rcases hmods with h | h
  · exact hlocal u hu h
  · exact hlocal v hv h

lemma low_two_extra_component {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hL : lowWeight N P = 2) :
    ∃ q ∈ N.primeFactors, q < P ∧ q % 3 = 1 ∧ 1 ≤ padicValNat 3 (component N q) := by
  have hs3 := source_sum_le_card hN hodd hPmem hmax (Or.inl rfl : 3=3 ∨ 3=6)
  have hs6 := source_sum_le_card hN hodd hPmem hmax (Or.inr rfl : 6=3 ∨ 6=6)
  have hc6 := six_sources_card_le_one (P := P) hN hodd
  have hc3 : 1 < (sources N P 3).card := by
    unfold lowWeight at hL
    rcases three_or_six_sources_empty hodd hPmem with h | h
    · simp only [h, Finset.sum_empty] at hL
      omega
    · simp only [h, Finset.sum_empty] at hL
      omega
  exact three_pair_extra_component (Nat.prime_of_mem_primeFactors hPmem) hc3

lemma weight_balance {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P) :
    highWeight N P + lowWeight N P = N.factorization P := by
  have hP2 : P ≠ 2 := by
    intro h
    exact (prime_odd hodd hPmem).not_two_dvd_nat (by simp [h])
  have h := valuation_balance hN (Nat.prime_of_mem_primeFactors hPmem) hP2
  rw [valuation_partition hmax] at h
  simpa [highWeight, lowWeight, Nat.add_assoc] using h

lemma euler_delta_component {N e : ℕ} (hemem : e ∈ N.primeFactors)
    (heodd : Odd (N.factorization e)) (he2 : e % 3 = 2) :
    padicValNat 3 (component N e) = eulerThreeDelta N e := by
  have hlen : 2 ∣ N.factorization e+1 := Nat.dvd_of_mod_eq_zero (by
    have := Nat.odd_iff.mp heodd; omega)
  simpa [component, eulerThreeDelta, he2] using
    geom_three_valuation_two (Nat.prime_of_mem_primeFactors hemem).one_lt (by omega) he2 hlen

lemma low_positive_euler_budget {N P e : ℕ} (hN : Nat.Perfect N)
    (hPmem : P ∈ N.primeFactors) (hemem : e ∈ N.primeFactors)
    (heodd : Odd (N.factorization e)) (hL : 0 < lowWeight N P) :
    padicValNat 3 (N.factorization P+1) + eulerThreeDelta N e ≤ padicValNat 3 N := by
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hPmod := low_positive_mod_three hP hL
  have hPv : padicValNat 3 (component N P) = padicValNat 3 (N.factorization P+1) :=
    geom_three_valuation_one hP.one_lt (by omega) hPmod
  by_cases he2 : e % 3 = 2
  · have hPe : P ≠ e := by intro h; subst e; omega
    have h := pair_three_le hN hPmem hemem hPe
    rwa [hPv, euler_delta_component hemem heodd he2] at h
  · simpa [eulerThreeDelta, he2, hPv] using component_three_le hN hPmem

lemma low_two_euler_budget {N P e : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hemem : e ∈ N.primeFactors) (heodd : Odd (N.factorization e))
    (hL : lowWeight N P = 2) :
    padicValNat 3 (N.factorization P+1) + eulerThreeDelta N e + 1 ≤ padicValNat 3 N := by
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hPmod := low_positive_mod_three (N := N) hP (by omega)
  have hPv : padicValNat 3 (component N P) = padicValNat 3 (N.factorization P+1) :=
    geom_three_valuation_one hP.one_lt (by omega) hPmod
  obtain ⟨q,hqm,hqP,hqmod,hqv⟩ := low_two_extra_component hN hodd hPmem hmax hL
  by_cases he2 : e % 3 = 2
  · have hPe : P ≠ e := by intro h; subst e; omega
    have heq : e ≠ q := by intro h; subst q; omega
    have h := triple_three_le hN hPmem hemem hqm hPe (by omega) heq
    rw [hPv, euler_delta_component hemem heodd he2] at h
    omega
  · have h := pair_three_le hN hPmem hqm (by omega)
    rw [hPv] at h
    simp only [eulerThreeDelta, if_neg he2, add_zero]
    omega

/-- The full piecewise refinement, including the Euler-prime contribution. -/
theorem euler_three_adic_refinement {N P e : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hemem : e ∈ N.primeFactors) (heodd : Odd (N.factorization e)) :
    N.factorization P - threeAllowance (padicValNat 3 N)
      (padicValNat 3 (N.factorization P+1) + eulerThreeDelta N e) ≤ highWeight N P := by
  have hb := weight_balance hN hodd hPmem hmax
  have hc : lowWeight N P ≤ 2 := low_order_contribution_bound hN hodd hPmem hmax
  have hp := low_positive_euler_budget hN hPmem hemem heodd
  have ht := low_two_euler_budget hN hodd hPmem hmax hemem heodd
  unfold threeAllowance
  split_ifs with hlt heq
  · have hz : lowWeight N P = 0 := by
      by_contra h
      have := hp (Nat.pos_of_ne_zero h)
      omega
    omega
  · have hl : lowWeight N P ≤ 1 := by
      by_contra h
      have := ht (by omega)
      omega
    omega
  · omega

/-- An odd perfect number has exactly one prime divisor with an odd exponent. -/
theorem exists_unique_odd_exponent_prime {N : ℕ} (hN : Nat.Perfect N) (hodd : Odd N) :
    ∃! e, e ∈ N.primeFactors ∧ Odd (N.factorization e) := by
  classical
  have hbal := two_valuation_balance hN hodd
  have hex : ∃ e ∈ N.primeFactors, 0 < padicValNat 2 (component N e) := by
    by_contra h
    push_neg at h
    have hz : (∑ q ∈ N.primeFactors, padicValNat 2 (component N q)) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have := h q hq
      omega
    omega
  obtain ⟨e,he,hev⟩ := hex
  have hed := dvd_of_one_le_padicValNat hev
  have heodd : Odd (N.factorization e) := by
    by_contra h
    have hlen : Odd (N.factorization e+1) := by
      apply Nat.odd_iff.mpr
      have hn : N.factorization e % 2 ≠ 1 := fun hh => h (Nat.odd_iff.mpr hh)
      omega
    exact (geom_odd (prime_odd hodd he) hlen).not_two_dvd_nat hed
  refine ⟨e, ⟨he,heodd⟩, ?_⟩
  intro q hq
  have hlen : 2 ∣ N.factorization q+1 := Nat.dvd_of_mod_eq_zero (by
    have := Nat.odd_iff.mp hq.2; omega)
  exact even_components_unique hN hodd hq.1 he
    (even_component_of_even_length (prime_odd hodd hq.1) hlen) hed

lemma threeAllowance_antitone_right (b t d : ℕ) :
    threeAllowance b (t+d) ≤ threeAllowance b t := by
  unfold threeAllowance
  split_ifs <;> omega

/-- The refinement depending only on the exponents at 3 and at the largest prime. -/
theorem three_adic_refinement {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P) :
    N.factorization P - threeAllowance (padicValNat 3 N)
      (padicValNat 3 (N.factorization P+1)) ≤ highWeight N P := by
  obtain ⟨e,he,_⟩ := exists_unique_odd_exponent_prime hN hodd
  have h := euler_three_adic_refinement hN hodd hPmem hmax he.1 he.2
  have hc := threeAllowance_antitone_right (padicValNat 3 N)
    (padicValNat 3 (N.factorization P+1)) (eulerThreeDelta N e)
  omega

end LargestPrimeOrders
