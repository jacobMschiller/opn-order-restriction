import FourthPowerBudget
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Data.Nat.Log

namespace LargestPrimeOrders

open Finset Polynomial

/-- The positive integer obtained by evaluating the d-th cyclotomic polynomial at q > 1. -/
noncomputable def cycloValue (q d : ℕ) : ℕ := ((cyclotomic d ℤ).eval (q : ℤ)).natAbs

lemma cycloValue_pos {q : ℕ} (hq : 1 < q) (d : ℕ) : 0 < cycloValue q d := by
  have h := cyclotomic_pos' d (show (1 : ℤ) < q by exact_mod_cast hq)
  exact Int.natAbs_pos.mpr (ne_of_gt h)

lemma cycloValue_cast {q : ℕ} (hq : 1 < q) (d : ℕ) :
    (cycloValue q d : ℝ) = (cyclotomic d ℝ).eval (q : ℝ) := by
  have h := cyclotomic_pos' d (show (1 : ℤ) < q by exact_mod_cast hq)
  have hc := cyclotomic.eval_apply (q : ℤ) d (Int.castRingHom ℝ)
  rw [cycloValue, Int.cast_natAbs, abs_of_pos (by exact_mod_cast h)]
  simpa using hc.symm

lemma cycloValue_prod {q d : ℕ} (hq : 1 < q) (hd : 0 < d) :
    (∏ i ∈ d.divisors, cycloValue q i) = q^d-1 := by
  have h := congrArg (fun f : Polynomial ℤ => f.eval (q : ℤ))
    (prod_cyclotomic_eq_X_pow_sub_one hd ℤ)
  simp only [eval_prod,eval_sub,eval_pow,eval_X,eval_one] at h
  let absHom : ℤ →* ℕ :=
    { toFun := Int.natAbs, map_one' := Int.natAbs_one, map_mul' := Int.natAbs_mul }
  have ha := congrArg absHom h
  rw [map_prod] at ha
  have hp : 1 ≤ q^d := one_le_pow₀ hq.le
  have hs : (q : ℤ)^d-1 = ((q^d-1 : ℕ) : ℤ) := by
    simp only [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_one]
  rw [hs] at ha
  simpa [cycloValue, absHom] using ha

lemma order_dvd_of_dvd_cycloValue {P q d : ℕ} (hd : 0 < d)
    (hdiv : P ∣ cycloValue q d) : ord P q ∣ d := by
  have hZ : (P : ℤ) ∣ (cyclotomic d ℤ).eval (q : ℤ) := Int.natCast_dvd.mpr hdiv
  have hzero : (Int.castRingHom (ZMod P)) ((cyclotomic d ℤ).eval (q : ℤ)) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hZ
  have hroot : (cyclotomic d (ZMod P)).IsRoot (q : ZMod P) := by
    have h := cyclotomic.eval_apply (q : ℤ) d (Int.castRingHom (ZMod P))
    simpa [IsRoot,hzero] using h
  exact orderOf_dvd_of_pow_eq_one
    (isRoot_of_unity_of_root_cyclotomic (Nat.mem_divisors_self _ hd.ne') hroot)

lemma order_valuation_eq_cycloValue {P q : ℕ} (hP : P.Prime) (hq : 1 < q)
    (hd : 0 < ord P q) :
    padicValNat P (q^(ord P q)-1) = padicValNat P (cycloValue q (ord P q)) := by
  letI : Fact P.Prime := ⟨hP⟩
  rw [← cycloValue_prod hq hd, padic_prod _ _ (fun i _ => (cycloValue_pos hq i).ne')]
  apply Finset.sum_eq_single (ord P q)
  · intro i hi hne
    apply padicValNat.eq_zero_of_not_dvd
    intro hdiv
    have hid := Nat.dvd_of_mem_divisors hi
    have hdi := order_dvd_of_dvd_cycloValue (Nat.pos_of_mem_divisors hi) hdiv
    exact hne (Nat.dvd_antisymm hid hdi)
  · intro h
    exact False.elim (h (Nat.mem_divisors_self _ hd.ne'))

lemma component_val_eq_cycloValue {N P q : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hqmem : q ∈ N.primeFactors) (hqP : q < P)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hdiv : P ∣ component N q) :
    padicValNat P (component N q) = padicValNat P (cycloValue q (ord P q)) := by
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hq := Nat.prime_of_mem_primeFactors hqmem
  letI : Fact P.Prime := ⟨hP⟩
  have hd := Nat.pos_of_dvd_of_pos (order_dvd_of_component_dvd hdiv) (by omega)
  have hcomp := component_val_eq_geom_order hP
    (max_not_dvd_exponent hN hodd hP (prime_odd hodd hPmem) hqmem hmax) hdiv
  have hqm : 0 < q-1 := by have := hq.two_le; omega
  have hnot : ¬P ∣ q-1 := Nat.not_dvd_of_pos_of_lt hqm (by omega)
  have hv : padicValNat P (q^(ord P q)-1) = padicValNat P (geom q (ord P q)) := by
    rw [← geom_identity q _ hq.one_lt.le,
      padicValNat.mul (geom_pos q hd).ne' hqm.ne',padicValNat.eq_zero_of_not_dvd hnot,add_zero]
  exact hcomp.trans (hv.symm.trans (order_valuation_eq_cycloValue hP hq.one_lt hd))

lemma cycloValue_lt_prime_pow {P q d : ℕ} (hq : 1 < q) (hqP : q < P) (hd : 3 ≤ d) :
    cycloValue q d < P^(Nat.totient d) := by
  have h := cyclotomic_eval_lt_add_one_pow_totient hd (show (1 : ℝ) < q by exact_mod_cast hq)
  have hle : ((q : ℝ)+1)^(Nat.totient d) ≤ (P : ℝ)^(Nat.totient d) := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast (show q+1 ≤ P by omega)
  have hlt := h.trans_le hle
  rw [← cycloValue_cast hq] at hlt
  exact_mod_cast hlt

/-- Every contributing component has a capacity controlled by its cyclotomic degree. -/
theorem high_component_totient_upper {N P q : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hq : q ∈ high N P) (hdiv : P ∣ component N q) :
    padicValNat P (component N q) ≤ Nat.totient (ord P q)-1 := by
  obtain ⟨hqm,hqP,_,_⟩ := Finset.mem_filter.mp hq
  have hp := Nat.prime_of_mem_primeFactors hPmem
  have hqp := Nat.prime_of_mem_primeFactors hqm
  have hdpos := Nat.pos_of_dvd_of_pos (order_dvd_of_component_dvd hdiv) (by omega)
  have hne := high_order_ne_one_two hodd hPmem hq
  have hd : 3 ≤ ord P q := by omega
  rw [component_val_eq_cycloValue hN hodd hPmem hqm hqP hmax hdiv]
  have hle := Nat.le_of_dvd (cycloValue_pos hqp.one_lt (ord P q))
    (pow_padicValNat_dvd (p := P) (n := cycloValue q (ord P q)))
  have hlt := hle.trans_lt (cycloValue_lt_prime_pow hqp.one_lt hqP hd)
  have hv : padicValNat P (cycloValue q (ord P q)) < Nat.totient (ord P q) :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  omega

/-- The subset of H whose components actually contribute to P. -/
noncomputable def highContributors (N P : ℕ) : Finset ℕ := by
  classical
  exact (high N P).filter (fun q => P ∣ component N q)

lemma highWeight_eq_contributors (N P : ℕ) :
    highWeight N P = ∑ q ∈ highContributors N P, padicValNat P (component N q) := by
  classical
  unfold highWeight highContributors
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : P ∣ component N q
  · simp [h]
  · simp [h,padicValNat.eq_zero_of_not_dvd h]

/-- An upper bound independent of the exponent at the largest prime. -/
theorem highWeight_totient_upper {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) :
    highWeight N P ≤ ∑ q ∈ highContributors N P, (Nat.totient (ord P q)-1) := by
  rw [highWeight_eq_contributors]
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hqh,hd⟩ := Finset.mem_filter.mp hq
  exact high_component_totient_upper hN hodd hPmem hmax hqh hd

lemma high_component_log_upper {N P q : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hq : q ∈ high N P) (hdiv : P ∣ component N q) :
    padicValNat P (component N q) ≤ Nat.log P (cycloValue q (ord P q)) := by
  obtain ⟨hqm,hqP,_,_⟩ := Finset.mem_filter.mp hq
  have hp := Nat.prime_of_mem_primeFactors hPmem
  have hqp := Nat.prime_of_mem_primeFactors hqm
  rw [component_val_eq_cycloValue hN hodd hPmem hqm hqP hmax hdiv]
  exact Nat.le_log_of_pow_le hp.one_lt
    (Nat.le_of_dvd (cycloValue_pos hqp.one_lt _) pow_padicValNat_dvd)

/-- A sharper numerical bound using the sizes of the cyclotomic values. -/
theorem highWeight_log_upper {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) :
    highWeight N P ≤ ∑ q ∈ highContributors N P, Nat.log P (cycloValue q (ord P q)) := by
  rw [highWeight_eq_contributors]
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hqh,hd⟩ := Finset.mem_filter.mp hq
  exact high_component_log_upper hN hodd hPmem hmax hqh hd

/-- The logarithmic bound is no larger than the sum of cyclotomic degree bounds. -/
theorem logarithmic_bound_le_totient_bound {N P : ℕ} (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) :
    (∑ q ∈ highContributors N P, Nat.log P (cycloValue q (ord P q))) ≤
      ∑ q ∈ highContributors N P, (Nat.totient (ord P q)-1) := by
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hqh,hdiv⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqm,hqP,_,_⟩ := Finset.mem_filter.mp hqh
  have hqp := Nat.prime_of_mem_primeFactors hqm
  have hdpos := Nat.pos_of_dvd_of_pos (order_dvd_of_component_dvd hdiv) (by omega)
  have hne := high_order_ne_one_two hodd hPmem hqh
  have hd : 3 ≤ ord P q := by omega
  have hlt := Nat.log_lt_of_lt_pow (cycloValue_pos hqp.one_lt (ord P q)).ne'
    (cycloValue_lt_prime_pow hqp.one_lt hqP hd)
  omega

lemma totient_le_of_dvd_two_pow_mul {d m s : ℕ} (hm : 0 < m)
    (hd : d ∣ 2^s*m) (hfour : ¬4 ∣ d) : Nat.totient d ≤ Nat.totient m := by
  rcases Nat.even_or_odd d with he | ho
  · obtain ⟨r,rfl⟩ := he.two_dvd
    have hr : Odd r := by
      rcases Nat.even_or_odd r with he | ho
      · obtain ⟨k,hk⟩ := he.two_dvd
        exact False.elim (hfour ⟨k,by omega⟩)
      · exact ho
    have hrd : r ∣ m := (hr.coprime_two_right.pow_right s).dvd_of_dvd_mul_left
      ((dvd_mul_left r 2).trans hd)
    rw [Nat.totient_mul hr.coprime_two_left]
    simpa using Nat.le_of_dvd (Nat.totient_pos.mpr hm) (Nat.totient_dvd_of_dvd hrd)
  · have hdm : d ∣ m := (ho.coprime_two_right.pow_right s).dvd_of_dvd_mul_left hd
    exact Nat.le_of_dvd (Nat.totient_pos.mpr hm) (Nat.totient_dvd_of_dvd hdm)

/-- Choosing m as the odd part of P-1 gives a uniform capacity for each contributing prime. -/
theorem highWeight_odd_part_upper {N P m s : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : 0 < m) (hfactor : P-1 = 2^s*m) :
    highWeight N P ≤ (highContributors N P).card * (Nat.totient m-1) := by
  have hp := Nat.prime_of_mem_primeFactors hPmem
  letI : Fact P.Prime := ⟨hp⟩
  calc
    highWeight N P ≤ ∑ q ∈ highContributors N P, (Nat.totient (ord P q)-1) :=
      highWeight_totient_upper hN hodd hPmem hmax
    _ ≤ ∑ _q ∈ highContributors N P, (Nat.totient m-1) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqh,hdiv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqm,hqP,_,_⟩ := Finset.mem_filter.mp hqh
      have hqp := Nat.prime_of_mem_primeFactors hqm
      have hqzero : (q : ZMod P) ≠ 0 := by
        intro h
        have hd := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
        have := Nat.le_of_dvd hqp.pos hd
        omega
      have hord : ord P q ∣ 2^s*m := by
        rw [← hfactor]
        exact ZMod.orderOf_dvd_card_sub_one hqzero
      have hfour : ¬4 ∣ ord P q := fun hd =>
        four_not_dvd_length hN hodd hqm (hd.trans (order_dvd_of_component_dvd hdiv))
      exact Nat.sub_le_sub_right (totient_le_of_dvd_two_pow_mul hm hord hfour) 1
    _ = _ := by simp

/-- Without base-q Wieferich congruences, every active high-order component contributes one. -/
theorem highWeight_eq_card_of_no_wieferich {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hnw : ∀ q ∈ highContributors N P, ¬P^2 ∣ q^(P-1)-1) :
    highWeight N P = (highContributors N P).card := by
  rw [highWeight_eq_contributors]
  suffices (∑ q ∈ highContributors N P, padicValNat P (component N q)) =
      (∑ _q ∈ highContributors N P, (1 : ℕ)) by simpa using this
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqh,hdiv⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqm,hqP,_,_⟩ := Finset.mem_filter.mp hqh
  have hp := Nat.prime_of_mem_primeFactors hPmem
  letI : Fact P.Prime := ⟨hp⟩
  have hpos := one_le_padicValNat_of_dvd (component_pos N q) hdiv
  have heq := component_val_eq_fermat hN hodd hPmem hqm hqP hmax hdiv
  have hle : padicValNat P (component N q) ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ padicValNat P (q^(P-1)-1) := by omega
    exact hnw q hq ((pow_dvd_pow P htwo).trans pow_padicValNat_dvd)
  omega

/-- Combining the upper bound with Theorem 1 restricts the largest-prime exponent. -/
theorem largest_exponent_totient_upper {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) :
    N.factorization P ≤ (∑ q ∈ highContributors N P, (Nat.totient (ord P q)-1)) +
      (if 3 ∣ N then 2 else 1) := by
  have hu := highWeight_totient_upper hN hodd hPmem hmax
  by_cases h3 : 3 ∣ N
  · have hl := largestPrime_order_bound hN hodd hPmem hmax
    change N.factorization P-2 ≤ highWeight N P at hl
    simp only [if_pos h3]
    omega
  · have hl := largestPrime_order_bound_without_three hN hodd hPmem hmax h3
    change N.factorization P-1 ≤ highWeight N P at hl
    simp only [if_neg h3]
    omega

end LargestPrimeOrders
