import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Orders three and six at the largest prime divisor of an odd perfect number

The final theorems use `Nat.Perfect` and `Odd` as their number-theoretic
hypotheses. No conjectural statement is assumed.
-/

namespace LargestPrimeOrders

open Finset

def geom (q n : ℕ) : ℕ := ∑ i ∈ range n, q ^ i

def component (N q : ℕ) : ℕ := geom q (N.factorization q + 1)

noncomputable def ord (P q : ℕ) : ℕ := orderOf (q : ZMod P)

lemma geom_pos (q : ℕ) {n : ℕ} (hn : 0 < n) : 0 < geom q n := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ range n) => Nat.zero_le (q ^ i))
    (show 0 ∈ range n by simpa)
  simp only [pow_zero] at h
  exact lt_of_lt_of_le (by decide : 0 < 1) h

lemma component_pos (N q : ℕ) : 0 < component N q := geom_pos q (by omega)

lemma geom_cast (q n P : ℕ) :
    (geom q n : ZMod P) = ∑ i ∈ range n, (q : ZMod P) ^ i := by
  simp [geom]

lemma geom_identity (q n : ℕ) (hq : 1 ≤ q) :
    geom q n * (q - 1) = q ^ n - 1 := by
  exact geom_sum_mul_of_one_le hq n

lemma geom_mul (q d m : ℕ) : geom q (d * m) = geom q d * geom (q ^ d) m := by
  induction m with
  | zero => simp [geom]
  | succ m ih =>
    rw [Nat.mul_succ]
    simp only [geom, Finset.sum_range_add] at *
    rw [ih]
    simp only [pow_add, ← Finset.mul_sum, ← pow_mul, Finset.sum_range_succ]
    ring

lemma geom_dvd_geom {q d n : ℕ} (h : d ∣ n) : geom q d ∣ geom q n := by
  obtain ⟨m, rfl⟩ := h
  rw [geom_mul]
  exact dvd_mul_right _ _

lemma component_sigma {N q : ℕ} (hq : q.Prime) :
    component N q = ArithmeticFunction.sigma 1 (q ^ N.factorization q) := by
  simpa [component, geom] using
    (ArithmeticFunction.sigma_one_apply_prime_pow (i := N.factorization q) hq).symm

lemma perfect_product {N : ℕ} (hN : Nat.Perfect N) :
    ∏ q ∈ N.primeFactors, component N q = 2 * N := by
  change (∏ q ∈ N.primeFactors, ∑ i ∈ range (N.factorization q + 1), q ^ i) = 2 * N
  rw [← Nat.sum_divisors hN.2.ne']
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN

lemma component_dvd {N q : ℕ} (hN : Nat.Perfect N) (hq : q ∈ N.primeFactors) :
    component N q ∣ 2 * N := by
  rw [← perfect_product hN]
  exact Finset.dvd_prod_of_mem _ hq

lemma prime_odd {N q : ℕ} (hN : Odd N) (hq : q ∈ N.primeFactors) : Odd q := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mem_primeFactors hq
  rw [hk, Nat.odd_mul] at hN
  exact hN.1

lemma prime_ge_three {N q : ℕ} (hN : Odd N) (hq : q ∈ N.primeFactors) : 3 ≤ q := by
  have h := (Nat.prime_of_mem_primeFactors hq).two_le
  have ho := Nat.odd_iff.mp (prime_odd hN hq)
  omega

lemma prime_closed {N q r : ℕ} (hN : Nat.Perfect N) (hq : q ∈ N.primeFactors)
    (hr : r.Prime) (hr2 : r ≠ 2) (hd : r ∣ component N q) : r ∈ N.primeFactors := by
  have h := hr.dvd_mul.mp (hd.trans (component_dvd hN hq))
  have hnot : ¬ r ∣ 2 := by
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  exact Nat.mem_primeFactors.mpr ⟨hr, h.resolve_left hnot, hN.2.ne'⟩

lemma padic_prod {P : ℕ} [Fact P.Prime] (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ q ∈ s, f q ≠ 0) :
    padicValNat P (∏ q ∈ s, f q) = ∑ q ∈ s, padicValNat P (f q) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul
      (hf a (by simp)) (Finset.prod_ne_zero_iff.mpr (fun q hq => hf q (by simp [hq])))]
    rw [ih (fun q hq => hf q (by simp [hq]))]

lemma valuation_balance {N P : ℕ} (hN : Nat.Perfect N) (hP : P.Prime) (hP2 : P ≠ 2) :
    ∑ q ∈ N.primeFactors, padicValNat P (component N q) = N.factorization P := by
  letI : Fact P.Prime := ⟨hP⟩
  rw [← padic_prod _ _ (fun q _ => (component_pos N q).ne'), perfect_product hN]
  rw [padicValNat.mul (by decide) hN.2.ne', Nat.factorization_def N hP]
  have hnot : ¬ P ∣ 2 := by
    intro h
    exact hP2 ((Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).mp h)
  rw [padicValNat.eq_zero_of_not_dvd hnot, zero_add]

lemma cast_ne_one_of_lt {P q : ℕ} (hP : 1 < P) (hq : 1 < q) (hqlt : q < P) :
    (q : ZMod P) ≠ 1 := by
  intro h
  have hh := (ZMod.natCast_eq_natCast_iff' q 1 P).mp (by simpa using h)
  rw [Nat.mod_eq_of_lt hqlt, Nat.mod_eq_of_lt hP] at hh
  omega

lemma geom_cast_of_one {P q n : ℕ} (h : (q : ZMod P) = 1) :
    (geom q n : ZMod P) = n := by
  simp [geom_cast, h]

lemma geom_odd {q n : ℕ} (hq : Odd q) (hn : Odd n) : Odd (geom q n) := by
  apply Nat.odd_iff.mpr
  have hq' : (q : ZMod 2) = 1 := by
    apply (ZMod.natCast_eq_natCast_iff' q 1 2).mpr
    simpa using Nat.odd_iff.mp hq
  have h := geom_cast_of_one (n := n) hq'
  have hh := (ZMod.natCast_eq_natCast_iff' (geom q n) n 2).mp h
  rwa [Nat.odd_iff.mp hn] at hh

lemma max_not_dvd_exponent {N P q : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hP : P.Prime) (hPodd : Odd P) (hq : q ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) : ¬ P ∣ N.factorization q + 1 := by
  letI : Fact P.Prime := ⟨hP⟩
  intro hd
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hqle := hmax q hq
  have hqone : (q : ZMod P) ≠ 1 := by
    rcases lt_or_eq_of_le hqle with hlt | rfl
    · exact cast_ne_one_of_lt hP.one_lt hqprime.one_lt hlt
    · simp
  have hcast : (geom q P : ZMod P) = 1 := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hqone)
    have h := geom_sum_mul (q : ZMod P) P
    rw [ZMod.pow_card, ← geom_cast] at h
    simpa using h
  have hgt : 1 < geom q P := by
    have h := Finset.sum_le_sum_of_subset (Finset.range_mono hP.two_le)
      (f := fun i => q ^ i)
    have hsmall : geom q 2 = 1 + q := by simp [geom, Finset.sum_range_succ]
    change geom q 2 ≤ geom q P at h
    rw [hsmall] at h
    have := hqprime.two_le
    omega
  obtain ⟨r, hr, hrdiv⟩ := Nat.exists_prime_and_dvd (by omega : geom q P ≠ 1)
  have hrP : r ≠ P := by
    intro heq
    subst r
    have hz := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hrdiv
    rw [hcast] at hz
    exact one_ne_zero hz
  have hr2 : r ≠ 2 := by
    intro heq
    subst r
    exact (geom_odd (prime_odd hodd hq) hPodd).not_two_dvd_nat hrdiv
  have hrmem : r ∈ N.primeFactors := prime_closed hN hq hr hr2
    (hrdiv.trans (geom_dvd_geom hd))
  letI : Fact r.Prime := ⟨hr⟩
  have hz : (geom q P : ZMod r) = 0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hrdiv
  have hpow : (q : ZMod r) ^ P = 1 := by
    have h := geom_sum_mul (q : ZMod r) P
    rw [← geom_cast, hz, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  have hqone' : (q : ZMod r) ≠ 1 := by
    intro heq
    have hc := geom_cast_of_one (n := P) heq
    rw [hz] at hc
    have hdvd : r ∣ P := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hc.symm
    exact hrP ((Nat.prime_dvd_prime_iff_eq hr hP).mp hdvd)
  have hord : orderOf (q : ZMod r) = P := by
    rcases (Nat.dvd_prime hP).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact False.elim (hqone' (orderOf_eq_one_iff.mp h))
    · exact h
  have hqzero : (q : ZMod r) ≠ 0 := by
    intro heq
    rw [heq, zero_pow hP.ne_zero] at hpow
    exact zero_ne_one hpow
  have horder := ZMod.orderOf_dvd_card_sub_one hqzero
  rw [hord] at horder
  have hle := Nat.le_of_dvd (by have := hr.two_le; omega : 0 < r - 1) horder
  have hrle := hmax r hrmem
  omega

lemma order_dvd_of_component_dvd {N P q : ℕ} (hd : P ∣ component N q) :
    ord P q ∣ N.factorization q + 1 := by
  apply orderOf_dvd_of_pow_eq_one
  have h := geom_sum_mul (q : ZMod P) (N.factorization q + 1)
  rw [← geom_cast, ← component, (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd,
    zero_mul] at h
  exact sub_eq_zero.mp h.symm

lemma component_val_eq_geom_order {N P q : ℕ} (hP : P.Prime)
    (hnd : ¬ P ∣ N.factorization q + 1) (hd : P ∣ component N q) :
    padicValNat P (component N q) = padicValNat P (geom q (ord P q)) := by
  letI : Fact P.Prime := ⟨hP⟩
  obtain ⟨m, hm⟩ := order_dvd_of_component_dvd hd
  have hpos : 0 < ord P q := by
    by_contra h
    have hz : ord P q = 0 := by omega
    rw [hz, zero_mul] at hm
    omega
  have hmpos : 0 < m := by nlinarith [Nat.zero_le (ord P q)]
  have hmn : ¬ P ∣ m := by
    intro h
    exact hnd (hm ▸ dvd_mul_of_dvd_right h _)
  have hp : ((q ^ ord P q : ℕ) : ZMod P) = 1 := by
    push_cast
    exact pow_orderOf_eq_one (q : ZMod P)
  have hgn : ¬ P ∣ geom (q ^ ord P q) m := by
    intro h
    have hzero := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h
    rw [geom_cast_of_one hp] at hzero
    exact hmn ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hzero)
  unfold component
  rw [hm, geom_mul, padicValNat.mul (geom_pos q hpos).ne'
    (geom_pos (q ^ ord P q) hmpos).ne', padicValNat.eq_zero_of_not_dvd hgn, add_zero]

def phi3 (q : ℕ) : ℕ := q ^ 2 + q + 1
def phi6 (q : ℕ) : ℕ := q ^ 2 - q + 1

lemma q_le_square {q : ℕ} (hq : 1 ≤ q) : q ≤ q ^ 2 := by nlinarith

lemma phi6_pos (q : ℕ) : 0 < phi6 q := by unfold phi6; omega

lemma phi6_cast (q P : ℕ) (hq : 1 ≤ q) :
    (phi6 q : ZMod P) = (q : ZMod P) ^ 2 - q + 1 := by
  simp [phi6, Nat.cast_sub (q_le_square hq)]

lemma geom_three (q : ℕ) : geom q 3 = phi3 q := by
  simp [geom, phi3, Finset.sum_range_succ]
  ring

lemma geom_six {q : ℕ} (hq : 1 ≤ q) :
    geom q 6 = (q + 1) * phi3 q * phi6 q := by
  have hsq := q_le_square hq
  zify
  simp [geom, phi3, phi6, Finset.sum_range_succ, Nat.cast_sub hsq]
  ring

lemma order_three_phi {P q : ℕ} (hP : P.Prime) (hord : ord P q = 3) :
    P ∣ phi3 q := by
  letI : Fact P.Prime := ⟨hP⟩
  have hpow : (q : ZMod P) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (q : ZMod P)
    change (q : ZMod P) ^ ord P q = 1 at h
    rwa [hord] at h
  have hne : (q : ZMod P) ≠ 1 := by
    intro h
    have h' : ord P q = 1 := orderOf_eq_one_iff.mpr h
    omega
  have hmul : ((q : ZMod P) - 1) * ((q : ZMod P)^2 + q + 1) = 0 := by
    linear_combination hpow
  have hzero := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa [phi3] using hzero

lemma order_six_phi {P q : ℕ} (hP : P.Prime) (hq : 1 ≤ q) (hord : ord P q = 6) :
    P ∣ phi6 q ∧ ¬ P ∣ phi3 q := by
  letI : Fact P.Prime := ⟨hP⟩
  have hpow : (q : ZMod P) ^ 6 = 1 := by
    have h := pow_orderOf_eq_one (q : ZMod P)
    change (q : ZMod P) ^ ord P q = 1 at h
    rwa [hord] at h
  have hnot3 : (q : ZMod P) ^ 3 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    change ord P q ∣ 3 at hd
    rw [hord] at hd
    norm_num at hd
  have hnot2 : (q : ZMod P) ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    change ord P q ∣ 2 at hd
    rw [hord] at hd
    norm_num at hd
  have hcube : (q : ZMod P)^3 + 1 = 0 := by
    have hmul : ((q : ZMod P)^3 - 1) * ((q : ZMod P)^3 + 1) = 0 := by
      linear_combination hpow
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hnot3)
  have hplus : (q : ZMod P) + 1 ≠ 0 := by
    intro h
    apply hnot2
    linear_combination ((q : ZMod P) - 1) * h
  have hphi : (q : ZMod P)^2 - q + 1 = 0 := by
    have hmul : ((q : ZMod P) + 1) * ((q : ZMod P)^2 - q + 1) = 0 := by
      linear_combination hcube
    exact (mul_eq_zero.mp hmul).resolve_left hplus
  constructor
  · apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
    rwa [phi6_cast q P hq]
  · intro hd
    have hzero := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    have hphi3 : (q : ZMod P)^2 + q + 1 = 0 := by simpa [phi3] using hzero
    apply hnot3
    linear_combination ((q : ZMod P) - 1) * hphi3

lemma phi_bounds {P q : ℕ} (hPodd : Odd P) (hqodd : Odd q)
    (hq : 3 ≤ q) (hqlt : q < P) : phi3 q < P^2 ∧ phi6 q < P^2 := by
  have hpmod := Nat.odd_iff.mp hPodd
  have hqmod := Nat.odd_iff.mp hqodd
  have hgap : q + 2 ≤ P := by omega
  have hsq := q_le_square (by omega : 1 ≤ q)
  have hsub := Nat.sub_add_cancel hsq
  unfold phi3 phi6
  constructor <;> nlinarith

lemma val_le_one_of_lt_square {P x : ℕ} (hP : P.Prime) (hx : 0 < x)
    (hsmall : x < P^2) : padicValNat P x ≤ 1 := by
  letI : Fact P.Prime := ⟨hP⟩
  by_contra h
  have hd : P^2 ∣ x := (padicValNat_dvd_iff_le hx.ne').mpr (by omega)
  exact (not_le_of_gt hsmall) (Nat.le_of_dvd hx hd)

lemma low_order_val_le_one {N P q : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hqmem : q ∈ N.primeFactors) (hqlt : q < P)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hord : ord P q = 3 ∨ ord P q = 6) :
    padicValNat P (component N q) ≤ 1 := by
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hPodd := prime_odd hodd hPmem
  have hqodd := prime_odd hodd hqmem
  have hq3 := prime_ge_three hodd hqmem
  letI : Fact P.Prime := ⟨hP⟩
  by_cases hd : P ∣ component N q
  · rw [component_val_eq_geom_order hP
      (max_not_dvd_exponent hN hodd hP hPodd hqmem hmax) hd]
    obtain h3 | h6 := hord
    · rw [h3, geom_three]
      exact val_le_one_of_lt_square hP (by unfold phi3; omega)
        (phi_bounds hPodd hqodd hq3 hqlt).1
    · rw [h6, geom_six (by omega : 1 ≤ q)]
      have hphi := order_six_phi hP (by omega : 1 ≤ q) h6
      have hnot : ¬ P ∣ q + 1 := by
        intro h
        have hle := Nat.le_of_dvd (by omega : 0 < q + 1) h
        have hpmod := Nat.odd_iff.mp hPodd
        have hqmod := Nat.odd_iff.mp hqodd
        omega
      rw [padicValNat.mul (by unfold phi3; positivity) (phi6_pos q).ne',
        padicValNat.mul (by omega) (by unfold phi3; positivity),
        padicValNat.eq_zero_of_not_dvd hnot,
        padicValNat.eq_zero_of_not_dvd hphi.2, zero_add, zero_add]
      exact val_le_one_of_lt_square hP (phi6_pos q) (phi_bounds hPodd hqodd hq3 hqlt).2
  · rw [padicValNat.eq_zero_of_not_dvd hd]
    omega

lemma three_six_incompatible {P u v : ℕ} (hP : P.Prime) (hPodd : Odd P)
    (huodd : Odd u) (hvodd : Odd v) (hu : 3 ≤ u) (hv : 3 ≤ v)
    (huP : u < P) (hvP : v < P)
    (h3 : ord P u = 3) (h6 : ord P v = 6) : False := by
  letI : Fact P.Prime := ⟨hP⟩
  have hu3 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (order_three_phi hP h3)
  have hv6 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr
    (order_six_phi hP (by omega : 1 ≤ v) h6).1
  have huc : (u : ZMod P)^2 + u + 1 = 0 := by simpa [phi3] using hu3
  have hvc : (v : ZMod P)^2 - v + 1 = 0 := by
    simpa [phi6_cast v P (by omega : 1 ≤ v)] using hv6
  have hm : ((u : ZMod P) + v) * ((u : ZMod P) - v + 1) = 0 := by
    linear_combination huc - hvc
  have hpmod := Nat.odd_iff.mp hPodd
  have humod := Nat.odd_iff.mp huodd
  have hvmod := Nat.odd_iff.mp hvodd
  obtain h | h := mul_eq_zero.mp hm
  · have hd : P ∣ u + v := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using h)
    obtain ⟨k, hk⟩ := hd
    have hkpos : 1 ≤ k := by nlinarith
    have hklt : k < 2 := by nlinarith
    have : k = 1 := by omega
    subst k
    omega
  · have hc : ((u + 1 : ℕ) : ZMod P) = (v : ZMod P) := by
      push_cast
      linear_combination h
    have heq := (ZMod.natCast_eq_natCast_iff' (u + 1) v P).mp hc
    have hup : u + 1 < P := by omega
    rw [Nat.mod_eq_of_lt hup, Nat.mod_eq_of_lt hvP] at heq
    omega

lemma three_pair_sum {P u v : ℕ} (hP : P.Prime) (huP : u < P) (hvP : v < P)
    (hne : u ≠ v) (h3u : ord P u = 3) (h3v : ord P v = 3) : u + v + 1 = P := by
  letI : Fact P.Prime := ⟨hP⟩
  have hu3 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (order_three_phi hP h3u)
  have hv3 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (order_three_phi hP h3v)
  have huc : (u : ZMod P)^2 + u + 1 = 0 := by simpa [phi3] using hu3
  have hvc : (v : ZMod P)^2 + v + 1 = 0 := by simpa [phi3] using hv3
  have hm : ((u : ZMod P) - v) * ((u : ZMod P) + v + 1) = 0 := by
    linear_combination huc - hvc
  have hne' : (u : ZMod P) ≠ v := by
    intro h
    have heq := (ZMod.natCast_eq_natCast_iff' u v P).mp h
    rw [Nat.mod_eq_of_lt huP, Nat.mod_eq_of_lt hvP] at heq
    exact hne heq
  have h := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne')
  have hd : P ∣ u + v + 1 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using h)
  obtain ⟨k, hk⟩ := hd
  have hkle : k ≤ 1 := by nlinarith
  have hkpos : 1 ≤ k := by nlinarith
  have : k = 1 := by omega
  subst k
  simpa using hk

lemma two_valuation_balance {N : ℕ} (hN : Nat.Perfect N) (hodd : Odd N) :
    ∑ q ∈ N.primeFactors, padicValNat 2 (component N q) = 1 := by
  rw [← padic_prod _ _ (fun q _ => (component_pos N q).ne'), perfect_product hN,
    padicValNat.mul (by decide) hN.2.ne', padicValNat_self,
    padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]

lemma even_components_unique {N u v : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hu : u ∈ N.primeFactors) (hv : v ∈ N.primeFactors)
    (hue : 2 ∣ component N u) (hve : 2 ∣ component N v) : u = v := by
  by_contra hne
  have huval := one_le_padicValNat_of_dvd (component_pos N u) hue
  have hvval := one_le_padicValNat_of_dvd (component_pos N v) hve
  have hsubset : ({u, v} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hs := Finset.sum_le_sum_of_subset hsubset
    (f := fun q => padicValNat 2 (component N q))
  rw [Finset.sum_pair hne, two_valuation_balance hN hodd] at hs
  omega

lemma even_component_of_even_length {N q : ℕ} (hodd : Odd q)
    (hlen : 2 ∣ N.factorization q + 1) : 2 ∣ component N q := by
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
  have hq : (q : ZMod 2) = 1 := by
    apply (ZMod.natCast_eq_natCast_iff' q 1 2).mpr
    simpa using Nat.odd_iff.mp hodd
  change (geom q (N.factorization q + 1) : ZMod 2) = 0
  rw [geom_cast_of_one hq]
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hlen

noncomputable def sources (N P d : ℕ) : Finset ℕ := by
  classical
  exact N.primeFactors.filter (fun q => q < P ∧ ord P q = d ∧ P ∣ component N q)

noncomputable def high (N P : ℕ) : Finset ℕ := by
  classical
  exact N.primeFactors.filter (fun q => q < P ∧ ord P q ≠ 3 ∧ ord P q ≠ 6)

lemma mem_sources {N P d q : ℕ} :
    q ∈ sources N P d ↔ q ∈ N.primeFactors ∧ q < P ∧ ord P q = d ∧ P ∣ component N q := by
  classical
  simp [sources]

lemma three_sources_card_le_two {N P : ℕ} (hP : P.Prime) : (sources N P 3).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < (sources N P 3).card)
  obtain ⟨_, huP, hu3, _⟩ := mem_sources.mp hu
  obtain ⟨_, hvP, hv3, _⟩ := mem_sources.mp hv
  obtain ⟨_, hwP, hw3, _⟩ := mem_sources.mp hw
  have h1 := three_pair_sum hP huP hvP huv hu3 hv3
  have h2 := three_pair_sum hP huP hwP huw hu3 hw3
  exact hvw (by omega)

lemma six_sources_card_le_one {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N) :
    (sources N P 6).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hum, _, hu6, hud⟩ := mem_sources.mp hu
  obtain ⟨hvm, _, hv6, hvd⟩ := mem_sources.mp hv
  have hdu := order_dvd_of_component_dvd hud
  have hdv := order_dvd_of_component_dvd hvd
  rw [hu6] at hdu
  rw [hv6] at hdv
  exact even_components_unique hN hodd hum hvm
    (even_component_of_even_length (prime_odd hodd hum) ((by decide : 2 ∣ 6).trans hdu))
    (even_component_of_even_length (prime_odd hodd hvm) ((by decide : 2 ∣ 6).trans hdv))

lemma three_or_six_sources_empty {N P : ℕ} (hodd : Odd N) (hPmem : P ∈ N.primeFactors) :
    sources N P 3 = ∅ ∨ sources N P 6 = ∅ := by
  classical
  by_cases h3 : sources N P 3 = ∅
  · exact Or.inl h3
  right
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro v hv
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr h3
  obtain ⟨hum, huP, hu3, _⟩ := mem_sources.mp hu
  obtain ⟨hvm, hvP, hv6, _⟩ := mem_sources.mp hv
  exact three_six_incompatible (Nat.prime_of_mem_primeFactors hPmem)
    (prime_odd hodd hPmem) (prime_odd hodd hum) (prime_odd hodd hvm)
    (prime_ge_three hodd hum) (prime_ge_three hodd hvm) huP hvP hu3 hv6

lemma order_three_mod_three {N P q : ℕ} (hN : Nat.Perfect N) (hnot3 : ¬3 ∣ N)
    (hq : q ∈ N.primeFactors) (hord : ord P q = 3) (hd : P ∣ component N q) : q % 3 = 2 := by
  have hlen := order_dvd_of_component_dvd hd
  rw [hord] at hlen
  have hq0 : q % 3 ≠ 0 := by
    intro h
    exact hnot3 ((Nat.dvd_of_mod_eq_zero h).trans (Nat.dvd_of_mem_primeFactors hq))
  have hq1 : q % 3 ≠ 1 := by
    intro h
    have hc : (q : ZMod 3) = 1 := by
      apply (ZMod.natCast_eq_natCast_iff' q 1 3).mpr
      simpa using h
    have hgc : (component N q : ZMod 3) = 0 := by
      change (geom q (N.factorization q + 1) : ZMod 3) = 0
      rw [geom_cast_of_one hc]
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hlen
    have hdiv := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hgc
    have h := prime_closed hN hq (by decide : Nat.Prime 3) (by decide : 3 ≠ 2) hdiv
    exact hnot3 (Nat.dvd_of_mem_primeFactors h)
  omega

lemma three_sources_card_le_one {N P : ℕ} (hN : Nat.Perfect N) (hP : P.Prime)
    (hnot3 : ¬3 ∣ N) : (sources N P 3).card ≤ 1 := by
  classical
  letI : Fact P.Prime := ⟨hP⟩
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra hne
  obtain ⟨hum, huP, hu3, hud⟩ := mem_sources.mp hu
  obtain ⟨hvm, hvP, hv3, hvd⟩ := mem_sources.mp hv
  have hsum := three_pair_sum hP huP hvP hne hu3 hv3
  have hu2 := order_three_mod_three hN hnot3 hum hu3 hud
  have hv2 := order_three_mod_three hN hnot3 hvm hv3 hvd
  have huzero : (u : ZMod P) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
    have := Nat.le_of_dvd (Nat.prime_of_mem_primeFactors hum).pos hd
    omega
  have hord := ZMod.orderOf_dvd_card_sub_one huzero
  change ord P u ∣ P - 1 at hord
  rw [hu3] at hord
  have hmod := Nat.mod_eq_zero_of_dvd hord
  have := hP.two_le
  omega

lemma source_sum_le_card {N P d : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hd : d = 3 ∨ d = 6) :
    ∑ q ∈ sources N P d, padicValNat P (component N q) ≤ (sources N P d).card := by
  classical
  calc
    _ ≤ ∑ q ∈ sources N P d, 1 := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqm, hqP, hqd, _⟩ := mem_sources.mp hq
      apply low_order_val_le_one hN hodd hPmem hqm hqP hmax
      rcases hd with h | h <;> simp_all
    _ = _ := by simp

lemma self_component_val_zero (N P : ℕ) : padicValNat P (component N P) = 0 := by
  by_cases hP : P = 1
  · subst P
    simp
  apply padicValNat.eq_zero_of_not_dvd
  intro hd
  have h := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  have hcast : (component N P : ZMod P) = 1 := by
    simp [component, geom_cast, Finset.sum_range_succ']
  rw [hcast] at h
  have hdiv : P ∣ 1 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using h)
  exact hP (Nat.eq_one_of_dvd_one hdiv)

lemma valuation_partition {N P : ℕ} (hmax : ∀ r ∈ N.primeFactors, r ≤ P) :
    ∑ q ∈ N.primeFactors, padicValNat P (component N q) =
      (∑ q ∈ high N P, padicValNat P (component N q)) +
      (∑ q ∈ sources N P 3, padicValNat P (component N q)) +
      (∑ q ∈ sources N P 6, padicValNat P (component N q)) := by
  classical
  simp only [high, sources, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqP : q = P
  · subst q
    simp [self_component_val_zero]
  have hqP' : q < P := lt_of_le_of_ne (hmax q hq) hqP
  by_cases hd : P ∣ component N q
  · by_cases h3 : ord P q = 3
    · have h6 : ord P q ≠ 6 := by omega
      simp [hqP', hd, h3, h6]
    · by_cases h6 : ord P q = 6 <;> simp [hqP', hd, h3, h6]
  · simp [padicValNat.eq_zero_of_not_dvd hd]

/-- The main bound, directly from oddness and `Nat.Perfect`. -/
theorem largestPrime_order_bound {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P) :
    N.factorization P - 2 ≤ ∑ q ∈ high N P, padicValNat P (component N q) := by
  classical
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hP2 : P ≠ 2 := by
    intro h
    exact (prime_odd hodd hPmem).not_two_dvd_nat (by simp [h])
  have hbal := valuation_balance hN hP hP2
  rw [valuation_partition hmax] at hbal
  have hs3 := source_sum_le_card hN hodd hPmem hmax (Or.inl rfl : 3 = 3 ∨ 3 = 6)
  have hs6 := source_sum_le_card hN hodd hPmem hmax (Or.inr rfl : 6 = 3 ∨ 6 = 6)
  have hc3 := three_sources_card_le_two (N := N) hP
  have hc6 := six_sources_card_le_one (P := P) hN hodd
  rcases three_or_six_sources_empty hodd hPmem with h | h
  · simp only [h, Finset.sum_empty] at hbal hs3
    omega
  · simp only [h, Finset.sum_empty] at hbal hs6
    omega

/-- The improved bound when three does not divide the odd perfect number. -/
theorem largestPrime_order_bound_without_three {N P : ℕ} (hN : Nat.Perfect N)
    (hodd : Odd N) (hPmem : P ∈ N.primeFactors)
    (hmax : ∀ q ∈ N.primeFactors, q ≤ P) (hnot3 : ¬3 ∣ N) :
    N.factorization P - 1 ≤ ∑ q ∈ high N P, padicValNat P (component N q) := by
  classical
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hP2 : P ≠ 2 := by
    intro h
    exact (prime_odd hodd hPmem).not_two_dvd_nat (by simp [h])
  have hbal := valuation_balance hN hP hP2
  rw [valuation_partition hmax] at hbal
  have hs3 := source_sum_le_card hN hodd hPmem hmax (Or.inl rfl : 3 = 3 ∨ 3 = 6)
  have hs6 := source_sum_le_card hN hodd hPmem hmax (Or.inr rfl : 6 = 3 ∨ 6 = 6)
  have hc3 := three_sources_card_le_one hN hP hnot3
  have hc6 := six_sources_card_le_one (P := P) hN hodd
  rcases three_or_six_sources_empty hodd hPmem with h | h
  · simp only [h, Finset.sum_empty] at hbal hs3
    omega
  · simp only [h, Finset.sum_empty] at hbal hs6
    omega

end LargestPrimeOrders



