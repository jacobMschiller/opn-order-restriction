import LargestPrimeOrders

namespace LargestPrimeOrders

open Finset

/-- The combined contribution of orders three and six is at most two. -/
theorem low_order_contribution_bound {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P) :
    (∑ q ∈ sources N P 3, padicValNat P (component N q)) +
    (∑ q ∈ sources N P 6, padicValNat P (component N q)) ≤ 2 := by
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hP2 : P ≠ 2 := by
    intro h
    exact (prime_odd hodd hPmem).not_two_dvd_nat (by simp [h])
  have hbal := valuation_balance hN hP hP2
  rw [valuation_partition hmax] at hbal
  have hb := largestPrime_order_bound hN hodd hPmem hmax
  omega

/-- The combined contribution is at most one when three does not divide N. -/
theorem low_order_contribution_bound_without_three {N P : ℕ}
    (hN : Nat.Perfect N) (hodd : Odd N) (hPmem : P ∈ N.primeFactors)
    (hmax : ∀ q ∈ N.primeFactors, q ≤ P) (hnot3 : ¬3 ∣ N) :
    (∑ q ∈ sources N P 3, padicValNat P (component N q)) +
    (∑ q ∈ sources N P 6, padicValNat P (component N q)) ≤ 1 := by
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hP2 : P ≠ 2 := by
    intro h
    exact (prime_odd hodd hPmem).not_two_dvd_nat (by simp [h])
  have hbal := valuation_balance hN hP hP2
  rw [valuation_partition hmax] at hbal
  have hb := largestPrime_order_bound_without_three hN hodd hPmem hmax hnot3
  omega

lemma geom_val_eq_short {P q d n : ℕ} (hP : P.Prime) (hn : 0 < n)
    (hnd : ¬P ∣ n) (hd : d ∣ n) (hpow : (q : ZMod P)^d = 1) :
    padicValNat P (geom q n) = padicValNat P (geom q d) := by
  letI : Fact P.Prime := ⟨hP⟩
  obtain ⟨m, rfl⟩ := hd
  have hdpos : 0 < d := by nlinarith [Nat.zero_le m]
  have hmpos : 0 < m := by nlinarith [Nat.zero_le d]
  have hmn : ¬ P ∣ m := fun h => hnd (dvd_mul_of_dvd_right h _)
  have hp : ((q^d : ℕ) : ZMod P) = 1 := by simpa using hpow
  have hgn : ¬P ∣ geom (q^d) m := by
    intro h
    have hzero := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h
    rw [geom_cast_of_one hp] at hzero
    exact hmn ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp hzero)
  rw [geom_mul, padicValNat.mul (geom_pos q hdpos).ne'
    (geom_pos (q^d) hmpos).ne', padicValNat.eq_zero_of_not_dvd hgn, add_zero]

lemma component_val_eq_fermat {N P q : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hqmem : q ∈ N.primeFactors) (hqlt : q < P)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hd : P ∣ component N q) :
    padicValNat P (component N q) = padicValNat P (q^(P-1)-1) := by
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hq := Nat.prime_of_mem_primeFactors hqmem
  letI : Fact P.Prime := ⟨hP⟩
  have hp1 : 0 < P - 1 := by have := hP.two_le; omega
  have hqn : (q : ZMod P) ≠ 0 := by
    intro h
    have hdiv := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h
    have := Nat.le_of_dvd hq.pos hdiv
    omega
  have hdorder := ZMod.orderOf_dvd_card_sub_one hqn
  have hpnd : ¬P ∣ P-1 := Nat.not_dvd_of_pos_of_lt hp1 (by omega)
  have hshort := geom_val_eq_short hP hp1 hpnd hdorder (pow_orderOf_eq_one (q : ZMod P))
  have hcomp := component_val_eq_geom_order hP
    (max_not_dvd_exponent hN hodd hP (prime_odd hodd hPmem) hqmem hmax) hd
  have hqm : 0 < q-1 := by have := hq.two_le; omega
  have hqmd : ¬P ∣ q-1 := Nat.not_dvd_of_pos_of_lt hqm (by omega)
  rw [← geom_identity q (P-1) hq.one_lt.le,
    padicValNat.mul (geom_pos q hp1).ne' hqm.ne',
    padicValNat.eq_zero_of_not_dvd hqmd, add_zero, hshort]
  exact hcomp

/-- Two distinct contributions outside orders 3 and 6, or a base-q Wieferich congruence. -/
theorem fourth_power_alternative {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hfour : 4 ≤ N.factorization P) :
    (∃ u ∈ high N P, ∃ v ∈ high N P, u ≠ v ∧ P ∣ component N u ∧ P ∣ component N v) ∨
    (∃ q ∈ high N P, P ∣ component N q ∧ P^2 ∣ q^(P-1)-1) := by
  classical
  have hP := Nat.prime_of_mem_primeFactors hPmem
  letI : Fact P.Prime := ⟨hP⟩
  have hbound := largestPrime_order_bound hN hodd hPmem hmax
  have htwo : 2 ≤ ∑ q ∈ high N P, padicValNat P (component N q) := by omega
  have hex : ∃ u ∈ high N P, 0 < padicValNat P (component N u) := by
    by_contra hh
    push_neg at hh
    have hz : (∑ q ∈ high N P, padicValNat P (component N q)) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have := hh q hq
      omega
    omega
  obtain ⟨u, hu, hup⟩ := hex
  by_cases hv : ∃ v ∈ high N P, v ≠ u ∧ 0 < padicValNat P (component N v)
  · obtain ⟨v, hv, hne, hvp⟩ := hv
    exact Or.inl ⟨u, hu, v, hv, Ne.symm hne,
      dvd_of_one_le_padicValNat hup, dvd_of_one_le_padicValNat hvp⟩
  · have hsum : (∑ q ∈ high N P, padicValNat P (component N q)) =
        padicValNat P (component N u) := by
      apply Finset.sum_eq_single u
      · intro v hv' hne
        by_contra hz
        exact hv ⟨v, hv', hne, Nat.pos_of_ne_zero hz⟩
      · intro hn
        exact False.elim (hn hu)
    rw [hsum] at htwo
    obtain ⟨hum, huP, _, _⟩ := Finset.mem_filter.mp hu
    have hud := dvd_of_one_le_padicValNat hup
    have hf := component_val_eq_fermat hN hodd hPmem hum huP hmax hud
    have hferpos : 0 < u^(P-1)-1 := by
      have huprime := Nat.prime_of_mem_primeFactors hum
      have hP2 := hP.two_le
      have hpow : 1 < u^(P-1) := one_lt_pow₀ huprime.one_lt (by omega)
      omega
    exact Or.inr ⟨u, hu, hud,
      (padicValNat_dvd_iff_le hferpos.ne').mpr (by omega)⟩

/-- If no higher-order component contributes, the largest exponent is one or the rigid paired case. -/
theorem exceptional_pair {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hno : ∀ q ∈ high N P, ¬P ∣ component N q) :
    N.factorization P = 1 ∨
      (N.factorization P = 2 ∧ 3 ∣ N ∧
        ∃ u ∈ sources N P 3, ∃ v ∈ sources N P 3, u ≠ v ∧ u+v+1=P) := by
  classical
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hP2 : P ≠ 2 := by
    intro h
    exact (prime_odd hodd hPmem).not_two_dvd_nat (by simp [h])
  have hzero : (∑ q ∈ high N P, padicValNat P (component N q)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    exact padicValNat.eq_zero_of_not_dvd (hno q hq)
  have hb := largestPrime_order_bound hN hodd hPmem hmax
  rw [hzero] at hb
  have hpos := hP.factorization_pos_of_dvd hN.2.ne' (Nat.dvd_of_mem_primeFactors hPmem)
  by_cases hone : N.factorization P = 1
  · exact Or.inl hone
  right
  have htwo : N.factorization P = 2 := by omega
  refine ⟨htwo, ?_, ?_⟩
  · by_contra hnot3
    have h := largestPrime_order_bound_without_three hN hodd hPmem hmax hnot3
    rw [hzero, htwo] at h
    omega
  · have hbal := valuation_balance hN hP hP2
    rw [valuation_partition hmax, hzero, htwo, zero_add] at hbal
    have hs3 := source_sum_le_card hN hodd hPmem hmax (Or.inl rfl : 3=3 ∨ 3=6)
    have hs6 := source_sum_le_card hN hodd hPmem hmax (Or.inr rfl : 6=3 ∨ 6=6)
    have hc6 := six_sources_card_le_one (P := P) hN hodd
    have hc3 : 1 < (sources N P 3).card := by
      rcases three_or_six_sources_empty hodd hPmem with h | h
      · simp only [h, Finset.sum_empty] at hbal
        omega
      · simp only [h, Finset.sum_empty] at hbal
        omega
    obtain ⟨u, hu, v, hv, hne⟩ := Finset.one_lt_card.mp hc3
    have hu' := mem_sources.mp hu
    have hv' := mem_sources.mp hv
    exact ⟨u, hu, v, hv, hne, three_pair_sum hP hu'.2.1 hv'.2.1 hne hu'.2.2.1 hv'.2.2.1⟩

lemma four_dvd_geom_four {q : ℕ} (hq : Odd q) : 4 ∣ geom q 4 := by
  obtain ⟨k, rfl⟩ := hq
  refine ⟨2*k^3 + 4*k^2 + 3*k + 1, ?_⟩
  simp [geom, Finset.sum_range_succ]
  ring

lemma four_not_dvd_length {N q : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hq : q ∈ N.primeFactors) : ¬4 ∣ N.factorization q + 1 := by
  intro h
  have h4 : 4 ∣ component N q :=
    (four_dvd_geom_four (prime_odd hodd hq)).trans (geom_dvd_geom h)
  have h4N := h4.trans (component_dvd hN hq)
  have h2N : 2 ∣ N := (mul_dvd_mul_iff_left (by decide : (2:ℕ) ≠ 0)).mp h4N
  exact hodd.not_two_dvd_nat h2N

lemma high_order_ne_one_two {N P q : ℕ} (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hq : q ∈ high N P) : ord P q ≠ 1 ∧ ord P q ≠ 2 := by
  classical
  obtain ⟨hqm, hqP, _, _⟩ := Finset.mem_filter.mp hq
  have hP := Nat.prime_of_mem_primeFactors hPmem
  have hqprime := Nat.prime_of_mem_primeFactors hqm
  letI : Fact P.Prime := ⟨hP⟩
  have hne := cast_ne_one_of_lt hP.one_lt hqprime.one_lt hqP
  refine ⟨fun h => hne (orderOf_eq_one_iff.mp h), ?_⟩
  intro htwo
  have hpow : (q : ZMod P)^2 = 1 := by
    have h := pow_orderOf_eq_one (q : ZMod P)
    change (q : ZMod P)^ord P q = 1 at h
    rwa [htwo] at h
  have hmul : ((q : ZMod P)-1)*((q : ZMod P)+1)=0 := by linear_combination hpow
  have h := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  have hdiv : P ∣ q+1 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using h)
  have hle := Nat.le_of_dvd (by omega : 0 < q+1) hdiv
  have hpodd := Nat.odd_iff.mp (prime_odd hodd hPmem)
  have hqodd := Nat.odd_iff.mp (prime_odd hodd hqm)
  omega

/-- Every contributing prime in H has exponent at least 4, or at least 9 if its exponent is odd. -/
theorem high_contributor_exponents {N P q : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hq : q ∈ high N P) (hd : P ∣ component N q) :
    4 ≤ N.factorization q ∧ (Odd (N.factorization q) → 9 ≤ N.factorization q) := by
  classical
  have hq' := Finset.mem_filter.mp hq
  have hne := high_order_ne_one_two hodd hPmem hq
  have hdiv := order_dvd_of_component_dvd hd
  have hpos := Nat.pos_of_dvd_of_pos hdiv (by omega : 0 < N.factorization q+1)
  have hle := Nat.le_of_dvd (by omega : 0 < N.factorization q+1) hdiv
  have hnot4 := four_not_dvd_length hN hodd hq'.1
  have hdnot4 : ord P q ≠ 4 := by
    intro heq
    exact hnot4 (heq ▸ hdiv)
  have he4 : 4 ≤ N.factorization q := by
    have hn3 := hq'.2.2.1
    omega
  refine ⟨he4, ?_⟩
  intro heodd
  by_contra he9
  have hemod := Nat.odd_iff.mp heodd
  have hecases : N.factorization q = 5 ∨ N.factorization q = 7 := by omega
  rcases hecases with he5 | he7
  · rw [he5] at hdiv hle
    have hn3 := hq'.2.2.1
    have hn6 := hq'.2.2.2
    have hd5 : ord P q = 5 := by omega
    rw [hd5] at hdiv
    norm_num at hdiv
  · apply hnot4
    rw [he7]
    decide

end LargestPrimeOrders

