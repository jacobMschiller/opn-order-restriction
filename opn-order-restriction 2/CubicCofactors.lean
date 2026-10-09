import RefinementConsequences

namespace LargestPrimeOrders

open Finset

/-- Phi_(3^(j+1))(P), with its single factor of 3 removed. -/
def cubicCofactor (P j : ℕ) : ℕ := phi3 (P^(3^j)) / 3

lemma cubic_cofactor_arithmetic {P : ℕ} (hm : P % 3 = 1) (j : ℕ) :
    phi3 (P^(3^j)) = 3 * cubicCofactor P j ∧ cubicCofactor P j % 3 = 1 := by
  have hx : P^(3^j) % 3 = 1 := by simp [Nat.pow_mod, hm]
  obtain ⟨k,hk⟩ : ∃ k, P^(3^j) = 3*k+1 := ⟨P^(3^j)/3, by omega⟩
  have hf : phi3 (P^(3^j)) = 3 * (3*k^2+3*k+1) := by rw [phi3,hk]; ring
  have hc : cubicCofactor P j = 3*k^2+3*k+1 := by simp [cubicCofactor,hf]
  constructor
  · simpa [hc] using hf
  · simp [hc, Nat.add_mod, Nat.mul_mod]

lemma cubic_cofactor_gt {P : ℕ} (hP : 1 < P) (hm : P % 3 = 1) (j : ℕ) :
    P < cubicCofactor P j := by
  have hpow : P ≤ P^(3^j) := Nat.le_self_pow (by positivity) P
  have hx2 : 2 ≤ P^(3^j) := by omega
  have hs := Nat.mul_le_mul_left (P^(3^j)) hx2
  have hf := (cubic_cofactor_arithmetic hm j).1
  unfold phi3 at hf
  nlinarith

lemma cubic_cofactor_dvd_component {N P j : ℕ}
    (hm : P % 3 = 1) (hj : j < padicValNat 3 (N.factorization P+1)) :
    cubicCofactor P j ∣ component N P := by
  have hd3 : 3^(j+1) ∣ N.factorization P+1 :=
    (pow_dvd_pow 3 (by omega)).trans pow_padicValNat_dvd
  have hf : phi3 (P^(3^j)) ∣ geom P (3^(j+1)) := by
    rw [pow_succ, geom_mul, geom_three]
    exact dvd_mul_left _ _
  have hc : cubicCofactor P j ∣ phi3 (P^(3^j)) := by
    rw [(cubic_cofactor_arithmetic hm j).1]
    exact dvd_mul_left _ _
  exact hc.trans (hf.trans (geom_dvd_geom hd3))

lemma cubic_cofactor_dvd_number {N P j : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hm : P % 3 = 1)
    (hj : j < padicValNat 3 (N.factorization P+1)) : cubicCofactor P j ∣ N := by
  have hfodd : Odd (phi3 (P^(3^j))) := by
    rw [← geom_three]
    exact geom_odd (prime_odd hodd hPmem).pow (by decide)
  rw [(cubic_cofactor_arithmetic hm j).1, Nat.odd_mul] at hfodd
  have hcop : Nat.Coprime (cubicCofactor P j) 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hfodd.2.not_two_dvd_nat).symm
  exact hcop.dvd_of_dvd_mul_left
    ((cubic_cofactor_dvd_component hm hj).trans (component_dvd hN hPmem))

lemma phi3_prime_order {r x : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hd : r ∣ phi3 x) : orderOf (x : ZMod r) = 3 := by
  letI : Fact r.Prime := ⟨hr⟩
  have hf : (x : ZMod r)^2 + x + 1 = 0 := by
    have h := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    simpa [phi3] using h
  have hx1 : (x : ZMod r) ≠ 1 := by
    intro h
    rw [h] at hf
    have h3 : (3 : ZMod r) = 0 := by linear_combination hf
    have hd3 := (ZMod.natCast_zmod_eq_zero_iff_dvd 3 r).mp h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 3)).mp hd3)
  have hp : (x : ZMod r)^3 = 1 := by linear_combination ((x : ZMod r)-1)*hf
  have ho := orderOf_dvd_of_pow_eq_one hp
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp ho with h | h
  · exact False.elim (hx1 (orderOf_eq_one_iff.mp h))
  · exact h

lemma cubic_cofactor_prime_mod_three {P j r : ℕ} (hm : P % 3 = 1)
    (hr : r.Prime) (hd : r ∣ cubicCofactor P j) : r % 3 = 1 := by
  letI : Fact r.Prime := ⟨hr⟩
  have hr3 : r ≠ 3 := by
    intro h
    subst r
    have h0 := Nat.mod_eq_zero_of_dvd hd
    have h1 := (cubic_cofactor_arithmetic hm j).2
    omega
  have hf : r ∣ phi3 (P^(3^j)) := by
    rw [(cubic_cofactor_arithmetic hm j).1]
    exact dvd_mul_of_dvd_right hd 3
  have ho := phi3_prime_order hr hr3 hf
  have hx : ((P^(3^j) : ℕ) : ZMod r) ≠ 0 := by
    intro h
    have hp := pow_orderOf_eq_one ((P^(3^j) : ℕ) : ZMod r)
    rw [ho,h] at hp
    norm_num at hp
  have hord := ZMod.orderOf_dvd_card_sub_one hx
  rw [ho] at hord
  have := Nat.mod_eq_zero_of_dvd hord
  have := hr.two_le
  omega

lemma cubic_cofactor_prime_lt {N P j r : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hm : P % 3 = 1) (hj : j < padicValNat 3 (N.factorization P+1))
    (hr : r.Prime) (hd : r ∣ cubicCofactor P j) : r ∈ N.primeFactors ∧ r < P := by
  have hP := Nat.prime_of_mem_primeFactors hPmem
  letI : Fact P.Prime := ⟨hP⟩
  have hrmem := Nat.mem_primeFactors.mpr
    ⟨hr,hd.trans (cubic_cofactor_dvd_number hN hodd hPmem hm hj),hN.2.ne'⟩
  have hrne : r ≠ P := by
    intro h
    subst r
    have hv := one_le_padicValNat_of_dvd (component_pos N P)
      (hd.trans (cubic_cofactor_dvd_component hm hj))
    rw [self_component_val_zero] at hv
    omega
  exact ⟨hrmem,lt_of_le_of_ne (hmax r hrmem) hrne⟩

/-- A divisor larger than the largest prime cannot be supported only at exponent-one primes. -/
lemma large_divisor_has_repeated_prime {N P C : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hmax : ∀ q ∈ N.primeFactors, q ≤ P) (hC : C ∣ N) (hbig : P < C) :
    ∃ r ∈ C.primeFactors, 2 ≤ N.factorization r := by
  classical
  obtain ⟨e,he,hunique⟩ := exists_unique_odd_exponent_prime hN hodd
  have hep := Nat.prime_of_mem_primeFactors he.1
  have hC0 : C ≠ 0 := by omega
  have hfac := (Nat.factorization_le_iff_dvd hC0 hN.2.ne').mpr hC
  by_contra h
  push_neg at h
  have hCe : C ∣ e := (Nat.factorization_le_iff_dvd hC0 hep.ne_zero).mp (by
    intro r
    by_cases hr : r ∈ C.primeFactors
    · have hrp := Nat.prime_of_mem_primeFactors hr
      have hrN := Nat.mem_primeFactors.mpr
        ⟨hrp,(Nat.dvd_of_mem_primeFactors hr).trans hC,hN.2.ne'⟩
      have hpos := hrp.factorization_pos_of_dvd hN.2.ne' (Nat.dvd_of_mem_primeFactors hrN)
      have ha : N.factorization r = 1 := by have := h r hr; omega
      have hre := hunique r ⟨hrN, by simp [ha]⟩
      subst r
      have hle : C.factorization e ≤ 1 := by have := hfac e; omega
      simpa [hep.factorization] using hle
    · have hz : C.factorization r = 0 := Finsupp.not_mem_support_iff.mp (by simpa using hr)
      simp [hz])
  have hle := Nat.le_of_dvd hep.pos hCe
  have := hmax e he.1
  omega

lemma cubic_cofactor_witness {N P j : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hm : P % 3 = 1) (hj : j < padicValNat 3 (N.factorization P+1)) :
    ∃ r, r ∈ N.primeFactors ∧ r < P ∧ r % 3 = 1 ∧
      2 ≤ N.factorization r ∧ r ∣ cubicCofactor P j := by
  obtain ⟨r,hr,ha⟩ := large_divisor_has_repeated_prime hN hodd hmax
    (cubic_cofactor_dvd_number hN hodd hPmem hm hj)
    (cubic_cofactor_gt (Nat.prime_of_mem_primeFactors hPmem).one_lt hm j)
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrd := Nat.dvd_of_mem_primeFactors hr
  have hmem := cubic_cofactor_prime_lt hN hodd hPmem hmax hm hj hrp hrd
  exact ⟨r,hmem.1,hmem.2,cubic_cofactor_prime_mod_three hm hrp hrd,ha,hrd⟩

/-- Different levels of the cubic tower share no prime divisor after removing 3. -/
lemma cubic_cofactor_prime_disjoint {P i j r : ℕ} (hm : P % 3 = 1)
    (hij : i < j) (hr : r.Prime) (hi : r ∣ cubicCofactor P i)
    (hj : r ∣ cubicCofactor P j) : False := by
  letI : Fact r.Prime := ⟨hr⟩
  have hrmod := cubic_cofactor_prime_mod_three hm hr hi
  have hr3 : r ≠ 3 := by intro h; subst r; norm_num at hrmod
  have hfi : r ∣ phi3 (P^(3^i)) := by
    rw [(cubic_cofactor_arithmetic hm i).1]
    exact dvd_mul_of_dvd_right hi 3
  have hfj : r ∣ phi3 (P^(3^j)) := by
    rw [(cubic_cofactor_arithmetic hm j).1]
    exact dvd_mul_of_dvd_right hj 3
  have ho := phi3_prime_order hr hr3 hfi
  have hpi : (P : ZMod r)^(3^(i+1)) = 1 := by
    rw [pow_succ, pow_mul]
    have h := pow_orderOf_eq_one ((P^(3^i) : ℕ) : ZMod r)
    rw [ho] at h
    simpa using h
  have hdiv : 3^(i+1) ∣ 3^j := pow_dvd_pow 3 (by omega)
  obtain ⟨m,hmul⟩ := hdiv
  have hpj : (P : ZMod r)^(3^j) = 1 := by rw [hmul,pow_mul,hpi,one_pow]
  have hcast := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hfj
  have hf : ((P : ZMod r)^(3^j))^2 + (P : ZMod r)^(3^j) + 1 = 0 := by
    simpa [phi3] using hcast
  rw [hpj] at hf
  have h3 : (3 : ZMod r) = 0 := by linear_combination hf
  exact hr3 ((Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 3)).mp
    ((ZMod.natCast_zmod_eq_zero_iff_dvd 3 r).mp h3))

end LargestPrimeOrders
