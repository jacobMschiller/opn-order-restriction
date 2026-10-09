import ThreeAdicRefinement

namespace LargestPrimeOrders

open Finset

/-- The refined Euler bound with existence of the Euler prime discharged. -/
theorem exists_euler_three_adic_refinement {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P) :
    ∃ e, e ∈ N.primeFactors ∧ Odd (N.factorization e) ∧
      N.factorization P - threeAllowance (padicValNat 3 N)
        (padicValNat 3 (N.factorization P+1) + eulerThreeDelta N e) ≤ highWeight N P := by
  obtain ⟨e,he,_⟩ := exists_unique_odd_exponent_prime hN hodd
  exact ⟨e,he.1,he.2,euler_three_adic_refinement hN hodd hPmem hmax he.1 he.2⟩

lemma three_val_nine : padicValNat 3 9 = 2 := by
  change padicValNat 3 (3^2) = 2
  exact padicValNat.prime_pow 2

lemma three_val_three : padicValNat 3 3 = 1 := padicValNat_self

/-- If 3^2 exactly divides N and P^8 exactly divides N, the high-order contribution is at least 7. -/
theorem eighth_power_refinement {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (h3 : N.factorization 3 = 2) (h8 : N.factorization P = 8) :
    7 ≤ highWeight N P := by
  have hb : padicValNat 3 N = 2 := by
    rwa [Nat.factorization_def N (by decide : Nat.Prime 3)] at h3
  have h := three_adic_refinement hN hodd hPmem hmax
  simpa [h8, hb, three_val_nine, threeAllowance] using h

/-- In the same case, an Euler prime congruent to 2 mod 3 forces all eight contributions into H. -/
theorem eighth_power_euler_refinement {N P e : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (h3 : N.factorization 3 = 2) (h8 : N.factorization P = 8)
    (hemem : e ∈ N.primeFactors) (heodd : Odd (N.factorization e)) (he2 : e % 3 = 2) :
    highWeight N P = 8 := by
  have hb : padicValNat 3 N = 2 := by
    rwa [Nat.factorization_def N (by decide : Nat.Prime 3)] at h3
  have hed : 3 ∣ e+1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hev := one_le_padicValNat_of_dvd (p := 3) (by omega : 0 < e+1) hed
  have hdelta : 1 ≤ eulerThreeDelta N e := by simp only [eulerThreeDelta, if_pos he2]; omega
  have hlt : 2 < 2 + eulerThreeDelta N e := by omega
  have h := euler_three_adic_refinement hN hodd hPmem hmax hemem heodd
  have hbound : 8 ≤ highWeight N P := by
    simpa [h8, hb, three_val_nine, threeAllowance, hlt] using h
  have hbal := weight_balance hN hodd hPmem hmax
  omega

/-- When 3 does not divide N and P has exponent 2, both units of valuation come from H. -/
theorem no_three_square_highWeight {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hnot3 : ¬3 ∣ N) (h2 : N.factorization P = 2) : highWeight N P = 2 := by
  have hb : padicValNat 3 N = 0 := padicValNat.eq_zero_of_not_dvd hnot3
  have h := three_adic_refinement hN hodd hPmem hmax
  have hbound : 2 ≤ highWeight N P := by
    simpa [h2, hb, three_val_three, threeAllowance] using h
  have hbal := weight_balance hN hodd hPmem hmax
  omega

lemma alternative_of_two_high_units {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (htwo : 2 ≤ highWeight N P) :
    (∃ u ∈ high N P, ∃ v ∈ high N P, u ≠ v ∧ P ∣ component N u ∧ P ∣ component N v) ∨
    (∃ q ∈ high N P, P ∣ component N q ∧ P^2 ∣ q^(P-1)-1) := by
  classical
  have hP := Nat.prime_of_mem_primeFactors hPmem
  letI : Fact P.Prime := ⟨hP⟩
  unfold highWeight at htwo
  have hex : ∃ u ∈ high N P, 0 < padicValNat P (component N u) := by
    by_contra hh
    push_neg at hh
    have hz : (∑ q ∈ high N P, padicValNat P (component N q)) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have := hh q hq
      omega
    omega
  obtain ⟨u,hu,hup⟩ := hex
  by_cases hv : ∃ v ∈ high N P, v ≠ u ∧ 0 < padicValNat P (component N v)
  · obtain ⟨v,hv,hne,hvp⟩ := hv
    exact Or.inl ⟨u,hu,v,hv,Ne.symm hne,
      dvd_of_one_le_padicValNat hup,dvd_of_one_le_padicValNat hvp⟩
  · have hsum : (∑ q ∈ high N P, padicValNat P (component N q)) =
        padicValNat P (component N u) := by
      apply Finset.sum_eq_single u
      · intro v hv' hne
        by_contra hz
        exact hv ⟨v,hv',hne,Nat.pos_of_ne_zero hz⟩
      · intro hn
        exact False.elim (hn hu)
    rw [hsum] at htwo
    obtain ⟨hum,huP,_,_⟩ := Finset.mem_filter.mp hu
    have hud := dvd_of_one_le_padicValNat hup
    have hf := component_val_eq_fermat hN hodd hPmem hum huP hmax hud
    have hferpos : 0 < u^(P-1)-1 := by
      have huprime := Nat.prime_of_mem_primeFactors hum
      have hP2 := hP.two_le
      have hpow : 1 < u^(P-1) := one_lt_pow₀ huprime.one_lt (by omega)
      omega
    exact Or.inr ⟨u,hu,hud,(padicValNat_dvd_iff_le hferpos.ne').mpr (by omega)⟩

/-- The two-contributor or Wieferich alternative at exponent 2, including the fourth-power condition. -/
theorem no_three_square_alternative {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hnot3 : ¬3 ∣ N) (h2 : N.factorization P = 2) :
    (∃ u ∈ high N P, ∃ v ∈ high N P, u ≠ v ∧
      P ∣ component N u ∧ P ∣ component N v ∧ 4 ≤ N.factorization u ∧ 4 ≤ N.factorization v) ∨
    (∃ q ∈ high N P, P ∣ component N q ∧ P^2 ∣ q^(P-1)-1 ∧ 4 ≤ N.factorization q) := by
  have htwo : 2 ≤ highWeight N P := by
    rw [no_three_square_highWeight hN hodd hPmem hmax hnot3 h2]
  rcases alternative_of_two_high_units hN hodd hPmem hmax htwo with h | h
  · obtain ⟨u,hu,v,hv,hne,hud,hvd⟩ := h
    exact Or.inl ⟨u,hu,v,hv,hne,hud,hvd,
      (high_contributor_exponents hN hodd hPmem hu hud).1,
      (high_contributor_exponents hN hodd hPmem hv hvd).1⟩
  · obtain ⟨q,hq,hqd,hqf⟩ := h
    exact Or.inr ⟨q,hq,hqd,hqf,(high_contributor_exponents hN hodd hPmem hq hqd).1⟩

end LargestPrimeOrders
