import CubicCofactors

namespace LargestPrimeOrders

open Finset

/-- Smaller prime divisors congruent to 1 mod 3 that occur at least to the fourth power. -/
noncomputable def fourthPrimes (N P : ℕ) : Finset ℕ := by
  classical
  exact N.primeFactors.filter (fun q => q < P ∧ q % 3 = 1 ∧ 4 ≤ N.factorization q)

lemma cubic_distinct_candidates {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hm : P % 3 = 1) :
    ∃ S : Finset ℕ, S.card = padicValNat 3 (N.factorization P+1) ∧
      ∀ q ∈ S, q ∈ N.primeFactors ∧ q < P ∧ q % 3 = 1 ∧ 2 ≤ N.factorization q := by
  classical
  let t := padicValNat 3 (N.factorization P+1)
  have hw : ∀ i : Fin t, ∃ r, r ∈ N.primeFactors ∧ r < P ∧ r % 3 = 1 ∧
      2 ≤ N.factorization r ∧ r ∣ cubicCofactor P i.val := fun i =>
    cubic_cofactor_witness hN hodd hPmem hmax hm i.isLt
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro i j heq
    apply Fin.ext
    by_contra hne
    obtain ⟨him,hiP,himod,hia,hid⟩ := hf i
    obtain ⟨hjm,hjP,hjmod,hja,hjd⟩ := hf j
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [← heq] at hjd
      exact cubic_cofactor_prime_disjoint hm hlt (Nat.prime_of_mem_primeFactors him) hid hjd
    · rw [heq] at hid
      exact cubic_cofactor_prime_disjoint hm hgt (Nat.prime_of_mem_primeFactors hjm) hjd hid
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp [t]
  · intro q hq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hi,hiP,himod,hia,_⟩ := hf i
    exact ⟨hi,hiP,himod,hia⟩

lemma candidate_fourth_or_three_cost {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ N.primeFactors ∧ q < P ∧ q % 3 = 1 ∧ 2 ≤ N.factorization q) :
    S.card ≤ (fourthPrimes N P).card + ∑ q ∈ S, padicValNat 3 (component N q) := by
  classical
  have hpoint : ∀ q ∈ S, 1 ≤ (if 4 ≤ N.factorization q then 1 else 0) +
      padicValNat 3 (component N q) := by
    intro q hq
    obtain ⟨hqm,hqP,hqmod,hqa⟩ := hS q hq
    by_cases h4 : 4 ≤ N.factorization q
    · simp [h4]
    · have hnot4 := four_not_dvd_length hN hodd hqm
      have hne3 : N.factorization q ≠ 3 := by intro h; apply hnot4; rw [h]
      have ha2 : N.factorization q = 2 := by omega
      have hv : padicValNat 3 (component N q) = 1 := by
        have h := geom_three_valuation_one (Nat.prime_of_mem_primeFactors hqm).one_lt
          (show 0 < N.factorization q+1 by omega) hqmod
        simpa [component,ha2,three_val_three] using h
      simp [h4,hv]
  have hsub : S.filter (fun q => 4 ≤ N.factorization q) ⊆ fourthPrimes N P := by
    intro q hq
    obtain ⟨hqs,hq4⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqm,hqP,hqmod,_⟩ := hS q hqs
    exact Finset.mem_filter.mpr ⟨hqm,hqP,hqmod,hq4⟩
  have hcount : (∑ q ∈ S, if 4 ≤ N.factorization q then 1 else 0) =
      (S.filter (fun q => 4 ≤ N.factorization q)).card := by simp [Finset.sum_filter]
  calc
    S.card = ∑ _q ∈ S, (1:ℕ) := by simp
    _ ≤ ∑ q ∈ S, ((if 4 ≤ N.factorization q then 1 else 0) +
        padicValNat 3 (component N q)) := Finset.sum_le_sum hpoint
    _ = (∑ q ∈ S, if 4 ≤ N.factorization q then 1 else 0) +
        ∑ q ∈ S, padicValNat 3 (component N q) := Finset.sum_add_distrib
    _ = (S.filter (fun q => 4 ≤ N.factorization q)).card +
        ∑ q ∈ S, padicValNat 3 (component N q) := by rw [hcount]
    _ ≤ _ := Nat.add_le_add_right (Finset.card_le_card hsub) _

lemma candidate_three_budget {N P e : ℕ} (hN : Nat.Perfect N)
    (hPmem : P ∈ N.primeFactors) (hm : P % 3 = 1)
    (hemem : e ∈ N.primeFactors) (heodd : Odd (N.factorization e))
    (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ N.primeFactors ∧ q < P ∧ q % 3 = 1 ∧ 2 ≤ N.factorization q) :
    padicValNat 3 (N.factorization P+1) + eulerThreeDelta N e +
      (∑ q ∈ S, padicValNat 3 (component N q)) ≤ padicValNat 3 N := by
  classical
  have hPnot : P ∉ S := by intro h; have := (hS P h).2.1; omega
  have hPv : padicValNat 3 (component N P) = padicValNat 3 (N.factorization P+1) :=
    geom_three_valuation_one (Nat.prime_of_mem_primeFactors hPmem).one_lt (by omega) hm
  by_cases he2 : e % 3 = 2
  · have henot : e ∉ S := by intro h; have := (hS e h).2.2.1; omega
    have hPe : P ≠ e := by intro h; subst e; omega
    have hPnot' : P ∉ insert e S := by simp [hPe,hPnot]
    have hsub : insert P (insert e S) ⊆ N.primeFactors := by
      intro q hq
      simp only [Finset.mem_insert] at hq
      rcases hq with rfl | rfl | hq
      · exact hPmem
      · exact hemem
      · exact (hS q hq).1
    have h := Finset.sum_le_sum_of_subset hsub (f := fun q => padicValNat 3 (component N q))
    rw [Finset.sum_insert hPnot',Finset.sum_insert henot,three_valuation_balance hN,
      hPv,euler_delta_component hemem heodd he2] at h
    omega
  · have hsub : insert P S ⊆ N.primeFactors := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hPmem
      · exact (hS q hq).1
    have h := Finset.sum_le_sum_of_subset hsub (f := fun q => padicValNat 3 (component N q))
    rw [Finset.sum_insert hPnot,three_valuation_balance hN,hPv] at h
    simpa [eulerThreeDelta,he2] using h

/-- A count of distinct fourth-power prime divisors, coupled to the 3-adic valuation. -/
theorem fourth_power_budget_euler {N P e : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hm : P % 3 = 1) (hemem : e ∈ N.primeFactors) (heodd : Odd (N.factorization e)) :
    2 * padicValNat 3 (N.factorization P+1) + eulerThreeDelta N e ≤
      padicValNat 3 N + (fourthPrimes N P).card := by
  obtain ⟨S,hcard,hS⟩ := cubic_distinct_candidates hN hodd hPmem hmax hm
  have hc := candidate_fourth_or_three_cost hN hodd S hS
  have hb := candidate_three_budget hN hPmem hm hemem heodd S hS
  omega

/-- The fourth-power count without naming the Euler prime. -/
theorem fourth_power_budget {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hm : P % 3 = 1) :
    2 * padicValNat 3 (N.factorization P+1) ≤ padicValNat 3 N + (fourthPrimes N P).card := by
  obtain ⟨e,he,_⟩ := exists_unique_odd_exponent_prime hN hodd
  have h := fourth_power_budget_euler hN hodd hPmem hmax hm he.1 he.2
  omega

/-- When the earlier 3-adic budget is saturated, all t tower levels force fourth powers. -/
theorem saturated_fourth_power_count {N P e : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hm : P % 3 = 1) (hemem : e ∈ N.primeFactors) (heodd : Odd (N.factorization e))
    (hsat : padicValNat 3 N = padicValNat 3 (N.factorization P+1) + eulerThreeDelta N e) :
    padicValNat 3 (N.factorization P+1) ≤ (fourthPrimes N P).card := by
  have h := fourth_power_budget_euler hN hodd hPmem hmax hm hemem heodd
  omega

/-- The exponent-8 case now forces two distinct fourth-power primes whenever W is only 7. -/
theorem eighth_power_fourth_power_dichotomy {N P : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (h3 : N.factorization 3 = 2) (h8 : N.factorization P = 8) :
    highWeight N P = 8 ∨ (highWeight N P = 7 ∧ 2 ≤ (fourthPrimes N P).card) := by
  have hw := eighth_power_refinement hN hodd hPmem hmax h3 h8
  have hbal := weight_balance hN hodd hPmem hmax
  by_cases heq : highWeight N P = 8
  · exact Or.inl heq
  right
  have h7 : highWeight N P = 7 := by omega
  refine ⟨h7, ?_⟩
  have hm := low_positive_mod_three (N := N) (Nat.prime_of_mem_primeFactors hPmem) (by omega)
  have h := fourth_power_budget hN hodd hPmem hmax hm
  have hb : padicValNat 3 N = 2 := by rwa [Nat.factorization_def N (by decide : Nat.Prime 3)] at h3
  have ht : padicValNat 3 (N.factorization P+1) = 2 := by simpa [h8] using three_val_nine
  omega

end LargestPrimeOrders
