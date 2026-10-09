import CyclotomicUpper

namespace LargestPrimeOrders

open Finset

/-- The sum of integer logarithms of the relevant cyclotomic values. -/
noncomputable def logarithmicCapacity (N P : ℕ) : ℕ :=
  ∑ q ∈ highContributors N P, Nat.log P (cycloValue q (ord P q))

/-- The sum of the corresponding cyclotomic degree caps. -/
noncomputable def totientCapacity (N P : ℕ) : ℕ :=
  ∑ q ∈ highContributors N P, (Nat.totient (ord P q)-1)

/-- The uniform cap obtained from an odd factor m of P-1. -/
noncomputable def oddPartCapacity (N P m : ℕ) : ℕ :=
  (highContributors N P).card * (Nat.totient m-1)

lemma totientCapacity_le_oddPartCapacity {N P m s : ℕ}
    (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hm : 0 < m)
    (hfactor : P-1 = 2^s*m) :
    totientCapacity N P ≤ oddPartCapacity N P m := by
  have hp := Nat.prime_of_mem_primeFactors hPmem
  letI : Fact P.Prime := ⟨hp⟩
  unfold totientCapacity oddPartCapacity
  calc
    (∑ q ∈ highContributors N P, (Nat.totient (ord P q)-1))
        ≤ ∑ _q ∈ highContributors N P, (Nat.totient m-1) := by
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

/-- A compiled combination of the Euler 3-adic lower bound and all three upper caps. -/
theorem combined_inequality {N P e m s : ℕ} (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hemem : e ∈ N.primeFactors) (heodd : Odd (N.factorization e))
    (hm : 0 < m) (hfactor : P-1 = 2^s*m) :
    N.factorization P - threeAllowance (padicValNat 3 N)
      (padicValNat 3 (N.factorization P+1)+eulerThreeDelta N e) ≤ highWeight N P ∧
    highWeight N P ≤ min (N.factorization P) (logarithmicCapacity N P) ∧
    logarithmicCapacity N P ≤ totientCapacity N P ∧
    totientCapacity N P ≤ oddPartCapacity N P m := by
  have hbalance := weight_balance hN hodd hPmem hmax
  have htrivial : highWeight N P ≤ N.factorization P := by omega
  exact ⟨euler_three_adic_refinement hN hodd hPmem hmax hemem heodd,
    le_min htrivial (highWeight_log_upper hN hodd hPmem hmax),
    logarithmic_bound_le_totient_bound hodd hPmem,
    totientCapacity_le_oddPartCapacity hN hodd hPmem hm hfactor⟩

/-- The two endpoints yield a necessary restriction on the largest-prime exponent. -/
theorem combined_exponent_constraint {N P e m s : ℕ}
    (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hemem : e ∈ N.primeFactors) (heodd : Odd (N.factorization e))
    (hm : 0 < m) (hfactor : P-1 = 2^s*m) :
    N.factorization P ≤
      threeAllowance (padicValNat 3 N)
        (padicValNat 3 (N.factorization P+1)+eulerThreeDelta N e) +
      oddPartCapacity N P m := by
  obtain ⟨hl, hu, hlog, htot⟩ :=
    combined_inequality hN hodd hPmem hmax hemem heodd hm hfactor
  have hcap := (hu.trans (min_le_right _ _)).trans (hlog.trans htot)
  omega

/-- The exponent restriction needs no separately assumed Euler prime. -/
theorem exists_combined_exponent_constraint {N P m s : ℕ}
    (hN : Nat.Perfect N) (hodd : Odd N)
    (hPmem : P ∈ N.primeFactors) (hmax : ∀ q ∈ N.primeFactors, q ≤ P)
    (hm : 0 < m) (hfactor : P-1 = 2^s*m) :
    ∃ e ∈ N.primeFactors, Odd (N.factorization e) ∧
      N.factorization P ≤
        threeAllowance (padicValNat 3 N)
          (padicValNat 3 (N.factorization P+1)+eulerThreeDelta N e) +
        oddPartCapacity N P m := by
  obtain ⟨e,he,_⟩ := exists_unique_odd_exponent_prime hN hodd
  exact ⟨e,he.1,he.2,
    combined_exponent_constraint hN hodd hPmem hmax he.1 he.2 hm hfactor⟩

end LargestPrimeOrders
