import CombinedBounds

/-!
This file checks the public statements and reports their axiom dependencies.
No number-theoretic conjecture or unproved local lemma is an axiom.
-/

open LargestPrimeOrders

#check largestPrime_order_bound
#check largestPrime_order_bound_without_three
#check low_order_contribution_bound
#check low_order_contribution_bound_without_three
#check fourth_power_alternative
#check exceptional_pair
#check high_contributor_exponents

#print axioms LargestPrimeOrders.largestPrime_order_bound
#print axioms LargestPrimeOrders.largestPrime_order_bound_without_three
#print axioms LargestPrimeOrders.low_order_contribution_bound
#print axioms LargestPrimeOrders.low_order_contribution_bound_without_three
#print axioms LargestPrimeOrders.fourth_power_alternative
#print axioms LargestPrimeOrders.exceptional_pair
#print axioms LargestPrimeOrders.high_contributor_exponents

-- The new 3-adic and Euler-prime refinements.
#check three_adic_refinement
#check euler_three_adic_refinement
#check exists_unique_odd_exponent_prime
#check exists_euler_three_adic_refinement
#check eighth_power_refinement
#check eighth_power_euler_refinement
#check no_three_square_highWeight
#check no_three_square_alternative

#print axioms LargestPrimeOrders.three_adic_refinement
#print axioms LargestPrimeOrders.euler_three_adic_refinement
#print axioms LargestPrimeOrders.exists_unique_odd_exponent_prime
#print axioms LargestPrimeOrders.exists_euler_three_adic_refinement
#print axioms LargestPrimeOrders.eighth_power_refinement
#print axioms LargestPrimeOrders.eighth_power_euler_refinement
#print axioms LargestPrimeOrders.no_three_square_highWeight
#print axioms LargestPrimeOrders.no_three_square_alternative

-- The distinct fourth-power prime-divisor refinement.
#check cubic_distinct_candidates
#check fourth_power_budget_euler
#check fourth_power_budget
#check saturated_fourth_power_count
#check eighth_power_fourth_power_dichotomy

#print axioms LargestPrimeOrders.cubic_distinct_candidates
#print axioms LargestPrimeOrders.fourth_power_budget_euler
#print axioms LargestPrimeOrders.fourth_power_budget
#print axioms LargestPrimeOrders.saturated_fourth_power_count
#print axioms LargestPrimeOrders.eighth_power_fourth_power_dichotomy

-- Upper bounds from cyclotomic values, degrees, and the odd part of P-1.
#check component_val_eq_cycloValue
#check high_component_totient_upper
#check highWeight_log_upper
#check logarithmic_bound_le_totient_bound
#check highWeight_totient_upper
#check highWeight_odd_part_upper
#check largest_exponent_totient_upper
#check highWeight_eq_card_of_no_wieferich

#print axioms LargestPrimeOrders.component_val_eq_cycloValue
#print axioms LargestPrimeOrders.high_component_totient_upper
#print axioms LargestPrimeOrders.highWeight_log_upper
#print axioms LargestPrimeOrders.logarithmic_bound_le_totient_bound
#print axioms LargestPrimeOrders.highWeight_totient_upper
#print axioms LargestPrimeOrders.highWeight_odd_part_upper
#print axioms LargestPrimeOrders.largest_exponent_totient_upper
#print axioms LargestPrimeOrders.highWeight_eq_card_of_no_wieferich

-- The complete combined interval and its consequence for the largest exponent.
#check combined_inequality
#check combined_exponent_constraint
#check exists_combined_exponent_constraint

#print axioms LargestPrimeOrders.combined_inequality
#print axioms LargestPrimeOrders.combined_exponent_constraint
#print axioms LargestPrimeOrders.exists_combined_exponent_constraint
