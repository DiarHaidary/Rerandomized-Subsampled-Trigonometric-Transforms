import SRHT
import Solution

/-! Check the public statements and every transitive axiom of the central results. -/
#check RerandomizedSTT.problem_5_6
#check SRHT.two_round_srht_ose
#check SRHT.two_round_srht_norm_failure
#check SRHT.two_round_srht_ose_independent
#check SRHT.rowCount_dimension_linear
#check SRHT.failureOrder_original
#check SRHT.BernoulliGeneral.moment_bound
#check SRHT.BernoulliGeneral.moment_bound_limited
#check SRHT.BernoulliGeneral.tail_bound_limited
#check SRHT.rowCount_log_confidence_capped
#check SRHT.two_round_srht_ose_log_confidence
#check SRHT.AlignmentObstruction.failure_lower
#check SRHT.AlignmentObstruction.necessary_rows
#check SRHT.AlignmentObstruction.two_round_three_quarters
#check SRHT.StrongAlignment.two_round_failure_lower
#check SRHT.GaussianObstruction.exists_dyadic_failure
#check SRHT.GaussianObstruction.no_universal_logarithmic_budget

#print axioms SRHT.two_round_srht_ose
#print axioms RerandomizedSTT.problem_5_6
#print axioms SRHT.two_round_srht_norm_failure
#print axioms SRHT.two_round_srht_ose_independent
#print axioms SRHT.BernoulliMoment.moment_bound
#print axioms SRHT.SmallRows.sign_cutoff_small_rows_norm_le
#print axioms SRHT.BernoulliMoment.compressed_matrix_eq
#print axioms SRHT.ActualMomentTransfer.fixed_to_bernoulli
#print axioms SRHT.ActualMomentTransfer.fixed_sign_moment_match_min
#print axioms SRHT.rowCount_dimension_linear
#print axioms SRHT.BernoulliGeneral.moment_bound
#print axioms SRHT.BernoulliGeneral.moment_bound_limited
#print axioms SRHT.BernoulliGeneral.tail_bound_limited
#print axioms SRHT.BernoulliGeneral.expected_rows
#print axioms SRHT.rowCount_log_confidence_capped
#print axioms SRHT.two_round_srht_ose_log_confidence
#print axioms SRHT.Alignment.tensorWalsh_eq_reindex
#print axioms SRHT.Alignment.horizontal_norm
#print axioms SRHT.Alignment.aligned_probability
#print axioms SRHT.Alignment.evolve_of_aligned
#print axioms SRHT.SupportMiss.miss_probability
#print axioms SRHT.SupportMiss.missRatio_symm
#print axioms SRHT.SupportMiss.missRatio_product
#print axioms SRHT.SupportMiss.missRatio_lower
#print axioms SRHT.AlignmentObstruction.failure_lower
#print axioms SRHT.AlignmentObstruction.necessary_rows
#print axioms SRHT.AlignmentObstruction.two_round_three_quarters
#print axioms SRHT.StrongAlignment.two_round_failure_lower
#print axioms SRHT.GaussianObstruction.exists_dyadic_failure
#print axioms SRHT.GaussianObstruction.no_universal_logarithmic_budget
#print axioms SRHT.PositiveSelector.norm_creation_le
#print axioms SRHT.PositiveSelector.norm_occupancy_le
#print axioms SRHT.PositiveSelector.norm_bernoulliOperator_le_of_sum_norm
