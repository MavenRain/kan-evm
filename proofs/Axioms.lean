-- Axiom report for completed finite-fragment inventory theorems and public corollaries.
import KanEvmProofs.Canonical
import KanEvmProofs.Budget
import KanEvmProofs.Weakening
import KanEvmProofs.Checker
import KanEvmProofs.Substitution
import KanEvmProofs.Evaluation
import KanEvmProofs.EvalSubst
import KanEvmProofs.NormalizeCore
import KanEvmProofs.NormalizeTyping
import KanEvmProofs.NormalizeAgree

#print axioms ty_canonical
#print axioms canonical_beq_iff
#print axioms budget_monotone_check
#print axioms budget_monotone_shift
#print axioms budget_monotone_sub
#print axioms budget_monotone_evaluate
#print axioms budget_monotone_reduce
#print axioms check_gas_irrelevant
#print axioms check_cost_exact
#print axioms reduce_step_charge
#print axioms check_sound
#print axioms check_complete
#print axioms check_error_not_typable
#print axioms check_error_choice_varies
#print axioms weakening_shift
#print axioms substitution_at_depth
#print axioms substitution_zero
#print axioms substitute_budget_sufficient
#print axioms evaluate_preserves_type
#print axioms run_never_expected_shape
#print axioms run_budget_two_size
#print axioms shift_preserves_value
#print axioms evaluate_sub_env
#print axioms evaluate_sub_budget_gap
#print axioms reduce_gas_irrelevant
#print axioms reduce_gas_unused
#print axioms reduce_fuel_irrelevant
#print axioms reduce_preserves_type
#print axioms normalize_is_check_then_reduce
#print axioms reduce_normal_form
#print axioms normalize_preserves_type
#print axioms normalize_output_checks
#print axioms normalize_normal_form
#print axioms normalize_agrees_with_run
