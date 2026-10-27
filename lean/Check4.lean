-- Check4.lean (part 4): cited declarations added 2026-10-19 (cov_assume, cov_split, sites_only, d1_guarded rounds 4-6, d1_residual, reviewer/prosecutor work files). Separate environment from Check1-3.
import CaT1
import CaT2d
import CsA1
import CsA2
import DrEquiv
import DrFamily2
import DrMargin
import DrPath4
import DrRed1
import GdGapAll
import GdGen5
import GdGen6
import GdGen9
import GdH1
import GdR5a
import GdR5b
import GdR6a
import GdR6b
import GdSG3
import GdV
import ProbeA
import SoA1
import SoA2
import SoA3
import SoPar
import SolR345Audit
import SolR6Audit
import SolR6Residual
import SolR6Witness
import SolSitesAffine
import Erratum126Slim

#print axioms CovAssume.P428Target8NCWDHcov  -- cov-def
#print axioms CovAssume.FamilyTorusCovConstAt  -- cov-fam-def
#print axioms CovAssume.FamilyTorusSitesConstAt  -- cov-sites-def
#print axioms CovAssume.p428Target8NCWDHcov_of_total  -- cov-t1
#print axioms CovAssume.familyTorusCovAt_of_proved  -- cov-t1-fam
#print axioms CovAssume.familyTorusCovConstAt_of_proved  -- cov-t1-const
#print axioms CovAssume.covSitesF_two  -- cov-sites-two
#print axioms CovAssume.constFam_witness_two_sites  -- cov-witness-sites
#print axioms CovAssume.covPlaq_separately_necessary_two  -- cov-plaq-necessary-two
#print axioms probe_sep  -- cov-sep
#print axioms AdalyFormal.D1Guarded.genFormS_eq_loc  -- d1g-eq-loc
#print axioms AdalyFormal.D1Guarded.Qs_injective_twist  -- d1g-qs-inj
#print axioms AdalyFormal.D1Guarded.Fth_theta_apply_eq  -- d1g-fth-apply
#print axioms AdalyFormal.D1Guarded.GapAt_twist  -- d1g-gap-twist
#print axioms AdalyFormal.D1Guarded.InstIneqSG2_twist  -- d1g-sg2-twist
#print axioms AdalyFormal.D1Guarded.InstIneqSG2_general  -- d1g-sg2-general
#print axioms AdalyFormal.D1Guarded.GuardResidual  -- d1g-residual-old
#print axioms AdalyFormal.D1Guarded.GuardResidualT  -- d1g-residualT
#print axioms AdalyFormal.D1Guarded.P428Target8SG_iff_residualT  -- d1g-iff-residualT
#print axioms AdalyFormal.D1Guarded.residualT_of_P428Target8SG  -- d1g-residualT-fwd
#print axioms AdalyFormal.D1Guarded.InstIneqS_of_no_testfield  -- d1g-no-testfield
#print axioms AdalyFormal.D1Guarded.Fth_zero_isUnit  -- d1g-fth-zero
#print axioms AdalyFormal.D1Guarded.Fth_isUnit_near_zero  -- d1g-fth-near
#print axioms AdalyFormal.D1Guarded.nv_guard_nonvacuous  -- d1g-nv-guard
#print axioms SolR345Audit.full_guard_literal  -- d1g-sol-fullguard
#print axioms SolR345Audit.no_testfield_iff_zero  -- d1g-sol-notestfield
#print axioms CovSplit.covPlaqF_imp_covSitesF  -- cov-incidence
#print axioms CovSplit.familyTorusPlaqConstAt_iff_cov  -- cov-plaq-iff
#print axioms CovSplit.familyTorusPlaqConstAt_holds  -- cov-plaq-holds
#print axioms CovSplit.classCoupledF_iff_plaq  -- cov-class-iff
#print axioms CovSplit.familyTorusSitesConstAt_imp_cov  -- cov-sites-imp-cov
#print axioms CovSplit.plaq_witness_full_not_plaq  -- cov-plaq-witness
#print axioms CovSplit.split_table_two  -- cov-split-two
#print axioms CovSplit.split_table_ge_three  -- cov-split-ge3
#print axioms CovSplit.sites_not_imp_plaq  -- cov-sites-not-plaq
#print axioms AdalyFormal.D1Guarded.G1inv_diff_eq  -- d1g-diff-eq
#print axioms AdalyFormal.D1Guarded.domination_fails_pi  -- d1g-dom-pi
#print axioms AdalyFormal.D1Guarded.Delta2_eq_zero_of_Jperp  -- d1g-delta2-jperp
#print axioms AdalyFormal.D1Guarded.JfS_vanish_base  -- d1g-jfs-base
#print axioms AdalyFormal.D1Guarded.G1invS_eq_Ginv_base  -- d1g-g1inv-base
#print axioms AdalyFormal.D1Guarded.SG_on_base_flat_family  -- d1g-sg-base
#print axioms SolR6Audit.corrected_domination_fails_pi  -- d1g-sol-corrdom
#print axioms SolR6Residual.delta_eq_with_only_literal_Ginv  -- d1g-sol-delta-lit
#print axioms SolR6Witness.nv_non_twist_guard  -- d1g-sol-nvtwist
#print axioms AdalyFormal.SitesOnly.not_familyTorusSitesConstAt_S  -- so-neg-S
#print axioms AdalyFormal.SitesOnly.not_familyTorusSitesConstAt_div  -- so-neg-div
#print axioms AdalyFormal.SitesOnly.sites_only_table_even  -- so-table-even
#print axioms AdalyFormal.SitesOnly.sites_not_imp_plaq_S  -- so-sites-not-plaq
#print axioms AdalyFormal.SitesOnly.no_uniform_step_blockzero_odd  -- so-odd-step
#print axioms AdalyFormal.SitesOnly.no_nearby_tau_odd  -- so-odd-nearby
#print axioms SolSitesAffine.fixed_branch_no_nearby  -- so-fixed-branch
#print axioms AdalyFormal.D1Residual.G1inv_lit_eq_pencil  -- d1r-pencil-eq
#print axioms AdalyFormal.D1Residual.GuardPencilT  -- d1r-guardpencil
#print axioms AdalyFormal.D1Residual.residualT_iff_pencilT  -- d1r-iff-residual
#print axioms AdalyFormal.D1Residual.P428Target8SG_iff_pencilT  -- d1r-iff-sg
#print axioms AdalyFormal.D1Residual.exterior_path_separation_unit  -- d1r-ext-sep
#print axioms AdalyFormal.D1Residual.SepPathFamily2  -- d1r-def-sep2
#print axioms AdalyFormal.D1Residual.not_GuardResidualT_of_sep2  -- d1r-not-residual
#print axioms AdalyFormal.D1Residual.not_P428Target8SG_of_sep2  -- d1r-not-sg
#print axioms AdalyFormal.D1Residual.G1inv_lit_isUnit_of_margin  -- d1r-margin
#print axioms Erratum126Slim.norm_delta124_le_Lfree  -- erratum126
