-- Check3.lean (part 3 of 3): imports the modules hosting cited declarations and prints their axioms. Split because modules from different lanes declare the same names and cannot be imported into one environment.
import NtAll
import NtFam
import NtFam2
import NtFam4
import NtFinal
import NtTwo
import NuA1
import NuA2
import NuA3

#print axioms NcwdhFam.famConst_all  -- famconst-all
#print axioms NcwdhFam.ncwdh_all  -- ncwdh-all
#print axioms NcwdhFam.FamilyTorusNCAt  -- famnc-at-def
#print axioms NcwdhFam.P428Target8FamilyTorusNC  -- famnc-def
#print axioms NcwdhFam.not_P428Target8FamilyTorusNC  -- famnc-not
#print axioms NcwdhFam.PerCubeRegularF  -- percuberegularf-def
#print axioms NcwdhFam.constFam  -- constfam-def
#print axioms NcwdhFam.FamilyTorusNCConstAt  -- famconst-def
#print axioms NcwdhFam.ConstFamWitnessFull  -- famconst-wit-def
#print axioms AdalyFormal.NcwdhStrong.ncwdh_fails_all  -- ncwdh-fails-all
#print axioms AdalyFormal.NcwdhStrong.not_P428Target8NCWDHc  -- ncwdh-not-c
#print axioms AdalyFormal.NcwdhStrong.not_P428Target8NCWDH_frozen  -- ncwdh-not-frozen
#print axioms AdalyFormal.CoverOmega.Win2.gU_not_adm_two  -- ell2-obstruction
#print axioms NcwdhFam.ncwdh_fails_two  -- ncwdh-fails-two
#print axioms NcwdhFam.not_covPlaqF_two  -- ell2-covplaq
#print axioms NcwdhFam.ConstFamWitnessTwo  -- constfam-wit-two-def
#print axioms NcwdhFam.constFam_witness_two  -- constfam-witness-two
#print axioms NcwdhFam.ncwdh_fails_ge_two  -- ncwdh-fails-ge-two
#print axioms NcwdhFam.famConst_ge_two  -- famconst-ge-two
