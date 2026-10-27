-- Check2.lean (part 2 of 3): imports the modules hosting cited declarations and prints their axioms. Split because modules from different lanes declare the same names and cannot be imported into one environment.
import NfFam4
import NuTwoUnc

#print axioms NcwdhFam.constFam_headline  -- constfam-headline
#print axioms AdalyFormal.CoverNested.ne2_bond_uncovered  -- ell2-bond-uncovered
