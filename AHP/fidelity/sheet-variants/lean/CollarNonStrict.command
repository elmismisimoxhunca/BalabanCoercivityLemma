export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/sheet-variants/lean/CollarNonStrict.lean > ../AHP/fidelity/sheet-variants/lean/CollarNonStrict.log 2>&1
echo $? > ../AHP/fidelity/sheet-variants/lean/CollarNonStrict.exit
