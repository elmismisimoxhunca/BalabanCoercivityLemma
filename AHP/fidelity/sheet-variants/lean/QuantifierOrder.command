export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/sheet-variants/lean/QuantifierOrder.lean > ../AHP/fidelity/sheet-variants/lean/QuantifierOrder.log 2>&1
echo $? > ../AHP/fidelity/sheet-variants/lean/QuantifierOrder.exit
