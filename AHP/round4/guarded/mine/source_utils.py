"""Source navigation only; compiled Lean types remain the authority."""
import re

def signature_end(clean):
    depth=0; i=0; quoted=False; escape=False
    while i<len(clean):
        c=clean[i]
        if quoted:
            if escape:escape=False
            elif c=='\\':escape=True
            elif c=='"':quoted=False
            i+=1;continue
        if c=='"':quoted=True;i+=1;continue
        if c in '([{⦃⟨':depth+=1
        elif c in ')]}⦄⟩':depth-=1
        if depth==0 and (clean[i:i+2]==':=' or re.match(r'where\b',clean[i:])):
            return i
        i+=1
    return None
