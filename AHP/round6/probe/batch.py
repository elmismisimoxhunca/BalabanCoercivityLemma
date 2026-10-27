#!/usr/bin/env python3
"""Bounded sequential batch of the probe; use heavy run, never spawn workers."""
import sys
sys.dont_write_bytecode = True
from probe import *
if __name__=='__main__':
    q=int(sys.argv[1]);R=int(sys.argv[2]);dps=int(sys.argv[3])
    for eps in sys.argv[4:]: run(q,R,eps,dps)
