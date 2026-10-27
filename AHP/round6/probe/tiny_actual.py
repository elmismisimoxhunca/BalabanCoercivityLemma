#!/usr/bin/env python3
"""Actual first character (7,7), very small eps; NOT the zero-character batch."""
import sys
sys.dont_write_bytecode = True
from probe import *
for eps in ['1e-40','1e-60','1e-100']:
    run(2,18,eps,400,7,7)
