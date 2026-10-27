"""Regression tests for the actual REPRODUCE.sh axiom-output gate.

A tiny compiler-output stub isolates the shell gate; it is not a Lean proof test.
"""
from pathlib import Path
import os
import re
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class AxiomGateTests(unittest.TestCase):
    def run_gate(self, output):
        source = (ROOT / 'REPRODUCE.sh').read_text()
        function = re.search(r'^run_check\(\) \{.*?^\}', source, re.M | re.S).group()
        with tempfile.TemporaryDirectory(dir=os.environ.get('BB_THREAD_TMP')) as td:
            work = Path(td)
            (work / 'tools').symlink_to(ROOT / 'tools', target_is_directory=True)
            compiler = work / 'compiler-output'
            compiler.write_text('#!/bin/sh\nprintf "%s" "$AXIOM_FIXTURE"\n')
            compiler.chmod(0o755)
            script = '\n'.join([
                'set -u', f'ROOT={shlex.quote(td)}',
                f'LAKE={shlex.quote(str(compiler))}', 'LEAN_BIN=unused',
                'say() { printf "%s\\n" "$*"; }', function, 'run_check Fixture',
            ])
            result = subprocess.run(['bash', '-c', script], text=True, capture_output=True,
                                    env={**os.environ, 'AXIOM_FIXTURE': output})
            canonical = work / 'Fixture.axioms.txt'
            return result, canonical.read_text() if canonical.exists() else None

    def test_wrapped_sorry_rejected(self):
        result, _ = self.run_gate("'Example.bad' depends on axioms: [propext,\n  Classical.choice, Quot.sound, sorryAx]\n")
        self.assertNotEqual(result.returncode, 0, 'Continuation-line sorryAx was silently accepted')

    def test_wrapped_unexpected_axiom_rejected(self):
        result, _ = self.run_gate("'Example.bad' depends on axioms: [propext,\n  Unexpected.assumption]\n")
        self.assertNotEqual(result.returncode, 0, 'Continuation-line nonstandard axiom was accepted')

    def test_truncated_record_rejected(self):
        result, _ = self.run_gate("'Example.bad' depends on axioms: [propext,\n")
        self.assertNotEqual(result.returncode, 0, 'An incomplete axiom record was accepted')

    def test_allowed_wrapped_record_is_complete(self):
        result, canonical = self.run_gate("'Example.good' depends on axioms: [propext,\n  Classical.choice, Quot.sound]\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(canonical, "'Example.good' depends on axioms: [propext, Classical.choice, Quot.sound]\n")

    def test_axiom_free_record_accepted(self):
        result, canonical = self.run_gate("'Example.definition' does not depend on any axioms\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(canonical, "'Example.definition' does not depend on any axioms\n")


if __name__ == '__main__':
    unittest.main()
