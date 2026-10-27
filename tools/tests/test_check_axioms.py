from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_axioms import normalize_log


class CompleteAxiomParserTests(unittest.TestCase):
    def test_subsets_order_and_multiple_records(self):
        text = "warning: an unrelated diagnostic\n'A.x' depends on axioms: [Quot.sound, propext]\n'A.y' does not depend on any axioms\n"
        self.assertEqual(normalize_log(text), [
            "'A.x' depends on axioms: [propext, Quot.sound]",
            "'A.y' does not depend on any axioms"])

    def test_apostrophe_in_declaration_name(self):
        self.assertEqual(normalize_log("'A.derivative'' depends on axioms: [propext]\n"),
                         ["'A.derivative'' depends on axioms: [propext]"])

    def test_list_can_start_on_next_line(self):
        self.assertEqual(normalize_log("'A.x' depends on axioms:\n [Classical.choice]\n"),
                         ["'A.x' depends on axioms: [Classical.choice]"])

    def test_empty_list(self):
        self.assertEqual(normalize_log("'A.x' depends on axioms: []"),
                         ["'A.x' does not depend on any axioms"])

    def test_reject_bad_messages(self):
        cases = [
            '', 'warning: no records',
            "'A.x' depends on axioms: [sorryAx]",
            "'A.x' depends on axioms: [propext,\n False.assumption]",
            "'A.x' depends on axioms: [propext,",
            "'A.x' depends on axioms: [propext,\n'A.y' depends on axioms: [Quot.sound]",
            "'A.x' depends on axioms: propext]",
            "'A.x' depends on axioms: [[propext]]",
            "'A.x' depends on axioms: [propext,]",
            "'A.x' depends on axioms: [propext, propext]",
            "'A.x' depends on axioms: [propext] trailing junk",
            "'A.x' does not depend on any axioms trailing junk",
            'malformed depends on axioms: [propext]',
        ]
        for text in cases:
            with self.subTest(text=text), self.assertRaises(ValueError):
                normalize_log(text)


if __name__ == '__main__':
    unittest.main()
