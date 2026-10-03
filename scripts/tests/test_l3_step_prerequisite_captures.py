"""Universal PC writer and raw instruction dispatcher captures retain full domains."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
class Captures(unittest.TestCase):
    def test_exact_and_mutated_captures(self):
        for family in ("write-pc", "decode-any", "update-pc"):
            path=ROOT / f"scripts/hol-probes/check-l3-{family}.py"
            spec=importlib.util.spec_from_file_location(family,path)
            module=importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            rows=module.EXPECTED
            module.check("\n".join(rows)+"\n")
            mutations=[rows[:-1],rows+[rows[0]],rows+["extra=T"],
                       [x.replace("hypotheses=0","hypotheses=1") for x in rows],
                       [x.replace("∀","∀restricted_") for x in rows],
                       [x.replace(" -> "," -> restricted_") for x in rows]]
            for mutation in mutations:
                with self.subTest(family=family,mutation=mutation):
                    with self.assertRaises(ValueError): module.check("\n".join(mutation))
