"""Focused printer controls; kernel replay remains the generated equations' check."""

import unittest
from pathlib import Path
import sys
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from bridges.structured import normal_forms as printer  # noqa: E402


BOOL = ["bool"]


class NormalFormPrinterTests(unittest.TestCase):
    def evaluator(self, roles=("prover", "verifier"), role=1, functions=None):
        unit = SimpleNamespace(function=lambda name: functions[name])
        frame = printer.Frame(unit, list(roles), role, "shared", {}, {}, {}, {})
        frame.role_name = roles[role]
        return printer.Evaluator(frame, printer.Names(),
                                 lambda values, proof, pad: printer.Done(
                                     printer.values_literal([value.component() for value in values])))

    def guard(self, condition, role=1, owner="verifier", environment=None):
        evaluator = self.evaluator(role=role)
        environment = environment or [condition]
        instruction = [["guard", owner], [0], [], [], "guard_site"]
        proof = []
        node = evaluator.run([instruction], ["return", list(range(len(environment)))],
                             environment, proof, 2)
        return node, "\n".join(proof)

    def test_symbolic_boolean_guard_preserves_other_terms(self):
        node, proof = self.guard(printer.present(BOOL, "flag"), environment=[
            printer.present(BOOL, "flag"), printer.present(BOOL, "flagSuffix")])
        self.assertEqual(node.prop, "flag = true")
        self.assertEqual(node.then.expr, ".cons (some true) (.cons (some flagSuffix) .nil)")
        self.assertEqual(node.otherwise.reason, "reject")
        self.assertIn("Bool.eq_false_iff.mpr", proof)

    def test_compound_boolean_guard(self):
        node, _ = self.guard(printer.present(BOOL, "flags.get .here && enabled"))
        self.assertEqual(node.prop, "(flags.get .here && enabled) = true")

    def test_boolean_guard_updates_only_its_operand(self):
        flag = printer.present(BOOL, "flag")
        node, _ = self.guard(flag, environment=[flag, flag])
        self.assertEqual(node.then.expr, ".cons (some true) (.cons (some flag) .nil)")

    def test_optional_boolean_guard_splits_presence_before_truth(self):
        node, _ = self.guard(printer.optional(BOOL, "flag"))
        self.assertIsInstance(node, printer.Match)
        self.assertEqual(node.none.reason, "incomplete")
        self.assertEqual(node.some.prop, "flag = true")
        self.assertEqual(node.some.otherwise.reason, "reject")

    def test_literal_and_inactive_guards_keep_stop_semantics(self):
        for expression, reason in (("true", None), ("false", "reject")):
            with self.subTest(expression=expression):
                node, _ = self.guard(printer.present(BOOL, expression))
                self.assertEqual(getattr(node, "reason", None), reason)
        node, _ = self.guard(printer.absent(BOOL))
        self.assertEqual(node.reason, "incomplete")
        node, _ = self.guard(printer.absent(BOOL), role=0)
        self.assertIsInstance(node, printer.Done)

    def test_decided_proposition_keeps_existing_presentation(self):
        node, proof = self.guard(printer.present(BOOL, "decide (left = right)"))
        self.assertEqual(node.prop, "left = right")
        self.assertIn("decide_true", proof)

    def application(self, mapping, callee_roles, input_scopes, output_scopes, caller_roles=None,
                    separation=None):
        caller_roles = caller_roles or ["prover", "verifier"]
        function = SimpleNamespace(roles=callee_roles, inputs=[BOOL], outputs=[BOOL],
                                   input_scopes=input_scopes, output_scopes=output_scopes)
        evaluator = self.evaluator(roles=caller_roles, role=len(caller_roles) - 1,
                                   functions={"terminal": function})
        index = mapping.index(caller_roles[-1]) if caller_roles[-1] in mapping else 0
        info = {"inputs": [{"name": "flag", "mode": "optional"}],
                "process": "Terminal.process", "process_binders": ["ctx", "flag"],
                "theorem": "Terminal.process_eq", "parameters": [], "binders": [],
                "premises": [], "uses_separate": len(callee_roles) == 2 if separation is None else separation}
        app = printer.Application(
            "terminal", "application_site", [caller_roles.index(role) for role in mapping],
            "terminalSignature", "terminalContext", "unit", "terminalDefinition",
            "terminal_member", "terminal_signature", "terminalBody", "terminal_raw", {},
            {index: info}, {}, ["accepted"], "terminal")
        evaluator.frame.applications[app.site] = app
        descriptor = ["protocol_apply", "terminal", mapping]
        proof = []
        node = evaluator.application(descriptor, [printer.optional(BOOL, "flag")], app.site,
                                     [], ["return", [0]], [], proof, 2)
        return node, "\n".join(proof)

    def test_single_role_application_in_two_role_caller(self):
        node, proof = self.application(["verifier"], ["checker"], [[0]], [[0]])
        self.assertIn("Terminal.process (terminalContext ctx) flag", node.process)
        self.assertIn("[1] \"application_site\" ctx (ctx.roles 1)", proof)
        self.assertNotIn("separate", proof)
        self.assertIn("terminalReturned.get .here", node.next.expr)

    def test_single_role_caller_and_empty_output_scope(self):
        node, proof = self.application(["checker"], ["checker"], [[0]], [[]], ["checker"])
        self.assertEqual(node.next.expr, ".cons none .nil")
        self.assertNotIn("separate", proof)

    def test_two_role_application_preserves_separation_and_output_mask(self):
        node, proof = self.application(["prover", "verifier"], ["sender", "checker"], [[0, 1]], [[0]])
        self.assertIn("(separate := separate)", proof)
        self.assertIn("Ne.symm separate", proof)
        self.assertIn("terminal_verifier_outputs ctx separate", proof)
        self.assertEqual(node.next.expr, ".cons none .nil")

    def test_two_role_premise_survives_without_foreign_input_masks(self):
        _, proof = self.application(["prover", "verifier"], ["sender", "checker"], [[1]], [[0]])
        self.assertIn("(separate := separate)", proof)
        self.assertNotIn("Ne.symm separate", proof)

    def test_ambiguous_or_unsupported_application_mapping_refused(self):
        for mapping, roles in ((["verifier", "verifier"], ["sender", "checker"]),
                               (["verifier"], ["first", "second"]),
                               (["prover", "verifier"], ["first", "second", "third"])):
            with self.subTest(mapping=mapping, roles=roles):
                with self.assertRaises(printer.GeneratorError):
                    self.application(mapping, roles, [[0]], [[0]])

    def test_invalid_protocol_roster_refused(self):
        for roles, role in (([], 0), (["a", "a"], 0), (["a", "b", "c"], 0),
                            (["a"], 1), (["a"], -1), (["a"], True), (["a"], 0.0)):
            with self.subTest(roles=roles, role=role):
                module = printer.Module.__new__(printer.Module)
                module.unit = SimpleNamespace(entry="entry", function=lambda name: SimpleNamespace(roles=roles))
                with self.assertRaisesRegex(printer.GeneratorError, "one or two distinct roles"):
                    module.shared({"roles": [{"role": role, "name": "checker"}]})

    def test_single_role_callee_cannot_require_separation(self):
        with self.assertRaisesRegex(printer.GeneratorError, "single-role callee cannot require separation"):
            self.application(["verifier"], ["checker"], [[0]], [[0]], separation=True)

    def test_empty_output_scope_needs_no_other_role(self):
        module = printer.Module.__new__(printer.Module)
        module.carrier = "CommRing"
        function = SimpleNamespace(outputs=[BOOL], output_scopes=[[]])
        text = []
        kept, separate = module.masked_outputs(text, "returned", function, "ctx", 0, None)
        self.assertEqual(kept, ".cons none .nil")
        self.assertFalse(separate)
        self.assertNotIn("separate", "\n".join(text))
        function.output_scopes = [[1]]
        with self.assertRaisesRegex(printer.GeneratorError, "masking needs a distinct other role"):
            module.masked_outputs([], "returned", function, "ctx", 0, None)


if __name__ == "__main__":
    unittest.main()
