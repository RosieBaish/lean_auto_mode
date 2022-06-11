import copy
import parse as parselib


from stmt import stmt
from expressions import *
from util import *

class proof:
    name = None
    assumptions = None
    goal = None

    def __init__(self, name, assumptions, goal):
        self.name = name
        self.assumptions = assumptions
        self.goal = goal

    def __eq__(self, other):
        if not isinstance(other, proof):
            return False
        return ((self.name == other.name) and
                (self.assumptions == other.assumptions) and
                (self.goal == other.goal))
    @staticmethod
    def parse(assumption_lines, goal):
        maybe_name = parselib.parse("case {name}", assumption_lines[0])
        if maybe_name:
            new_name = maybe_name['name']
            assumption_lines = assumption_lines[1:]
        else:
            new_name = None
        new_goal = stmt(new_name, goal)

        new_assumptions = []
        for line in assumption_lines:
            colon_loc = line.index(":")
            names = line[:colon_loc].strip().split()
            value = line[colon_loc + 1:]
            for name in names:
                new_assumptions.append(stmt(name, value))
        return proof(new_name, new_assumptions, new_goal)

    def to_string(self, func):
        s = ""
        if self.name is not None:
            s += self.name + "\n"
        s += "\n".join([func(assumption) for assumption in self.assumptions])
        s += "\n"
        s += "⊢ " + func(self.goal)
        return s

    def calculate_complexity(self):
        # TODO Implement
        return 1

    def __str__(self):
        return self.to_string(str)

    def __repr__(self):
        return self.to_string(repr)

    def apply_rewrite_in_place(self, rewrite):
        assert valid_rewrite_dict(rewrite_kind.IN_PLACE, rewrite)
        # If we have no assumptions we automatically need it,
        # If we do have them we only might
        need_proof_text = not "assumptions" in rewrite
        debug("in Proof: ", rewrite, "\n", self, "\n\n\n")
        if "name" in rewrite:
            self.name = rewrite["name"]
        if "goal" in rewrite:
            self.goal = rewrite["goal"]
            need_proof_text = True
        if "assumptions" in rewrite:
            for a in rewrite["assumptions"]:
                if not stmt.check_type_match(a, self.assumptions):
                    self.assumptions.append(a)
                    need_proof_text = True
        if "proof_text" in rewrite:
            if need_proof_text:
                return rewrite["proof_text"]
            else:
                debug("Didn't need", rewrite["proof_text"])
                return []
        else:
            return []

    # Is this proof finishable in a single step
    def can_finish(self):
        if self.goal.value == token("False"):
            for i, assumption in enumerate(self.assumptions):
                if contr := stmt.check_type_match_expr_negation(assumption.value, self.assumptions[i + 1:]):
                    return "contradiction"

        if exact := stmt.check_type_match(self.goal, self.assumptions):
            return f"exact {exact.name}"

    def simplify(self):
        new_proof_text = []
        changed = False
        for (func, val) in (
                [(stmt.simplify_assumption, a) for a in self.assumptions] +
                [(stmt.simplify_goal, self.goal)]):
            rw_kind, rewrite = func(val, self)
            if rw_kind == rewrite_kind.IN_PLACE:
                changed = True
                new_proof_text.extend(self.apply_rewrite_in_place(rewrite))
            elif is_split_proof(rw_kind):
                debug(rewrite)
                if "name" in rewrite:
                    self.name = rewrite["name"]
                if "proof_text" in rewrite:
                    new_proof_text.extend(rewrite["proof_text"])
                rewrite["proof_text"] = new_proof_text
                return (rw_kind, rewrite)

        if changed:
            return (rewrite_kind.IN_PLACE, {"proof_text": new_proof_text})
        else:
            assert new_proof_text == []
            return (rewrite_kind.NONE, {})

    def unstick(self):
        new_proofs = []

        # By contradiction
        name = "h" # This is just want lean calls it, IDK why
        new_assumptions = self.assumptions + [self.goal]
        new_goal = stmt(f'Not_{stmt.get_name(self.goal.value, self)}_implies_False',
                        expr.create([token("Implies"),
                                     expr.create([token("Not"), copy.copy(self.goal.value)]),
                                     token("False")]))
        new_proofs.append((["apply Classical.byContradiction"], proof(name, new_assumptions, new_goal)))
        return new_proofs
