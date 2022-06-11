from expressions import *
from parsers import parse_expr
from util import *

class stmt:
    def __init__(self, name, value):
        self.name = name
        if isinstance(value, expr):
            self.value = value
        else:
            self.value = parse_expr(f'({value})')

    @staticmethod
    def anon(value, proof):
        """Construct a statement with a sensible, non-clashing name"""
        name = stmt.get_name(value, proof)
        return stmt(name, value)

    def __repr__(self):
        s = ""
        if self.name is not None:
            s += f'{self.name} : '
        s += f'{repr(self.value)}'
        return s

    @staticmethod
    def check_type_match_expr_negation(e, others):
        if isinstance(e, unary) and e.name == "Not":
            return stmt.check_type_match_expr(e.arg, others)
        else:
            return stmt.check_type_match_expr(unary("Not", e), others)

    @staticmethod
    def check_type_match_expr(e, others):
        for other in others:
            if other.value == e:
                return other
        return None

    def check_type_match(self, others):
        return stmt.check_type_match_expr(self.value, others)

    @staticmethod
    def get_name(expression, proof):
        name = expression.as_name()
        while(name in [p.name for p in proof.assumptions]):
            name = name + "'"
        return name

    def simplify_assumption(self, proof):
        if isinstance(self.value, binary_combinator):
            if self.value.keyword == "And":
                lhs = stmt.anon(self.value.left, proof)
                rhs = stmt.anon(self.value.right, proof)
                return (rewrite_kind.IN_PLACE,
                        {
                            "proof_text": [f"have ⟨ {lhs.name} , {rhs.name} ⟩ := {self.name}" ],
                            "assumptions": [lhs, rhs],
                        })
            elif self.value.keyword == "Or":
                lhs = stmt.anon(self.value.left, proof)
                rhs = stmt.anon(self.value.right, proof)
                if (stmt.check_type_match(self.value.left, proof.assumptions) is None and
                    stmt.check_type_match(self.value.left, proof.assumptions) is None):
                    return (rewrite_kind.SPLIT_CONJUNCTION,
                            {
                                "proof_text": [f"apply (Or.elim {self.name})" ],
                                "new_proofs": [
                                    {
                                        "name": "left",
                                        "goal": stmt(goal.name, binary_combinator("Implies", lhs, copy.copy(goal.value)))
                                    },
                                    {
                                        "name": "right",
                                        "goal": stmt(goal.name, binary_combinator("Implies", rhs, copy.copy(goal.value)))
                                    }
                                ]
                            })
            elif self.value.keyword == "Implies":
                if other := stmt.check_type_match_expr(self.value.left, proof.assumptions):
                    rhs = stmt.anon(self.value.right, proof)
                    return (rewrite_kind.IN_PLACE,
                            {
                                "proof_text": [f"have {rhs.name} := ({self.name} {other.name})" ],
                                "assumptions": [rhs],
                            })
        if self.value.contents[0] == "ite":
            assert len(self.value.contents) == 4
            cond = self.value.contents[1]
            #rw [if_pos]
            if other := stmt.check_type_match_expr(cond, proof.assumptions):
                return (rewrite_kind.IN_PLACE,
                        {
                            "proof_text": [f"rw [(if_pos {other.name})]"],
                            "assumptions": [stmt.anon(self.value.contents[2], proof)],
                        })
            elif other := stmt.check_type_match_expr_negation(cond, proof.assumptions):
                return (rewrite_kind.IN_PLACE,
                        {
                            "proof_text": [f"rw [(if_neg {other.name})]"],
                            "assumptions": [stmt.anon(self.value.contents[3], proof)],
                        })

        return (rewrite_kind.NONE, {})

    def simplify_goal(self, proof):
        if self.value.contents[0] == "ite":
            assert len(self.value.contents) == 4
            cond = self.value.contents[1]
            #rw [if_pos]
            if other := stmt.check_type_match_expr(cond, proof.assumptions):
                return (rewrite_kind.IN_PLACE,
                        {
                            "proof_text": [f"rw [(if_pos {other.name})]"],
                            "goal": stmt.anon(self.value.contents[2], proof),
                        })
            elif other := stmt.check_type_match_expr_negation(cond, proof.assumptions):
                return (rewrite_kind.IN_PLACE,
                        {
                            "proof_text": [f"rw [(if_neg {other.name})]"],
                            "goal": stmt.anon(self.value.contents[3], proof),
                        })
            else:
                return (rewrite_kind.SPLIT_CONJUNCTION,
                            {
                                "proof_text": [f"apply Or.elim (Classical.em {self.name})" ],
                                "new_proofs": [
                                    {
                                        "name": "left",
                                        "goal": stmt(goal.name, binary_combinator("Implies", lhs, copy.copy(goal.value)))
                                    },
                                    {
                                        "name": "right",
                                        "goal": stmt(goal.name, binary_combinator("Implies", rhs, copy.copy(goal.value)))
                                    }
                                ]
                            })

        if isinstance(self.value, unary) and self.value.name == "Not":
            name = stmt.get_name(self.value.arg, proof)
            return (rewrite_kind.IN_PLACE,
                    {
                        "proof_text": [f"intro {name}"],
                        "assumptions": [stmt(name, self.value.arg)],
                        "goal": stmt("False", token("False"))
                    })
        if isinstance(self.value, binary_combinator):
            if self.value.keyword == "And":
                return (rewrite_kind.SPLIT_CONJUNCTION,
                    {
                        "proof_text": ["apply And.intro"],
                        "new_proofs": [
                            {
                                "name": "left",
                                "goal": stmt.anon(self.value.left, proof),
                            },
                            {
                                "name": "right",
                                "goal": stmt.anon(self.value.right, proof),
                            }
                        ]
                    })
            elif self.value.keyword == "Iff":
                return (rewrite_kind.SPLIT_CONJUNCTION,
                        {
                            "proof_text": ["apply Iff.intro"],
                            "new_proofs": [
                                {
                                    "name": "mp",
                                    "goal": stmt.anon(
                                        binary_combinator(
                                            "Implies",
                                            self.value.left,
                                            self.value.right),
                                        proof),
                                },
                                {
                                    "name": "mpr",
                                    "goal": stmt.anon(
                                        binary_combinator(
                                            "Implies",
                                            self.value.right,
                                            self.value.left),
                                        proof),
                                }
                            ]
                        })
            elif self.value.keyword == "Implies":
                intro = stmt.anon(self.value.left, proof)
                return (rewrite_kind.IN_PLACE,
                        {
                            "proof_text": [f"intro {intro.name}"],
                            "assumptions": [intro],
                            "goal": stmt.anon(self.value.right, proof),
                        })
        return (rewrite_kind.NONE, {})
