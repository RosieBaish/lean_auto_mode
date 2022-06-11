import copy
from enum import Enum

from proof import proof
from util import *

def debug(*args, **kwargs):
    if (False):
        print(*args, **kwargs)

proof_tree_kind = Enum("kind", "SINGLETON AND OR", qualname="proof_tree.kind")

class proof_tree:
    name = None
    kind = None
    contents = None
    proof_text = None
    done = False
    is_stuck = False
    complexity = None

    def __init__(self, kind, *contents):
        assert isinstance(kind, proof_tree_kind)
        self.kind = kind
        self.proof_text = []
        if kind == kind.SINGLETON:
            assert len(contents) == 1
            assert isinstance(contents[0], proof)
            self.name = contents[0].name
            self.contents = contents[0]
        else:
            for c in contents:
                assert isinstance(c, proof_tree)
            self.contents = contents

    @staticmethod
    def singleton(contents):
        return proof_tree(proof_tree_kind.SINGLETON, contents)

    @staticmethod
    def conjunction(*contents):
        return proof_tree(proof_tree_kind.AND, contents)

    @staticmethod
    def disjunction(*contents):
        return proof_tree(proof_tree_kind.OR, contents)

    def to_string(self, func):
        if self.kind == proof_tree_kind.SINGLETON:
            return "SINGLETON(" + str(self.name) + "): " + func(self.contents)
        else:
            return (str(self.kind) + "(" + str(self.name) + "):\n" + "\n".join([func(c) for c in self.contents]))
    def __str__(self):
        return self.to_string(str)
    def __repr__(self):
        return self.to_string(repr)

    def get_proof_text(self):
        # Adding [''] so that we get a trailing semicolon
        if self.kind == proof_tree_kind.SINGLETON:
            return ";\n".join(self.proof_text + [''])
        elif self.kind == proof_tree_kind.AND:
            total_proof = ";\n".join(self.proof_text + [''])
            debug(self)
            for p in self.contents:
                total_proof += f"case {p.name} => {{\n"
                total_proof += p.get_proof_text()
                total_proof += ("}\n")
            return total_proof
        elif self.kind == proof_tree_kind.OR:
            for p in self.contents:
                if p.done:
                    return f"apply {p.name};\n" + p.get_proof_text()

    def get_complexity(self):
        if self.done:
            self.complexity = -1
        if self.kind == proof_tree_kind.SINGLETON:
            self.complexity = self.contents.calculate_complexity()
        else:
            self.complexity = min_non_neg(*[c.get_complexity() for c in self.contents])
        return self.complexity

    def unstick(self):
        assert not self.done
        assert self.is_stuck

        if self.kind == proof_tree_kind.SINGLETON:
            old_contents = self.contents
            proof_text, new_proofs = zip(*self.contents.unstick())
            self.update_self(conjunction=None, disjunction=new_proofs, new_proof_text=proof_text)
            self.is_stuck = (old_contents == self.contents)
        else:
            for c in self.contents:
                if c.complexity == self.complexity:
                    c.unstick()
                    self.is_stuck = c.is_stuck
                    break

    def set_kind_from_rewrite_kind(self, rw_kind):
        if rw_kind == rewrite_kind.SPLIT_CONJUNCTION:
            self.kind = proof_tree_kind.AND
        elif rw_kind == rewrite_kind.SPLIT_DISJUNCTION:
            self.kind = proof_tree_kind.OR
        else:
            debug(rw_kind)
            assert False, "Unknown kind"

    def do_rewrite(self, rw_kind, rewrite):
        assert valid_rewrite_dict(rw_kind, rewrite)
        debug("in proof_tree: ", rw_kind, rewrite, "\n", self, "\n\n")
        if "name" in rewrite.keys():
            debug("NAME")
            self.name = rewrite["name"]
            rewrite.pop("name")
        if "proof_text" in rewrite:
            self.proof_text.extend(rewrite["proof_text"])
            rewrite.pop("proof_text")
        if rw_kind == rewrite_kind.NONE:
            return
        elif rw_kind == rewrite_kind.IN_PLACE:
            # Only name and proof_text are possible
            self.proof_text.extend(
                self.contents.apply_rewrite_in_place(rewrite))
            debug(self, "\n\n\n\n")
            return
        elif is_split_proof(rw_kind):
            self.set_kind_from_rewrite_kind(rw_kind)
            new_contents = []
            for a in rewrite["new_proofs"]:
                new_proof_tree = proof_tree.singleton(copy.deepcopy(self.contents))
                debug("A: ", new_proof_tree)
                new_proof_tree.do_rewrite(rewrite_kind.IN_PLACE, a)
                debug("B: ", new_proof_tree)
                new_contents.append(new_proof_tree)
            self.contents = new_contents
            debug("self: ", self)

    def simplify_singleton(self):
        if soln := self.contents.can_finish():
            self.proof_text.append(soln)
            self.done = True
            return

        self.do_rewrite(*self.contents.simplify())

        self.done = False
        self.is_stuck = False

    def step_proofs(self, steps_remaining):
        debug(self)
        if steps_remaining <= 0:
            return steps_remaining
        if self.done:
            return steps_remaining
        if self.is_stuck:
            return steps_remaining

        if self.kind == proof_tree_kind.SINGLETON:
            assert isinstance(self.contents, proof)
            self.simplify_singleton()
            steps_remaining -= 1
        elif self.kind == proof_tree_kind.AND:
            assert isinstance(self.contents, list)
            for p in self.contents:
                assert isinstance(p, proof_tree)
                steps_remaining = p.step_proofs(steps_remaining)
            if all(c.done for c in self.contents):
                self.done = True
            self.is_stuck = all(c.is_stuck for c in self.contents)
        elif self.kind == proof_tree_kind.OR:
            assert isinstance(self.contents, list)
            for p in self.contents:
                assert isinstance(p, proof_tree)
                steps_remaining = p.step_proofs(steps_remaining)
            if any(c.done for c in self.contents):
                self.done = True
            self.is_stuck = all(c.is_stuck for c in self.contents)
        return steps_remaining
