import parse as parselib
import sys

from expressions import *
from parsers import parse_expr
from proof import proof
from proof_tree import proof_tree

def solve_goal(goal_output):
    goal_output_lines = goal_output.strip().splitlines()
    assert len(goal_output_lines) > 1

    parse_ret = parselib.parse("Goals ({num_goals:d})", goal_output_lines[0])
    assert parse_ret
    num_goals = parse_ret['num_goals']
    assert num_goals > 0

    interesting_regions = []
    current_region = []
    num_goals_found = 0
    for l in goal_output_lines[1:]:
        if len(l) == 0:
            num_goals_found += 1
            interesting_regions.append(current_region)
            current_region = []
        else:
            current_region.append(l)
        if num_goals_found == num_goals:
            break

    if current_region != []:
        interesting_regions.append(current_region)

    proofs = []

    for region in interesting_regions:
        assumption_lines = []
        current_line = ""
        for line in region:
            if line[0] == ' ':
                current_line += " " + line.strip()
            else:
                if current_line != "":
                    assumption_lines.append(current_line)
                current_line = line.strip()
        if current_line != "":
            assumption_lines.append(current_line)
        assert assumption_lines[-1][0] == "⊢"
        goal = assumption_lines[-1][1:].strip()
        assumption_lines = assumption_lines[:-1]

        proofs.append(proof.parse(assumption_lines, goal))


    assert len(proofs) == num_goals
    if num_goals == 1:
        target = proof_tree.singleton(proofs[0])
    else:
        target = proof_tree.conjunction(*[proof_tree.singleton(p) for p in proofs])

    num_steps_remaining = 10
    stuck = False
    while num_steps_remaining > 0 and not target.done and not stuck:
        if target.is_stuck:
            target.get_complexity()
            target.unstick()
            stuck = target.is_stuck
        num_steps_remaining = target.step_proofs(num_steps_remaining)

    return target.get_proof_text()


if __name__ == '__main__':
    from io import StringIO
    class Capturing(list):
        def __enter__(self):
            self._stdout = sys.stdout
            sys.stdout = self._stringio = StringIO()
            return self
        def __exit__(self, *args):
            self.extend(self._stringio.getvalue().splitlines())
            del self._stringio    # free up some memory
            sys.stdout = self._stdout

    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            i = f.read()
    else:
        i = sys.stdin.read()

    ex = None
    output = None
    with Capturing() as stdout:
        try:
            output = solve_goal(i)
        except Exception as e:
            ex = e
    if stdout != []:
        for line in stdout:
            print("-- " + line)
    print(output)

    if ex is not None:
        raise ex
