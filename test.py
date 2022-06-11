from main import *

import subprocess
import tempfile
import textwrap

def auto_test(function_preamble, goal, function_postamble=None):
    function_preamble = textwrap.dedent(function_preamble)
    goal = textwrap.dedent(goal)
    if function_postamble is None:
        function_postamble = "}"
    function_postamble = textwrap.dedent(function_postamble)

    print("A" + "-" * 20)
    print(goal)
    print("B" + "-" * 20)
    proof = solve_goal(goal)
    print("C" + "-" * 20)
    print(proof)
    print("D" + "-" * 20)

    complete_function = (
        function_preamble + "\n" +
        proof +
        function_postamble
    )

    with tempfile.NamedTemporaryFile(mode='w') as f:
        f.write(complete_function)
        f.flush()
        ret = subprocess.run(['lean', f.name])
        assert ret.returncode == 0

def test_basic_identity():
    auto_test("example {P : Prop} (p : P) : P := by {",
              """
              Goals (1)
              P : Prop
              p : P
              ⊢ P
              """)

def test_basic_implication():
    auto_test("example {P : Prop} : P → P := by {",
              """
              Goals (1)
              P : Prop
              ⊢ P → P
              """)

def test_and_left():
    auto_test("example {P Q : Prop} : P ∧ Q → P := by {",
              """
              Goals (1)
              P Q : Prop
              ⊢ (And P Q) → P
              """)

def test_and_right():
    auto_test("example {P Q : Prop} : P ∧ Q → Q := by {",
              """
              Goals (1)
              P Q : Prop
              ⊢ (And P Q) → Q
              """)

def test_a_imp_b_imp_a():
    auto_test("example {A B : Prop} : A → B → A := by {",
              """
              Goals (1)
              A B : Prop
              ⊢ A → B → A
              """)

def test_a_iff_a():
    auto_test("example {A : Prop} : A ↔ A := by {",
              """
              Goals (1)
              A : Prop
              ⊢ Iff A A
              """)

def test_contrapos():
    auto_test("example {A B : Prop} : (A → B) → ((¬B) → (¬A)) := by {",
              """
              Goals (1)
              A B : Prop
              ⊢ (A → B) → ¬B → ¬A
              """)

def test_and_symmetric():
    auto_test("example { p q : Prop } : p ∧ q ↔ q ∧ p := by {",
              """
              Goals (1)
              p q : Prop
              ⊢ Iff (And p q) (And q p)
              """)

'''
def test_stuck():
    auto_test("example {p} (hyp : ¬¬p) : p := by {",
              """
              Goals (1)
              p : Prop
              hyp : Not (Not p)
              ⊢

'''

'''
def test_disjunction():
    auto_test("example (A B : Prop) : (Or
'''

if __name__ == '__main__':
    test_basic()
