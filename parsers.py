import copy

import parse as parselib
from expressions import *
from util import *

def parse_expr_inner(text):
    contents = []
    text = text.strip()
    assert text[0] == '(' or text[0] == '['
    text = text[1:]
    open_idx = min_non_neg(text.find('('), text.find('['))
    close_idx = min_non_neg(text.find(')'), text.find(']'))
    assert close_idx > -1
    while (open_idx > -1) and (open_idx < close_idx):
        contents.extend([token(x) for x in text[:open_idx].strip().split()])
        text = text[open_idx:]
        (subexp, text) = parse_expr_inner(text)
        contents.append(copy.copy(subexp))
        open_idx = min_non_neg(text.find('('), text.find('['))
        close_idx = min_non_neg(text.find(')'), text.find(']'))
        assert close_idx > -1

    contents.extend([token(x) for x in text[:close_idx].strip().split()])
    text = text[close_idx + 1:]

    expression = expr.create(contents)

    projections = [
        ('fst', 1),
        ('1',   1),
        ('snd', 2),
        ('2',   2),
    ]
    # Projection
    while len(text) > 0 and text[0] == '.':
        text = text[1:]
        for proj, index in projections:
            if text.startswith(proj):
                expression = projection(index, expression)
                text = text[len(proj):]
                break

    return (expression, text)

def parse_expr(text):
    text = ' '.join(text.split())
    (parsed, emp) = parse_expr_inner(text)
    assert emp == ""
    return parsed
