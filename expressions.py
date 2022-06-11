

class expr:
    contents = None
    def __init__(self, contents):
        assert contents != []
        assert isinstance(contents[0], str)
        for c in contents[1:]:
            assert isinstance(c, expr)

        self.contents = contents

    @staticmethod
    def create(contents):
        for (i, c) in enumerate(contents):
            assert isinstance(c, expr)
            if not isinstance(c, token):
                continue
            if "¬" in c.name:
                assert c.name[0] == "¬"
                if len(c.name) == 1:
                    # Negation on it's own
                    del contents[i]
                    # The term we need to modify is now contents[i]
                    new_expr = expr.create([token("Not")] + contents[i])
                    contents[i] = new_expr
                else:
                    new_expr = expr.create([token("Not"), token(c.name[1:])])
                    contents[i] = new_expr

        assert len(contents) > 0
        if len(contents) == 1:
            return contents[0]
        elif len(contents) == 2:
            assert isinstance(contents[0], token)
            return unary(contents[0].name, contents[1])
        else:
            return n_ary.create(contents)


    def to_string(self, recursive_call):
        if self.contents is None:
            return f"(Uninitialised {type(self)})"
        s = ""
        string_contents = []
        for c in self.contents:
            if isinstance(c, expr):
                string_contents.append(f'({recursive_call(c)})')
            elif isinstance(c, str):
                string_contents.append(c)
        return " ".join(string_contents)

    def __str__(self):
        return self.to_string(str)

    def __repr__(self):
        return self.to_string(repr)

    def eq_inner(self, other):
        if not isinstance(other, expr):
            return False
        if len(self.contents) != len(other.contents):
            return False
        for (l, r) in zip(self.contents, other.contents):
            if not l == r:
                return False
        return True

    def __eq__(self, other):
        ret = self.eq_inner(other)
        return ret

class token(expr):
    name = None

    def __init__(self, name):
        assert isinstance(name, str)
        super().__init__([name])
        self.name = name

    def as_name(self):
        return self.name

class unary(expr):
    name = None
    arg = None
    def __init__(self, name, arg):
        assert isinstance(name, str)
        assert isinstance(arg, expr)
        super().__init__([name, arg])
        self.name = name
        self.arg = arg

    def as_name(self):
        return f'{self.name}_{self.arg.as_name()}'


class n_ary(expr):
    name = None
    def __init__(self, name, args):
        assert isinstance(name, str)
        assert isinstance(args, list)
        for a in args:
            assert isinstance(a, expr)
        super().__init__([name] + args)
        self.name = name

    def as_name(self):
        return f'{self.name}_' + "_".join([a.as_name() for c in self.contents[1:]])

    @staticmethod
    def create(contents):
        if token("→") in contents:
            if len(contents) == 3:
                assert contents.index(token("→")) == 1
                return binary_combinator("Implies", contents[0], contents[2])
            else:
                arrow_index = contents.index(token("→"))
                return binary_combinator("Implies", expr.create(contents[:arrow_index]), expr.create(contents[arrow_index + 1:]))
        else:
            if isinstance(contents[0], token) and contents[0].name in binary_combinator.keywords:
                assert len(contents) == 3
                [kw, lhs, rhs] = contents
                return binary_combinator(kw.name, lhs, rhs)
            if isinstance(contents[0], token) and contents[0].name == "Proj":
                assert len(contents) == 3
                [kw, index, subexpr] = contents
                return projection(int(index), subexpr)

            assert isinstance(contents[0], token)
            return n_ary(contents[0].name, contents[1:])

class binary_combinator(n_ary):
    keyword = None
    left = None
    right = None

    keywords = [
        'And',
        'Or',
        'Iff',
        'Implies',
    ]

    def __init__(self, keyword, left, right):
        assert isinstance(keyword, str)
        assert keyword in binary_combinator.keywords
        assert isinstance(left, expr)
        assert isinstance(right, expr)
        super().__init__(keyword, [left, right])
        self.keyword = keyword
        self.left = left
        self.right = right

    def as_name(self):
        return f'{self.left.as_name()}_{self.keyword.lower()}_{self.right.as_name()}'

    def __str__(self):
        return f'{self.keyword} {str(self.left)} {str(self.right)}'

    def __repr__(self):
        return f'{self.keyword} {repr(self.left)} {repr(self.right)}'


class projection(n_ary):
    index = None
    sub_expr = None

    def __init__(self, index, sub_expr):
        super().__init__("Proj", [token(str(index)), sub_expr])
        self.index = index
        self.sub_expr = sub_expr

    names = ["fst", "snd"]
    def as_name(self):
        return f'{self.sub_expr.as_name()}_{self.names[self.index - 1]}'

    def __str__(self):
        return f'({str(self.sub_expr)}).{self.index}'

    def __repr__(self):
        return f'({repr(self.sub_expr)}).{self.index}'
