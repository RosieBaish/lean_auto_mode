from enum import Enum

rewrite_kind = Enum("rewrite_kind", "SPLIT_CONJUNCTION SPLIT_DISJUNCTION IN_PLACE NONE")

def debug(*args, **kwargs):
    if (False):
        print(*args, **kwargs)

def is_split_proof(rw_kind):
    return (rw_kind == rewrite_kind.SPLIT_CONJUNCTION or
            rw_kind == rewrite_kind.SPLIT_DISJUNCTION)

def valid_rewrite_dict(rw_kind, rewrite):
    # Have to import here because of a stupid circular import problem
    from stmt import stmt
    outer_keys = [
        ("new_proofs", list),
        ("proof_text", list),
    ]
    inner_keys = [
        ("name", str),
        ("proof_text", list),
        ("assumptions", list),
        ("goal", stmt),
    ]

    debug(rewrite)
    rewrite = dict(rewrite)
    keys = rewrite.keys()
    if "proof_text" in keys:
        if not all([isinstance(p, str) for p in rewrite["proof_text"]]):
            debug("Proof text didn't type check")
            return False
    if rw_kind == rewrite_kind.NONE:
        debug("kind is NONE, checking for empty dict")
        return rewrite == {}
    elif rw_kind == rewrite_kind.IN_PLACE:
        debug("kind is IN_PLACE")
        if "assumptions" in keys:
            if not all([isinstance(a, stmt) for a in rewrite["assumptions"]]):
                debug("assumption wasn't stmt")
                return False
        for (key, typ) in inner_keys:
            if key in keys:
                if not isinstance(rewrite[key], typ):
                    debug("f'{key}({rewrite[key]}) was not {typ}'")
                    return False
                rewrite.pop(key)
    elif is_split_proof(rw_kind):
        if "new_proofs" not in keys:
            debug("new_proofs not in keys")
            return False
        if not all(
                [
                    valid_rewrite_dict(rewrite_kind.IN_PLACE, p)
                    for p in rewrite["new_proofs"]
                ]):
            debug("subproof_check_failed")
            return False
        for (key, typ) in outer_keys:
            if key in keys:
                if not isinstance(rewrite[key], typ):
                    debug("f'{key}({rewrite[key]}) was not {typ}'")
                    return False
                rewrite.pop(key)
    else:
        debug(rw_kind)
        assert False, "Unrecognised enum value"
    debug(list(rewrite.keys()))
    assert list(rewrite.keys()) == [], "All keys should now have been removed"
    return True



def min_non_neg(*numbers):
    assert len(numbers)
    if len(numbers) == 1:
        return numbers[0]
    if len(numbers) == 2:
        a = numbers[0]
        b = numbers[1]
        if a < 0:
            return b
        if b < 0:
            return a
        return min(a, b)
    if a < 0:
        return min_non_neg(numbers[1:])
    else:
        return min(a, min_non_neg(numbers[1:]))
