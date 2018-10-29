#!/usr/bin/env python3

import operator as op
from collections import namedtuple

RockstarType = namedtuple('RockstarType', 'name, coercions, conv')
RockstarValue = namedtuple('RockstarType', 'value, ty')

true_literals = ["true", "right", "yes", "ok"]
false_literals = ["false", "wrong", "no", "lies"]
null_literals = ["null", "nothing", "nowhere", "nobody", "empty", "gone"]


def none_on_err(fn):
    try:
        return fn()
    except (TypeError, ValueError):
        return None


type_list = [
    RockstarType('string', {
        'number': lambda s: none_on_err(lambda: float(s)),
        'boolean': lambda s: 'true' if s in true_literals else 'false' if s in false_literals else None,
        'null': lambda s: 'null' if s in null_literals else None,
    }, lambda s: s.strip('"')),
    RockstarType('number', {
        'boolean': lambda n: 'false' if (n == 0.0) else 'true',
        'null': lambda n: 'null' if n == 0.0 else None,
    }, lambda n: float(n)),
    RockstarType('boolean', {
        'null': lambda b: 'null' if not b else None
    }, lambda b: (b == 'true')),
    RockstarType('null', {}, lambda _: 0),
    RockstarType('mysterious', {}, lambda _: 0),
]

types = { t.name: t for t in type_list }


values = [
    RockstarValue('"0"', types['string']),
    RockstarValue('".0"', types['string']),
    # RockstarValue('"-10"', types['string']),
    RockstarValue('"yes"', types['string']),
    RockstarValue('"no"', types['string']),
    RockstarValue('"null"', types['string']),
    RockstarValue('"other"', types['string']),

    RockstarValue('0', types['number']),
    RockstarValue('10', types['number']),
    # RockstarValue('-10', types['number']),
    # Defined in test prelude
    RockstarValue('NaN', types['number']),

    RockstarValue('true', types['boolean']),
    RockstarValue('false', types['boolean']),
    RockstarValue('null', types['null']),
    RockstarValue('mysterious', types['mysterious']),
]

prelude = '''\
put 0 over 0 into NaN
'''


def main():
    print(prelude)
    no_type_conversion_pairs = set()
    for v1 in values:
        for v2 in values:
            generate_order_comparisons(v1, v2, no_type_conversion_pairs)


def generate_order_comparisons(v1, v2, no_type_conversion_pairs):
    coerced = apply_coercion(v1, v2)

    if coerced is None:
        tys = (v1.ty.name, v2.ty.name)
        if tys in no_type_conversion_pairs:
            return
        else:
            no_type_conversion_pairs.add(tys)

        print('(Expected: no applicable conversion)')
        test_comparison((v1, v2), lambda f: f == op.ne)
    else:
        c1 = coerced[0].ty.conv(coerced[0].value)
        c2 = coerced[1].ty.conv(coerced[1].value)

        print(f'(Expected: converted to {c1}, {c2})')
        test_comparison((v1, v2), lambda f: f(c1, c2))


def test_comparison(vals, t):
    (v1, v2) = vals

    verify_expr(v1, v2, t(op.lt), 'is less than', '<')
    verify_expr(v1, v2, t(op.le), 'is as little as', '<=')
    verify_expr(v1, v2, t(op.gt), 'is greater than', '>')
    verify_expr(v1, v2, t(op.ge), 'is as great as', '>=')
    verify_expr(v1, v2, t(op.eq), 'is', 'is')
    verify_expr(v1, v2, t(op.ne), 'isnt', 'isnt')


def verify_expr(v1, v2, expected, expr, tag):
    fail_check = 'not Result' if expected else 'Result'
    fail_res = 'FALSE' if expected else 'TRUE'
    print(
        f'put {v1.value} {expr} {v2.value} into Result\n'
        f'if {fail_check}\n'
        f'    say "! {fail_res}: {esc(v1)} {tag} {esc(v2)}"\n'
        #f'if {v1.value} {expr} {v2.value}\n'
        #f'    say "{true_mark} TRUE: {esc(v1)} {tag} {esc(v2)}"\n'
        #f'else\n'
        #f'    say "{false_mark} FALSE: {esc(v1)} {tag} {esc(v2)}"\n'
    )


def apply_coercion(v1, v2):
    t1 = v1.ty.name
    t2 = v2.ty.name

    if t1 == t2:
        return v1, v2

    assert not (t1 in v2.ty.coercions and t2 in v1.ty.coercions), \
        f'mutually convertible: {t1}, {t2}'

    if t1 in v2.ty.coercions:
        v2 = coerce_value(v2, v1.ty)

    elif t2 in v1.ty.coercions:
        v1 = coerce_value(v1, v2.ty)

    else:
        v1 = v2 = None

    if v1 is None or v2 is None:
        return None

    return v1, v2


def coerce_value(value, dest_ty):
    conv = value.ty.conv(value.value)
    coerced = value.ty.coercions[dest_ty.name](conv)
    if coerced is None:
        return None
    return RockstarValue(coerced, dest_ty)


def esc(value):
    if value.ty == types['string']:
        escaped = value.value.strip('"')
        return f'string({escaped})'
    return value.value



main()