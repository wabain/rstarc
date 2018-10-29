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

prelude = '''\
put 0 over 0 into NaN
'''


def main():
    print(prelude)

    N_0 = RockstarValue('0', types['number'])
    N_15 = RockstarValue('15', types['number'])
    N_NAN = RockstarValue('NaN', types['number'])

    TRUE = RockstarValue('true', types['boolean'])
    FALSE = RockstarValue('false', types['boolean'])
    NULL = RockstarValue('null', types['null'])
    MYST = RockstarValue('mysterious', types['mysterious'])

    comment('STRINGS')
    S_ = RockstarValue('""', types['string'])
    S_A = RockstarValue('"a"', types['string'])
    S_AB = RockstarValue('"ab"', types['string'])
    S_B = RockstarValue('"b"', types['string'])

    gen_order_comparisons(S_A, S_A)
    gen_order_comparisons(S_, S_A)
    gen_order_comparisons(S_A, S_AB)
    gen_order_comparisons(S_A, S_B)

    comment('STRING COERCIONS')
    S_0 = RockstarValue('"0"', types['string'])
    S_OTHER = RockstarValue('"other"', types['string'])

    gen_order_comparisons(N_0, S_0)
    gen_order_comparisons(N_15, S_0)
    gen_order_comparisons(N_0, RockstarValue('".0"', types['string']))
    gen_order_comparisons(N_NAN, S_0)
    gen_order_comparisons(N_0, S_OTHER)

    gen_order_comparisons(TRUE, RockstarValue('"yes"', types['string']))
    gen_order_comparisons(FALSE, RockstarValue('"no"', types['string']))
    gen_order_comparisons(TRUE, RockstarValue('"no"', types['string']))
    gen_order_comparisons(TRUE, S_OTHER)

    gen_order_comparisons(NULL, RockstarValue('"null"', types['string']))  # XXX is this a thing?
    gen_order_comparisons(NULL, S_OTHER)

    gen_order_comparisons(MYST, RockstarValue('"mysterious"', types['string']))

    comment('NUMBERS')
    gen_order_comparisons(N_0, N_0)
    gen_order_comparisons(N_0, N_15)
    gen_order_comparisons(N_0, N_NAN)

    comment('NUMBER COERCIONS')
    gen_order_comparisons(N_0, FALSE)
    gen_order_comparisons(N_15, FALSE)
    gen_order_comparisons(N_15, TRUE)
    gen_order_comparisons(N_NAN, FALSE)

    gen_order_comparisons(N_0, NULL)
    gen_order_comparisons(N_15, NULL)

    comment('BOOLEANS')
    gen_order_comparisons(TRUE, TRUE)
    gen_order_comparisons(FALSE, FALSE)
    gen_order_comparisons(TRUE, FALSE)

    comment('BOOLEAN COERCIONS')
    gen_order_comparisons(NULL, FALSE)
    gen_order_comparisons(NULL, TRUE)

    comment('NULL')
    gen_order_comparisons(NULL, NULL)

    comment('MYSTERIOUS')
    gen_order_comparisons(MYST, MYST)

    comment('NO CONVERSION')
    gen_order_comparisons(NULL, MYST)


def comment(s):
    print(f'( {s} )')


def gen_order_comparisons(v1, v2):
    initial = (v1, v2)
    coerced = apply_coercion(v1, v2)

    if coerced is None:
        comment(f'Test {v1.value}, {v2.value}: no applicable conversion')
        test_comparison((v1, v2), lambda f: f == op.ne)
        test_comparison((v2, v1), lambda f: f == op.ne)
    else:
        c1 = coerced[0].ty.conv(coerced[0].value)
        c2 = coerced[1].ty.conv(coerced[1].value)

        if initial == coerced:
            comment(f'Test {v1.value}, {v2.value}: no conversion needed')
        else:
            comment(f'Test {v1.value}, {v2.value}: convert to {coerced[0].value}, {coerced[1].value}')

        test_comparison((v1, v2), lambda f: f(c1, c2))
        if v1.value != v2.value:
            test_comparison((v2, v1), lambda f: f(c2, c1))


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