#!/usr/bin/env python3

import operator as op
from collections import namedtuple

# A Rockstar value, with a Python value that will give
# an equivalent in-type ordering
RockstarValue = namedtuple('RockstarValue', 'value, py')

prelude = '''\
put 0 over 0 into NaN
'''


def main():
    print(prelude)

    N_0 = RockstarValue('0', 0.0)
    N_15 = RockstarValue('15', 15.0)
    N_NAN = RockstarValue('NaN', float('nan'))

    TRUE = RockstarValue('true', True)
    FALSE = RockstarValue('false', False)
    NULL = RockstarValue('null', 0)
    MYST = RockstarValue('mysterious', 0)

    comment('STRINGS')
    S_ = r_str('')
    S_A = r_str('a')
    S_AB = r_str('ab')
    S_B = r_str('b')

    gen_order_comparisons(S_A, S_A, conv=False)
    gen_order_comparisons(S_, S_A, conv=False)
    gen_order_comparisons(S_A, S_AB, conv=False)
    gen_order_comparisons(S_A, S_B, conv=False)

    comment('STRING COERCIONS')
    S_0 = r_str('0')
    S_OTHER = r_str('other')

    gen_order_comparisons(N_0, S_0, conv=(N_0, N_0))
    gen_order_comparisons(N_15, S_0, conv=(N_15, N_0))
    gen_order_comparisons(N_0, r_str('.0'), conv=(N_0, N_0))
    gen_order_comparisons(N_NAN, S_0, conv=(N_NAN, N_0))
    gen_order_comparisons(N_0, S_OTHER, conv=None)

    gen_order_comparisons(TRUE, r_str('yes'), conv=(TRUE, TRUE))
    gen_order_comparisons(FALSE, r_str('no'), conv=(FALSE, FALSE))
    gen_order_comparisons(TRUE, r_str('no'), conv=(TRUE, FALSE))
    gen_order_comparisons(TRUE, S_OTHER, conv=None)

    gen_order_comparisons(NULL, r_str('null'), conv=(NULL, NULL))  # FIXME: is this in the spec?
    gen_order_comparisons(NULL, S_OTHER, conv=None)

    gen_order_comparisons(MYST, r_str('mysterious'), conv=None)

    comment('NUMBERS')
    gen_order_comparisons(N_0, N_0, conv=False)
    gen_order_comparisons(N_0, N_15, conv=False)
    gen_order_comparisons(N_0, N_NAN, conv=False)

    comment('NUMBER COERCIONS')
    gen_order_comparisons(N_0, FALSE, conv=(FALSE, FALSE))
    gen_order_comparisons(N_15, FALSE, conv=(TRUE, FALSE))
    gen_order_comparisons(N_15, TRUE, conv=(TRUE, TRUE))
    gen_order_comparisons(N_NAN, FALSE, conv=(TRUE, FALSE))

    gen_order_comparisons(N_0, NULL, conv=(NULL, NULL))
    gen_order_comparisons(N_15, NULL, conv=None)

    comment('BOOLEANS')
    gen_order_comparisons(TRUE, TRUE, conv=False)
    gen_order_comparisons(FALSE, FALSE, conv=False)
    gen_order_comparisons(TRUE, FALSE, conv=False)

    comment('BOOLEAN COERCIONS')
    gen_order_comparisons(NULL, FALSE, conv=(NULL, NULL))
    gen_order_comparisons(NULL, TRUE, conv=None)

    comment('NULL')
    gen_order_comparisons(NULL, NULL, conv=False)

    comment('MYSTERIOUS')
    gen_order_comparisons(MYST, MYST, conv=False)

    comment('NO CONVERSION')
    gen_order_comparisons(NULL, MYST, conv=None)


def r_str(s):
    return RockstarValue(f'"{s}"', s)


def comment(s):
    print(f'( {s} )')


def gen_order_comparisons(v1, v2, conv):
    if conv is None:
        comment(f'Test {v1.value}, {v2.value}: no applicable conversion')
        test_comparison((v1, v2), lambda f: f == op.ne)
        test_comparison((v2, v1), lambda f: f == op.ne)
    elif conv is False:
        comment(f'Test {v1.value}, {v2.value}: no conversion needed')

        test_comparison((v1, v2), lambda f: f(v1.py, v2.py))
        if v1.value != v2.value:
            test_comparison((v2, v1), lambda f: f(v2.py, v1.py))
    else:
        c1, c2 = conv
        comment(f'Test {v1.value}, {v2.value}: convert to {c1.value}, {c2.value}')

        test_comparison((v1, v2), lambda f: f(c1.py, c2.py))
        if v1.value != v2.value:
            test_comparison((v2, v1), lambda f: f(c2.py, c1.py))


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


def esc(value):
    if value.value.startswith('"'):
        escaped = value.value.strip('"')
        return f'string({escaped})'
    return value.value


main()