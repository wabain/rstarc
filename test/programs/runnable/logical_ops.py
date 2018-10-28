#!/usr/bin/env python3
import os

fname = os.path.basename(__file__)

unary_ops = [
    ('not', lambda x: not x),
]

binary_ops = [
    ('and', lambda x, y: x and y),
    ('or', lambda x, y: x or y),
    ('nor', lambda x, y: (not x) and (not y)),
]

unary_inputs = [True, False]

binary_inputs = [
    (True, True),
    (False, True),
    (True, False),
    (False, False),
]

prelude = f'''\
(NOTE: This is generated code. Apply changes to {fname} and recompile)

(Test logic tables and short-circuiting)

SayTrue takes ArgId
    say ArgId
    give back true

SayFalse takes ArgId
    say ArgId
    give back false
'''

def main():
    print(prelude)

    generate_binary()
    generate_unary()


def generate_binary():
    for op, expected in binary_ops:
        for (in1, in2) in binary_inputs:
            base_id = f'{op}({int(in1)},{int(in2)})'

            arg1 = 'true' if in1 else 'false'

            fn2 = 'SayTrue' if in2 else 'SayFalse'
            arg2 = f'{fn2} taking "  {base_id}: eval2"'

            exp = expected(in1, in2)
            true_indicator = ' ' if exp else '!'
            false_indicator = '!' if exp else ' '

            print('if', arg1, op, arg2)
            print(f'    say "{true_indicator} {base_id}: TRUE"')
            print('else')
            print(f'    say "{false_indicator} {base_id}: FALSE"')
            print()


def generate_unary():
    for op, expected in unary_ops:
        for in_value in unary_inputs:
            base_id = f'{op}({int(in_value)})'

            arg = 'true' if in_value else 'false'

            exp = expected(in_value)
            true_indicator = ' ' if exp else '!'
            false_indicator = '!' if exp else ' '

            print('if', op, arg)
            print(f'    say "{true_indicator} {base_id}: TRUE"')
            print('else')
            print(f'    say "{false_indicator} {base_id}: FALSE"')
            print()


main()
