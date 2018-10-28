#!/usr/bin/env python3
import os

fname = os.path.basename(__file__)

binary_ops = [
    ('and', lambda x, y: x and y),
    ('or', lambda x, y: x or y),
]

binary_inputs = [
    (True, True),
    (False, True),
    (True, False),
    (False, False),
]

# Prelude
print(f'''\
(NOTE: This is generated code. Apply changes to {fname} and recompile)

(Test logic tables and short-circuiting)

SayTrue takes ArgId
    say ArgId
    give back true

SayFalse takes ArgId
    say ArgId
    give back false
''')

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
