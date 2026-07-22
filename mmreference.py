'''
mmreference.py - simple conformant Metamath verifier

Originally written in 2026 by Matthew House

To the extent possible under law, the author(s) have dedicated all copyright and
related and neighboring rights to this software to the public domain worldwide.
This software is distributed without any warranty.

You should have received a copy of the CC0 Public Domain Dedication along with
this software. If not, see <http://creativecommons.org/publicdomain/zero/1.0/>. 
'''

from dataclasses import dataclass
import os
from pathlib import Path
import sys
sys.setrecursionlimit(0x7fffffff)
sys.stdout.reconfigure(encoding=sys.getfilesystemencoding(), errors=sys.getfilesystemencodeerrors())

class VerifyError(Exception):
    pass
@dataclass
class Cursor:
    file: Path
    buf: bytes
    pos: int
@dataclass
class Hyp:
    label: bytes
    head: bytes
    string: list[bytes]
@dataclass
class Frame:
    dvs: list[tuple[bytes, bytes]]
    hyps: list[Hyp]
    assrt: list[bytes]

def is_ws(b):
    return b in b'\t\n\f\r '
def is_math(tok):
    return b'$' not in tok
def is_label(tok):
    return all(0x30 <= b <= 0x39 or 0x41 <= b <= 0x5a or 0x61 <= b <= 0x7a or b in b'-._' for b in tok)

def verify(filename):
    try:
        seen_files = set()
        cursors = []
        def push_file(filename):
            file = cursors[-1].file / filename if cursors else Path(filename)
            try:
                absfile = str(file.resolve())
            except OSError:
                raise VerifyError('could not resolve included file')
            if absfile in seen_files:
                return False
            seen_files.add(absfile)
            try:
                buf = file.read_bytes()
            except OSError:
                raise VerifyError('could not read included file')
            cursors.append(Cursor(file=file.parent, buf=buf, pos=0))
            return True
        push_file(filename)
        def read1(cursor):
            while True:
                while cursor.pos != len(cursor.buf) and is_ws(cursor.buf[cursor.pos]):
                    cursor.pos += 1
                if cursor.pos == len(cursor.buf):
                    return
                start = cursor.pos
                while cursor.pos != len(cursor.buf) and not is_ws(cursor.buf[cursor.pos]):
                    if not 0x21 <= cursor.buf[cursor.pos] <= 0x7e:
                        raise VerifyError('bad character')
                    cursor.pos += 1
                yield cursor.buf[start:cursor.pos]
        def read2(cursor):
            in_comment = False
            for tok in read1(cursor):
                if in_comment:
                    if tok == b'$)':
                        in_comment = False
                    elif b'$(' in tok or b'$)' in tok:
                        raise VerifyError('bad token in comment')
                else:
                    if tok == b'$(':
                        in_comment = True
                    else:
                        yield tok
            if in_comment:
                raise VerifyError('within comment at end of file')
        in_statement = False
        block_depth = 0
        def read3():
            toks = read2(cursors[-1])
            for tok in toks:
                if tok == b'$[':
                    if in_statement:
                        raise VerifyError('file inclusion within statement')
                    if block_depth != 0:
                        raise VerifyError('file inclusion within non-outermost block')
                    tok = next(toks, None)
                    if tok is None:
                        raise VerifyError('within file inclusion at end of file')
                    if not is_math(tok):
                        raise VerifyError('bad filename in file inclusion')
                    if push_file(os.fsdecode(tok)):
                        yield from read3()
                    tok = next(toks, None)
                    if tok is None:
                        raise VerifyError('within file inclusion at end of file')
                    if tok != b'$]':
                        raise VerifyError('bad filename in file inclusion')
                else:
                    yield tok
            if in_statement:
                raise VerifyError('within statement at end of file')
            if block_depth != 0:
                raise VerifyError('within non-outermost block at end of file')
        toks = read3()
        def read_until(end):
            for tok in toks:
                if tok == end:
                    break
                yield tok
        declared_labels = {}
        declared_math = set()
        declared_consts = set()
        var_typecodes = {}
        active_vars = set()
        var_scopes = [[]]
        active_dvs = set()
        dv_scopes = [[]]
        active_f_vars = {}
        active_f_hyps = {}
        f_var_scopes = [[]]
        active_e_hyps = {}
        e_hyp_scopes = [[]]
        active_frames = {}
        has_unknown_proofs = False
        def collect_frame(assrt):
            mand_vars = set()
            for sym in assrt:
                if sym not in declared_consts:
                    mand_vars.add(sym)
            hyps = []
            for hyp in active_e_hyps:
                hyps.append(Hyp(label=hyp, head=b'$e', string=active_e_hyps[hyp]))
                for sym in active_e_hyps[hyp]:
                    if sym not in declared_consts:
                        mand_vars.add(sym)
            for var in mand_vars:
                hyp = active_f_vars[var]
                hyps.append(Hyp(label=hyp, head=b'$f', string=active_f_hyps[hyp]))
            hyps.sort(key=lambda hyp: declared_labels[hyp.label])
            dvs = []
            for dv in active_dvs:
                if dv[0] in mand_vars and dv[1] in mand_vars:
                    dvs.append(dv)
            return Frame(dvs=dvs, hyps=hyps, assrt=assrt)
        def read_math_string(end, ctx, needs_types=True):
            typecode = next(toks)
            if typecode == end:
                raise VerifyError(f'empty math string in {ctx}')
            if not is_math(typecode):
                raise VerifyError(f'bad math symbol in {ctx}')
            if typecode not in declared_math:
                raise VerifyError(f'undeclared math symbol in {ctx}')
            if typecode not in declared_consts:
                raise VerifyError(f'variable typecode in {ctx}')
            string = [typecode]
            for sym in read_until(end):
                if not is_math(sym):
                    raise VerifyError(f'bad math symbol in {ctx}')
                if sym not in declared_math:
                    raise VerifyError(f'undeclared math symbol in {ctx}')
                if sym not in declared_consts and sym not in active_vars:
                    raise VerifyError(f'inactive variable in {ctx}')
                if needs_types and sym in active_vars and sym not in active_f_vars:
                    raise VerifyError(f'variable without active type in {ctx}')
                string.append(sym)
            return string
        def apply_substs(string, substs):
            subst = []
            for sym in string:
                if sym in declared_consts:
                    subst.append(sym)
                else:
                    subst += substs[sym]
            return subst
        def proof_step(stack, frame):
            if len(frame.hyps) > len(stack):
                raise VerifyError('stack underflow in proof')
            start = len(stack) - len(frame.hyps)
            substs = {}
            for i in range(len(frame.hyps)):
                hyp = frame.hyps[i]
                entry = stack[start + i]
                if hyp.head == b'$f':
                    if hyp.string[0] != entry[0]:
                        raise VerifyError('variable type mismatch in proof')
                    substs[hyp.string[1]] = entry[1:]
                else:
                    if apply_substs(hyp.string, substs) != entry:
                        raise VerifyError('hypothesis mismatch in proof')
            del stack[start:]
            for (var1, var2) in frame.dvs:
                for sym1 in substs[var1]:
                    if sym1 not in declared_consts:
                        for sym2 in substs[var2]:
                            if sym2 not in declared_consts:
                                if sym1 == sym2:
                                    raise VerifyError('DV condition violated in proof')
                                target_dv = (sym1, sym2) if sym1 < sym2 else (sym2, sym1)
                                if target_dv not in active_dvs:
                                    raise VerifyError('DV condition not satisfied in proof')
            stack.append(apply_substs(frame.assrt, substs))
        for head in toks:
            if head == b'${':
                block_depth += 1
                var_scopes.append([])
                dv_scopes.append([])
                f_var_scopes.append([])
                e_hyp_scopes.append([])
                continue
            if head == b'$}':
                if block_depth == 0:
                    raise VerifyError('outermost block closed')
                block_depth -= 1
                active_vars.difference_update(var_scopes.pop())
                active_dvs.difference_update(dv_scopes.pop())
                for var in f_var_scopes.pop():
                    del active_f_hyps[active_f_vars[var]]
                    del active_f_vars[var]
                for label in e_hyp_scopes.pop():
                    del active_e_hyps[label]
                continue
            in_statement = True
            if head == b'$c':
                if block_depth != 0:
                    raise VerifyError('constant declaration within non-outermost block')
                is_empty = True
                for sym in read_until(b'$.'):
                    is_empty = False
                    if not is_math(sym):
                        raise VerifyError('bad math symbol in constant declaration')
                    if sym in declared_labels:
                        raise VerifyError('label token in constant declaration')
                    if sym in declared_math:
                        raise VerifyError('declared math symbol in constant declaration')
                    declared_math.add(sym)
                    declared_consts.add(sym)
                if is_empty:
                    raise VerifyError('empty constant declaration')
                in_statement = False
                continue
            if head == b'$v':
                is_empty = True
                for sym in read_until(b'$.'):
                    is_empty = False
                    if not is_math(sym):
                        raise VerifyError('bad math symbol in variable declaration')
                    if sym in declared_labels:
                        raise VerifyError('label token in variable declaration')
                    if sym in declared_consts:
                        raise VerifyError('constant symbol in variable declaration')
                    if sym in active_vars:
                        raise VerifyError('active variable in variable declaration')
                    declared_math.add(sym)
                    active_vars.add(sym)
                    var_scopes[-1].append(sym)
                if is_empty:
                    raise VerifyError('empty variable declaration')
                in_statement = False
                continue
            if head == b'$d':
                dv_vars = []
                for sym in read_until(b'$.'):
                    if not is_math(sym):
                        raise VerifyError('bad math symbol in DV statement')
                    if sym not in declared_math:
                        raise VerifyError('undeclared math symbol in DV statement')
                    if sym in declared_consts:
                        raise VerifyError('constant symbol in DV statement')
                    if sym not in active_vars:
                        raise VerifyError('inactive variable in DV statement')
                    dv_vars.append(sym)
                if len(dv_vars) < 2:
                    raise VerifyError('too few variables in DV statement')
                for i in range(len(dv_vars)):
                    var1 = dv_vars[i]
                    for j in range(i + 1, len(dv_vars)):
                        var2 = dv_vars[j]
                        if var1 == var2:
                            raise VerifyError('repeated variable in DV statement')
                        dv = (var1, var2) if var1 < var2 else (var2, var1)
                        if dv not in active_dvs:
                            active_dvs.add(dv)
                            dv_scopes[-1].append(dv)
                in_statement = False
                continue
            label = head
            if not is_label(label):
                raise VerifyError('bad label token outside of statement')
            if label in declared_math:
                raise VerifyError('declared math symbol used as statement label')
            if label in declared_labels:
                raise VerifyError('declared label token reused as statement label')
            head = next(toks)
            if head == b'$f':
                string = read_math_string(b'$.', 'floating hypothesis', needs_types=False)
                if len(string) == 1:
                    raise VerifyError('missing variable in floating hypothesis')
                if len(string) != 2:
                    raise VerifyError('too many symbols in floating hypothesis')
                typecode, var = string
                if var in declared_consts:
                    raise VerifyError('constant as variable in floating hypothesis')
                if var in active_f_vars:
                    raise VerifyError('multiple active floating hypotheses')
                if var in var_typecodes and var_typecodes[var] != typecode:
                    raise VerifyError('typecode mismatch in floating hypotheses')
                declared_labels[label] = len(declared_labels)
                var_typecodes[var] = typecode
                active_f_vars[var] = label
                active_f_hyps[label] = [typecode, var]
                f_var_scopes[-1].append(var)
                in_statement = False
                continue
            if head == b'$e':
                string = read_math_string(b'$.', 'essential hypothesis')
                declared_labels[label] = len(declared_labels)
                active_e_hyps[label] = string
                e_hyp_scopes[-1].append(label)
                in_statement = False
                continue
            if head == b'$a':
                string = read_math_string(b'$.', 'axiom statement')
                frame = collect_frame(string)
                declared_labels[label] = len(declared_labels)
                active_frames[label] = frame
                in_statement = False
                continue
            if head == b'$p':
                string = read_math_string(b'$=', 'proof statement')
                frame = collect_frame(string)
                stack = []
                proof_toks = [*read_until(b'$.')]
                has_unknown_step = False
                if proof_toks and proof_toks[0] == b'(':
                    pos = 1
                    saved_steps = [hyp.string for hyp in frame.hyps]
                    while pos != len(proof_toks) and proof_toks[pos] != b')':
                        lab = proof_toks[pos]
                        pos += 1
                        if not is_label(lab):
                            raise VerifyError('bad label token in compressed proof')
                        if lab not in declared_labels:
                            raise VerifyError('undeclared label token in compressed proof')
                        if any(lab == hyp.label for hyp in frame.hyps):
                            raise VerifyError('mandatory hypothesis label in compressed proof')
                        if lab in active_frames:
                            saved_steps.append(active_frames[lab])
                        elif lab in active_f_hyps:
                            saved_steps.append(active_f_hyps[lab])
                        else:
                            raise VerifyError('inactive hypothesis label in compressed proof')
                    if pos == len(proof_toks):
                        raise VerifyError('unclosed label section in compressed proof')
                    pos += 1
                    proof_letters = bytearray()
                    while pos != len(proof_toks):
                        for letter in proof_toks[pos]:
                            if not (0x41 <= letter <= 0x5a or letter == 0x3f):
                                raise VerifyError('bad letter in compressed proof')
                            proof_letters.append(letter)
                        pos += 1
                    proof_numbers = []
                    number = 0
                    for letter in proof_letters:
                        if 0x41 <= letter <= 0x54:
                            proof_numbers.append(20*number + (letter - 0x41))
                            number = 0
                        elif 0x55 <= letter <= 0x59:
                            number = 5*number + (letter - 0x54)
                        else:
                            if number != 0:
                                raise VerifyError('incomplete number in compressed proof')
                            if letter == 0x3f:
                                proof_numbers.append(-2)
                            elif letter == 0x5a:
                                proof_numbers.append(-1)
                    if number != 0:
                        raise VerifyError('incomplete number in compressed proof')
                    for number in proof_numbers:
                        if number == -2:
                            has_unknown_step = True
                            break
                        if number == -1:
                            if not stack:
                                raise VerifyError('tagged empty stack in compressed proof')
                            saved_steps.append(stack[-1])
                            continue
                        if number >= len(saved_steps):
                            raise VerifyError('nonexistent step number in compressed proof')
                        if isinstance(saved_steps[number], Frame):
                            proof_step(stack, saved_steps[number])
                        else:
                            stack.append(saved_steps[number])
                else:
                    for lab in proof_toks:
                        if lab == b'?':
                            continue
                        if not is_label(lab):
                            raise VerifyError('bad label token in proof')
                        if lab not in declared_labels:
                            raise VerifyError('undeclared label token in proof')
                        if lab not in active_frames and lab not in active_f_hyps and lab not in active_e_hyps:
                            raise VerifyError('inactive hypothesis label in proof')
                    for lab in proof_toks:
                        if lab == b'?':
                            has_unknown_step = True
                            break
                        if lab in active_frames:
                            proof_step(stack, active_frames[lab])
                        elif lab in active_f_hyps:
                            stack.append(active_f_hyps[lab])
                        elif lab in active_e_hyps:
                            stack.append(active_e_hyps[lab])
                if has_unknown_step:
                    has_unknown_proofs = True
                else:
                    if not stack:
                        raise VerifyError('empty stack at end of proof')
                    if len(stack) != 1:
                        raise VerifyError('too many stack entries at end of proof')
                    if stack[0] != string:
                        raise VerifyError('stack entry mismatch at end of proof')
                declared_labels[label] = len(declared_labels)
                active_frames[label] = frame
                in_statement = False
                continue
            raise VerifyError('bad statement keyword after label')
        if has_unknown_proofs:
            return 'warn', 'database has proofs with unknown steps'
        else:
            return 'verify', None
    except VerifyError as err:
        return 'error', str(err)

for filename in sys.argv[1:]:
    result, message = verify(filename)
    if message is not None:
        print(f'{result}\t{filename}\t{message}')
    else:
        print(f'{result}\t{filename}')
