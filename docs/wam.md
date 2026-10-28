<!-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 -->
<!-- Copyright Ahmad Ali Parr -->

# WAM: a Warren Abstract Machine you send tokens to

*Etymology:* "WAM" is David H. D. Warren's 1983 abstract machine for Prolog.
"Token" is the old English *tacen*, a sign. The engine reads signs, one
word at a time, and does what they say.

The engine is `wam/wam.c`, one C99 file, built after Hassan Aït-Kaci's
tutorial: heap, argument and temporary registers, environment stack with
permanent variables, trail, choice points, read/write mode.
`wam/emit.pl` turns ordinary ISO Prolog into tokens.

```
cd wam
make                                   # builds ./wam
swipl -q emit.pl -- examples/append.pl | ./wam -all -
./wam examples/unify.tok
```

## Sending tokens

```
./wam [-all] [-trace] [file | -]
```

| Way to send | Command |
|---|---|
| a file | `./wam program.tok` |
| stdin | `./wam < program.tok` |
| a pipe that keeps talking | `producer \| ./wam -` |

- `-all` prints every answer of every query.
- Without `-all` the first answer is printed. If the next token is `;`, the
  engine gives the next answer. Each `;` asks once more.
- `-trace` prints every instruction as it runs, the registers, and what it
  did to the heap and trail. `runs/unify_trace.txt` is the trace of
  `examples/unify.tok`.

A query runs the moment its `halt` token arrives, so a producer can send a
program, then a query, read the answer, then send more.

## Answers

```
X = a
X = b, Y = c
A = tom, B = bob
Y = X
true
false
```

One line per answer. Variables named in the query print as `Name = term`.
A variable bound to another query variable prints as `Y = X`. A variable
that stays free inside a term prints as `_`. A query with nothing to show
prints `true`; no solution prints `false`.

## Token grammar

Tokens are separated by white space. `%` starts a comment that runs to the
end of the line.

```
program   = { label | instruction | query } .
label     = name "/" arity ":" .
query     = "query" { "name" Var Yk } { instruction } "halt" .
instruction = mnemonic { operand } .
```

A label names a predicate: `append/3:`. A second label inside a predicate
names a clause or a chain of clauses: `append/3#2:`. Atom names with spaces
or odd characters are quoted the Prolog way: `'hello world'/1:`.

### Operands

| Kind | Looks like |
|---|---|
| register | `X1` … `X1024`, or `Y1` … `Y4096` (`A1` is the same as `X1`) |
| constant | an atom `tom`, `[]`, a quoted atom `'a b'`, an integer `-3`, a float `2.5e3` |
| functor | `name/arity`, e.g. `f/2`, `'.'/2`, `'a b'/1` |
| number | a non-negative integer |
| label | `name/arity` or `name/arity#tag` |

Quoted atoms use `''` for a quote and `\\`, `\'`, `\n`, `\t`, `\xHH\`
as escapes.

### Instructions

Put (build arguments for a call):

| Token | Operands |
|---|---|
| `put_variable` | register, Xi |
| `put_value` | register, Xi |
| `put_unsafe_value` | Yn, Xi |
| `put_constant` | constant, Xi |
| `put_structure` | functor, Xi |
| `put_list` | Xi |

Get (take arguments apart in a clause head):

| Token | Operands |
|---|---|
| `get_variable` | register, Xi |
| `get_value` | register, Xi |
| `get_constant` | constant, Xi |
| `get_structure` | functor, Xi |
| `get_list` | Xi |

Set (write mode) and unify (read or write mode, by what is on the heap):

| Token | Operand |
|---|---|
| `set_variable`, `set_value`, `set_local_value` | register |
| `set_constant` | constant |
| `set_void` | number |
| `unify_variable`, `unify_value`, `unify_local_value` | register |
| `unify_constant` | constant |
| `unify_void` | number |

Control:

| Token | Operands |
|---|---|
| `allocate` | number of permanent variables |
| `deallocate`, `proceed`, `fail`, `halt` | none |
| `call`, `execute` | label |
| `try_me_else`, `retry_me_else` | label |
| `trust_me` | none |
| `try`, `retry`, `trust` | label |
| `switch_on_term` | four labels: variable, constant, list, structure; any may be `fail` |
| `get_level` | Yn |
| `cut` | Yn |
| `neck_cut` | none |

`get_level Yn` stores the choice point to cut back to; `cut Yn` cuts to it;
`neck_cut` is a cut at the first goal of a clause.

Built-in predicates are labels you `call` or `execute`:
`=/2`, `\=/2`, `==/2`, `\==/2`, `var/1`, `nonvar/1`, `atom/1`, `atomic/1`,
`integer/1`.

### Queries

```
query
  name X Y1          % show Y1 under the name X
  name Y Y2
  allocate 2
  put_variable Y1 X1
  ...
  call p/3
  halt
```

`name Var Yk` says which permanent register holds the query variable `Var`.
The answer prints it by that name.

### Errors

A malformed token is rejected with where it is and what is wrong:

```
file.tok:12:3: token 41 'get_costant': unknown instruction, label or directive
```

That is file, line, column, the token's number on its line, the token, and
the reason. From a file the engine stops at the first error. From stdin it
reports the error and reads on from the next line, so a producer that sends
one bad token can send the next one. A runtime fault (stack overflow, a call
to a label that does not exist) is reported the same way and the exit code
is 1.

## Prolog source: `emit.pl`

```
swipl -q emit.pl -- file.pl > file.tok
swipl -q emit.pl -- file.pl | ./wam -all -
swipl -q emit.pl -- - < file.pl | ./wam -all -
```

`emit.pl` reads plain ISO Prolog and writes the token program. swipl only
reads the text; the compilation is in `emit.pl`.

What it reads:

- the ISO operators and their precedences, and `op/3` directives
- quoted atoms and their escapes, `0'c` character codes, `0x`, `0o`, `0b`
  numbers, floats
- lists `[a,b]` and partial lists `[H|T]`, curly terms `{a,b}`
- double-quoted strings, as codes, chars or atom, by
  `:- set_prolog_flag(double_quotes, codes).`
- `% line` and `/* block */` comments

What it compiles:

- facts and rules
- conjunction `,`, disjunction `;` and `|`, if-then-else `( C -> T ; E )`,
  if-then `( C -> T )`, negation `\+ G`, cut `!`
- `=/2`, `\=/2`, `==/2`, `\==/2`, `var/1`, `nonvar/1`, `atom/1`, `atomic/1`,
  `integer/1`, `true`, `fail`
- `:- dynamic p/1.` declares a predicate with no clauses
- `?- Goal.` and `:- Goal.` become queries; each prints its answers

Clauses of one predicate are indexed on their first argument with
`switch_on_term`. Disjunction, if-then-else and negation become small helper
predicates (`$or1`, `$ite2`, `$not3`) that receive the clause's cut point, so
`!` inside them cuts the clause as Prolog says.

Errors name the file and line:

```
file.pl:7:10: syntax error: end_of_clause
file.pl:12: unknown procedure qux/1
```

The exit code is 1 when the source has an error and nothing is written to
stdout.

### The examples

| File | Shows |
|---|---|
| `examples/unify.tok` | the tutorial's unification, with `-trace` |
| `examples/ancestor.tok`, `.pl` | recursion over facts |
| `examples/append.tok`, `.pl` | lists, running forwards and backwards |
| `examples/member.tok`, `.pl` | backtracking through a list |
| `examples/cut.tok` | `get_level`, `cut`, `neck_cut` |
| `examples/control.pl` | cut, if-then-else, `\+`, `;` |
| `examples/syntax.pl` | quoted atoms, `0'c`, numbers, strings, curly terms, `op/3` |

`make run` writes every answer file to `runs/`. `make compare` also runs
`answers.pl`, which asks swipl itself the same queries, and checks that both
print the same lines.
