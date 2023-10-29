Simply typed lambda calculus program.

Commands: `help list save load eval`

Definitions: `<letter> = <term>`

```
<term> = * | <var> | <term> <term> | \<var>:<type> -> <term>
<var> = <letter>
<type> = 1 | <type> -> <type>
```

a chain of `<term> <term> <term> ...` associates to the left
a chain of `<type> -> <type> -> <type> -> ...` associates to the right
parentheses can be used in terms and types to override associativity

`help` command - you're looking at it

`list` command - display the defined terms held in memory and their types

`save` command - save the defined terms to a file called 'floppy'

`load` command - clear all definitions and load those in file 'floppy'

`eval <letter>` command - evaluate the term `<letter>` found in the environment

Typing judgments. `<term> : <type>` means the term `<term>` has type `<type>`.

When a definition is entered, the program will check that the term is
well-typed in the context of previously terms entered. If there is a problem
during this process an error message will be printed and nothing new is
defined. Otherwise the term's type is printed and the definition is appended to
the environment.
