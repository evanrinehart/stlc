Simply typed lambda calculus program.

Commands: `help list save load eval`

Definitions: `<letter> = <term>`

```
<term> = * | <var> | <term> <term> | \<var>:<type> -> <term>
<var> = <letter>
<type> = 1 | <type> -> <type>
```

A chain of `<term> <term> <term> ...` associates to the left.

A chain of `<type> -> <type> -> <type> -> ...` associates to the right.

Parentheses can be used in terms and types to override associativity.

`help` command - You're looking at it.

`list` command - Display the defined terms held in memory and their types.

`save` command - Save the defined terms to a file called 'floppy'.

`load` command - Clear all definitions and load those in file 'floppy'.

`eval <term>` command - Evaluate the term `<term>` within the environment.

Typing judgments. `<term> : <type>` means the term `<term>` has type `<type>`.

When a definition is entered, the program will check that the term is
well-typed in the context of previously entered terms. If there is a problem
during this process an error message will be printed and nothing new is
defined. Otherwise the term's type is printed and the definition is appended to
the environment.

Notable facts about simply typed lambda calculus. Once a definition is parsed and
type-checked within a given environment, evaluation always produces a normal
form in finite time. The normal form is unique and of the correct type.

* Datatypes, parsers, pretty printers - 101 lines
* Evaluator - 54 lines, complicated by substituting open terms
* Type checker - 39 lines
* REPL - 101 lines
* Help messages - 33 lines
