# RegexToolkit

This is a Java library for regular expressions and finite automata.
It includes a few applications that are useful for teaching
courses (see **User Interface** below).

It started out as an attempt to write a Java clone of RegeXeX:

http://sourceforge.net/projects/regexex/

http://dl.acm.org/citation.cfm?doid=1227310.1227462

I got as far as parsing regular expressions, converting them to finite
automata, and checking their equivalence: this is pretty useful for
grading regular expression assignments, since you can create
canonical solutions and then check students' regular expressions
against them.  Like RegeXeX, when regular expressions don't match
it will construct examples of strings that should be generated but
aren't, and strings that shouldn't be generated but are.

Unlike RegeXeX, there is no GUI, but I might get around to adding one
at some point.

## Building it

There is an Ant build file (**build.xml**).  Run the command `ant jar` to build **regexToolkit.jar**.

## User Interface

To run the program interactively, run

```bash
java -jar regexToolkit.jar command
```

where `command` is one of the following commands:

* `help`: Prints a usage summary.
* `check`: Allows the user to enter a regular expression
  and example strings.  For each string, prints **ACCEPT** or
  **REJECT** depending on whether it is or isn't in the language
  generated by the regular expression.  This is useful for students
  to use to test their regular expressions.
* `equiv`: Allows the user to compare
  two regular expressions to see if the are equivalent.
  If they are not, generates example strings in the
  set differences between them.  (I.e., strings in A but not in B,
  and strings in B but not in A.)
* `batchequiv`: Like `equiv`, but allows comparing multiple
  regular expressions to a single master regular expression.
* `grade`: Takes a solution file and a student file, each of
  which is a text file with one regular expression per line.
  Checks the equivalence of each pair of regular expressions
  and prints out a message stating whether they are equivalent,
  and if not, produces example strings illustrating the differences
  in the generated languages.  This is nice for grading
  an entire assignment (consisting of multiple regular expression
  problems.)

There is some other useful stuff if you poke around a bit.

The code is free software, distributed under the terms of the
[MIT license](http://opensource.org/licenses/MIT).

Feel free to email me if you have any feedback, and I hope you find this
stuff useful!

David Hovemeyer, <david.hovemeyer@gmail.com>
