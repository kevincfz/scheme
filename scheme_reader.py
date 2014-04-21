"""This module implements the built-in data types of the Scheme language, along
with a parser for Scheme expressions.

In addition to the types defined in this file, some data types in Scheme are
represented by their corresponding type in Python:
    number:       int or float
    symbol:       string
    boolean:      bool
    unspecified:  None

The __repr__ method of a Scheme value will return a Python expression that
would be evaluated to the value, where possible.

The __str__ method of a Scheme value will return a Scheme expression that
would be read to the value, where possible.
"""

from ucb import main, trace, interact
from scheme_primitives import Pair, nil, intern, scnum, scstr, scbool
from scheme_tokens import tokenize_lines, DELIMITERS
from buffer import Buffer, InputReader, LineReader

# Scheme list parser


def scheme_read(src):
    """Read the next expression from SRC, a Buffer of tokens.

    >>> lines = ["(+ 1 ", "(+ 23 4)) ("]
    >>> src = Buffer(tokenize_lines(lines))
    >>> print(scheme_read(src))
    (+ 1 (+ 23 4))
    >>> read_line("'hello")
    Pair('quote', Pair('hello', nil))
    >>> print(read_line("(car '(1 2))"))
    (car (quote (1 2)))
    """
    if src.current() is None:
        raise EOFError
    val = src.pop()
    if val == "nil":
        return nil
    elif type(val) is int or type(val) is float:
        return scnum(val)
    elif type(val) is bool:
        return scbool(val)
    elif val not in DELIMITERS:
        if val[0] == '"':
            return scstr(eval(val))
        else:
            return intern(val)
    elif val == "'":
        "*** YOUR CODE HERE ***"
    elif val == "(":
        return read_tail(src)
    else:
        raise SyntaxError("unexpected token: {0}".format(val))

def read_tail(src):
    """Return the remainder of a list in SRC, starting before an element or ).

    >>> read_tail(Buffer(tokenize_lines([")"])))
    nil
    >>> read_tail(Buffer(tokenize_lines(["2 3)"])))
    Pair(2, Pair(3, nil))
    >>> read_tail(Buffer(tokenize_lines(["2 (3 4))"])))
    Pair(2, Pair(Pair(3, Pair(4, nil)), nil))
    >>> read_line("(1 . 2)")
    Pair(1, 2)
    >>> read_line("(1 2 . 3)")
    Pair(1, Pair(2, 3))
    >>> read_line("(1 . 2 3)")
    Traceback (most recent call last):
        ...
    SyntaxError: Expected one element after .
    >>> scheme_read(Buffer(tokenize_lines(["(1", "2 .", "'(3 4))", "4"])))
    Pair(1, Pair(2, Pair('quote', Pair(Pair(3, Pair(4, nil)), nil))))

    "'"
    """
    try:
        if src.current() is None:
            raise SyntaxError("unexpected end of file")
        if src.current() == ")":
            src.pop()
            return nil
        "*** YOUR CODE HERE ***"
        first = scheme_read(src)
        rest = read_tail(src)
        return Pair(first, rest)
    except EOFError:
        raise SyntaxError("unexpected end of file")

# Convenience methods

def buffer_input(prompt="scm> "):
    """Return a Buffer instance containing interactive input."""
    return Buffer(tokenize_lines(InputReader(prompt)))

def buffer_lines(lines, prompt="scm> ", show_prompt=False):
    """Return a Buffer instance iterating through LINES."""
    if show_prompt:
        input_lines = lines
    else:
        input_lines = LineReader(lines, prompt)
    return Buffer(tokenize_lines(input_lines))

def read_line(line):
    """Read a single string LINE as a Scheme expression."""
    return scheme_read(Buffer(tokenize_lines([line])))

# Interactive loop

@main
def read_print_loop():
    """Run a read-print loop for Scheme expressions."""
    while True:
        try:
            src = buffer_input("read> ")
            while src.more_on_line:
                expression = scheme_read(src)
                print(expression)
                print(repr(expression))
        except (SyntaxError, ValueError) as err:
            print(type(err).__name__ + ":", err)
        except (KeyboardInterrupt, EOFError):  # <Control>-D, etc.
            return
