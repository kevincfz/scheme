"""This module implements the primitives of the Scheme language."""

import math
import operator
import sys
import numbers
import re

try:
    import turtle
except:
    print("warning: could not import the turtle module.", file=sys.stderr)

#############################
# Errors and Error Checking #
#############################

class SchemeError(Exception):
    """Exception indicating an error in a Scheme program."""

def bad_type(val, k, name):
    """Raise a SchemeError using "argument K of NAME" to describe the
    offending value (VAL)."""
    msg = "argument {0} of {1} has wrong type ({2})"
    raise SchemeError(msg.format(k, name, type(val).__name__))

def check_type(val, predicate, k, name):
    """Returns VAL.  Raises a SchemeError if not PREDICATE(VAL)
    using "argument K of NAME" to describe the offending value."""
    if not predicate(val):
        bad_type(val, k, name)
    return val

#################
# Scheme Values #
#################

# Every value used in the interpreter to represent a Scheme value "is a"
# SchemeValue.  Thus, if x is such a value, isinstance(x, SchemeValue).
# In proper object-oriented fashion, however, you will only need to use
# this test in 'assert' statements that catch bugs in your interpreter.
# The SchemeValue class has methods for testing for Scheme integers,
# procedures, etc.  The SchemeValue class documents these methods by
# giving default 'def's for all of them.  The various subclasses of
# SchemeValue, which stand for Scheme integers, Scheme pairs, etc., override
# these methods with appropriate methods of their own.

# As an example, consider the method pairp (returns a true Scheme value iff
# its argument is a pair).  The default definition (in SchemeValue) returns
# scheme_false (which represents #f).  Most subtypes of SchemeValue simply
# inherit this definition, and so also return #f.  The type Pair, however,
# overrides pairp to return scheme_true (which represents #t).  As a result,
# No 'if' statements are necessary to check for pairs.

# In other examples, such as the length method, the default implementation
# causes an error, since length is defined only for proper lists (so it
# is overridden in the classes Pair and Nil).

class SchemeValue:
    """The parent class of all Scheme values manipulated by the interpreter.
    The methods here give default implementations, and are overridden in the
    subclasses of SchemeValue."""
    
    def __bool__(self):
        """True if I am supposed to count as a "true value" in Python.  This
        is the method used by Python's conditionals (if, and, or, not, while)
        to determine whether some value is to be treated as meaning 'true'.
        As a result, any SchemeValue that Scheme considers to represent true
        also means true to Python.  It is therefore unnecessary in Python to
        write things like 'if EXPRESSION is not scheme_false: ...'"""
        return True

    def print_repr(self):
        """The string printed for me by the Scheme 'print' procedure."""
        return str(self)

    # The following methods return SchemeValues.  Those ending in 'p' (for
    # 'predicate') return scheme_false to mean 'false', and some other
    # SchemeValue (often scheme_true) to mean 'true'.

    def booleanp(self):
        return scheme_false

    def notp(self):
        return scbool(not self)

    def eqp(self, y):
        return scbool(self is y)

    def eqvp(self, y):
        """True iff I am equivalent to Y (same object, same numeric or boolean
        value."""
        return scbool(self is y)

    def equalp(self, y):
        """True iff I am equal in value to Y."""
        return scbool(self == y)

    def atomp(self):
        return scheme_true

    def pairp(self):
        return scheme_false

    def nullp(self):
        return scheme_false

    def listp(self):
        return scheme_false
    
    def length(self):
        bad_type(self, 0, "length")

    def neg(self):
        """Unary negation (as in -x), returning a SchemeValue."""
        bad_type(self, 0, "sub")

    def quo(self, y):
        bad_type(self, 0, "quotient")

    def modulo(self, y):
        bad_type(self, 0, "modulo")

    def rem(self, y):
        bad_type(self, 0, "remainder")

    def floor(self):
        bad_type(self, 0, "floor")

    def ceil(self):
        bad_type(self, 0, "ceil")

    def eq(self, y):
        bad_type(self, 0, "=")

    def ltp(self, y):
        bad_type(self, 0, "<")

    def gtp(self, y):
        bad_type(self, 0, ">")

    def lep(self, y):
        bad_type(self, 0, "<=")

    def gep(self, y):
        bad_type(self, 0, ">=")

    def evenp(self):
        bad_type(self, 0, "even?")

    def oddp(self):
        bad_type(self, 0, "odd?")

    def zerop(self):
        bad_type(self, 0, "zero?")

    def cons(self, y):
        return Pair(self, y)

    def append(self, y):
        bad_type(self, 0, "append")

    def car(self):
        bad_type(self, 0, "car")

    def cdr(self):
        bad_type(self, 0, "cdr")


    def stringp(self):
        return scheme_false

    def symbolp(self):
        return scheme_false

    def numberp(self):
        return scheme_false

    def integerp(self):
        return scheme_false

    def evaluate_arguments(self, arg_list, env):
        """Evaluate the expressions in ARG_LIST in ENV to produce
        arguments for this procedure. Returns an iterable of the results."""
        msg = "attempt to call something of non-function type ({0})"
        raise SchemeError(msg.format(type(self).__name__))

    def apply(self, args, env):
        """Apply me to a Scheme list of ARGS in environment ENV. Returns
        either
          A. A tuple (val, None), where val is the value this procedure
             returns when given ARGS and called in environment ENV, or
          B. A tuple (expr1, env1), where evaluating the Scheme
             expression expr1 in environment env1 will yield the same result
             and the same effects as evaluating ARGS in ENV.
        This method is overridden in procedure types.  THis default
        implementation causes an error.
        NOTE: Until you complete extra-credit question 22, this method
        will always return (val, None)."""
        msg = "attempt to call something of non-function type ({0})"
        raise SchemeError(msg.format(type(self).__name__))

    def get_actual_value(self):
        """Returns any desired transformation of a value newly fetched
        from a symbol before it is used. The default implementation
        is simply the identity.  [This method is useful for the call-by-name
        extension in extra-credit Problem 23.]""" 
        return self

def scheme_coerce(x):
    """Returns the Scheme value corresponding to X.  Converts numbers to
    SchemeNumbers and strings to interned symbols.  SchemeValues are unchanged.
    Other values raise a TypeError."""
    if isinstance(x, SchemeValue):
        return x
    elif isinstance(x, numbers.Number):
        return scnum(x)
    elif isinstance(x, str):
        return intern(x)
    else:
        raise TypeError("cannot convert type {} to SchemeValue".format(type(x)))

########
# okay #
########

class okay(SchemeValue):
    """Signifies an undefined value."""
    def __repr__(self):
        return "okay"

okay = okay() # Assignment hides the okay class; there is only one instance

############
# Booleans #
############

class scheme_true(SchemeValue):
    def booleanp(self):
        return scheme_true

    def __repr__(self):
        return 'scheme_true'

    def __str__(self):
        return "#t"

class scheme_false(SchemeValue):
    def __bool__(self):
        return False

    def booleanp(self):
        return scheme_true

    def __repr__(self):
        return 'scheme_false'

    def __str__(self):
        return "#f"

# scheme_true and scheme_false hide the classes scheme_true and scheme_false.
# Thus they are the only instances of those classes.

scheme_true = scheme_true()
scheme_false = scheme_false()

def scbool(x):
    """The Scheme boolean value (#t or #f) that corresponds to the Python value
    X.  True Python values yield scheme_true, and false values yield
    scheme_false."""
    return scheme_true if x else scheme_false

###########
# Numbers #
###########

def _check_num(x, name):
    """If X is a number, return it.  Otherwise, indicate a type error in
    argument 1 of operation NAME."""
    return check_type(x, scheme_numberp, 1, name)

class SchemeNumber(SchemeValue):
    """The parent class of all Scheme numeric types."""
    
    def numberp(self):
        return scheme_true

    def __repr__(self):
        return "scnum({})".format(self)

    # Tests 

    def eq(self, y):
        return scbool(self == _check_num(y, "="))

    def ltp(self, y):
        return scbool(self < _check_num(y, "<"))

    def gtp(self, y):
        return scbool(self > _check_num(y, ">"))

    def lep(self, y):
        return scbool(self <= _check_num(y, "<="))

    def gep(self, y):
        return scbool(self >= _check_num(y, ">="))

    def zerop(self):
        return scbool(self == 0)


# Types SchemeInt and SchemeFloat illustrate *multiple inheritance*.
# That is, they inherits methods from both SchemeValue and int or float.
# Thus, SchemeInts print as integers, and respond to all the
# same operators (+, -, etc.) as integers.  To convert an ordinary Python
# integer, x, into a SchemeInt, use SchemeInt(x); likewise for SchemeFloat.

class SchemeInt(SchemeNumber, int):
    def integerp(self):
        return scheme_true

    def neg(self):
        return SchemeInt(-self)

    # Scheme quotient rounds toward 0; Pythons rounds toward negative infinity.
    def quo(self, y):
        check_type(y, scheme_integerp, 1, "quotient")
        try:
            if (y < 0) != (self < 0):
                return SchemeInt(- (abs(self) // abs(y)))
            else:
                return SchemeInt(self // y)
        except ZeroDivisionError as err:
            raise SchemeError(err)

    def modulo(self, y):
        check_type(y, scheme_integerp, 1, "modulo")
        try:
            return SchemeInt(self % y)
        except ZeroDivisionError as err:
            raise SchemeError(err)

    def rem(self, y):
        q = self.quo(y)
        return SchemeInt(self - q * y)

    def floor(self):
        return self

    def ceil(self):
        return self

    def eqvp(self, y):
        return scbool(self == y)
  
    def evenp(self):
        return scbool(self % 2 == 0)

    def oddp(self):
        return scbool(self % 2 == 1)

class SchemeFloat(SchemeNumber, float):
    def neg(self):
        return SchemeFloat(-self)

    def floor(self):
        return SchemeInt(int(math.floor(self)))

    def ceil(self):
        return SchemeInt(int(math.ceil(self)))

    def eqvp(self, y):
        return scbool(self == y)

# Shorthand for numeric types.

scint = SchemeInt
scfloat = SchemeFloat

def scnum(num):
    r = round(num)
    if r == num:
        return scint(r)
    else:
        return scfloat(num)

###########
# Symbols #
###########

class SchemeSymbol(SchemeValue):
    """Represents a Scheme symbol.  Normally, one creates new symbols with
    the static intern factory method.  Each distinct symbol name is associated
    with exactly one symbol.  Symbol equality is simply object identity, so
    that SchemeSymbols are hashable (so may be used as dictionary keys and
    in sets)."""

    def __init__(self, name):
        """A new symbol whose name is NAME. Normally, you should create new
        symbols with intern (below).  This function is for internal use."""
        assert type(name) is str, \
               "invalid type of symbol name: {}".format(type(name))
        self.name = name

    def symbolp(self):
        return scheme_true

    def __repr__(self):
        if self is _all_symbols.get(self.name, None):
            return "intern('{}')".format(self.name)
        else:
            return "SchemeSymbol('{}')".format(self.name)

    def __str__(self):
        return self.name

# The symbols corresponding to each unique symbol name.
_all_symbols = {}

def intern(name):
    """If NAME is a string, the canonical symbol named NAME.  If NAME is a
    symbol, a canonical symbol with that name."""
    if isinstance(name, SchemeSymbol):
        if str(name) in _all_symbols:
            return _all_symbols[str(name)]
        else:
            _all_symbols[str(name)] = name
            return name
    if name in _all_symbols:
        return _all_symbols[name]
    else:
        sym = SchemeSymbol(name)
        _all_symbols[name] = sym
        return sym

###########
# Strings #
###########

class SchemeStr(SchemeValue, str):
    def stringp(self):
        return scheme_true

    def __repr__(self):
        return "scstr({!r})".format(str(self))

    _escape = re.compile(r'''"|\.''')

    def print_repr(self):
        s = str.__repr__(self)
        if s[0] == "'":
            s = s[1:-1]
            s = SchemeStr._escape.sub(lambda x: (r'\"' if x == '"' 
                                                 else "'" if x == r"\'"
                                                 else x), s)
            s = '"' + s + '"'
        return s

scstr = SchemeStr

##########################
# Pairs and Scheme lists #
##########################

class Pair(SchemeValue):
    """A pair has two instance attributes: first and second.  For a Pair to be
    a well-formed list, second is either a well-formed list or nil.  Some
    methods only apply to well-formed lists.  As a convenience, the constructor
    for Pair converts arguments that are numbers into SchemeNumbers and
    arguments that are strings into SchemeStrs (NOT symbols, which the caller
    must convert explictly, generally using intern).  Likewise, the __repr__
    function will abbreviate scnum(x) to x and scstr(x) to x.

    >>> s = Pair(1, Pair(2, nil))
    >>> s
    Pair(1, Pair(2, nil))
    >>> print(s)
    (1 2)
    >>> len(s)
    2
    >>> s[1]
    scnum(2)
    >>> print(s.map(lambda x: x+4))
    (5 6)
    """
    def __init__(self, first, second):
        """The pair (FIRST . SECOND).  As a convenience, FIRST and SECOND
        are coerced from Python numbers to SchemeNumbers or from Python
        strings to SchemeStrs."""
        first = scheme_coerce(first)
        second = scheme_coerce(second)

        assert isinstance(first, SchemeValue) and \
               isinstance(second, SchemeValue), \
            "bad types to Pair: {}, {}".format(type(first), type(second))
            
        self.first = first
        self.second = second

    def atomp(self):
        return scheme_false

    def pairp(self):
        return scheme_true

    def car(self):
        return self.first

    def cdr(self):
        return self.second

    def set_car(self, v):
        self.first = v
        return okay

    def set_cdr(self, v):
        self.second = v
        return okay

    def length(self):
        return SchemeInt(self.__len__())

    def equalp(self, y):
        return scbool(self == y)

    def listp(self):
        return self._list_end().nullp()

    def _list_end(self):
        """The 'end' of the list of which I am the head.  This is nil if
        I am a normal list.  If I am a dot list---e.g. (1 2 . 3)---, then
        the atom after the dot.  If the list is circular, then the first
        repeated pair in the list."""
        p0 = self
        p1 = self.second
        while p1 is not p0 and p1.pairp():
            p1 = p1.second
            if p1 is p0 or not p1.pairp():
                break
            p0 = p0.second
        return p1

    def __repr__(self):
        def uncoerce(x):
            if scheme_numberp(x):
                return x + 0
            elif scheme_symbolp(x):
                return str(x)
            else:
                return x
        return "Pair({0!r}, {1!r})".format(uncoerce(self.first),
                                           uncoerce(self.second))

    def __str__(self):
        s = "(" + str(self.first)
        second = self.second
        while second.pairp():
            s += " " + str(second.car())
            second = second.cdr()
        if not second.nullp():
            s += " . " + str(second)
        return s + ")"

    def __len__(self):
        if not self._list_end().nullp():
            raise SchemeError("length attempted on improper list")
        n, second = 1, self.second
        while second.pairp():
            n += 1
            second = second.second
        return n

    def __getitem__(self, k):
        if k < 0:
            raise IndexError("negative index into list")
        y = self
        for _ in range(k):
            if y.second is nil:
                raise IndexError("list index out of bounds")
            elif not isinstance(y.second, Pair):
                raise SchemeError("ill-formed list")
            y = y.second
        return y.first

    def __eq__(self, p):
        if not isinstance(p, Pair):
            return False
        return bool(self.first.equalp(p.first) and self.second.equalp(p.second))

    def map(self, fn):
        """Return a Scheme list after mapping Python function FN to SELF."""
        mapped = fn(self.first)
        if self.second.nullp() or self.second.pairp():
            return Pair(mapped, self.second.map(fn))
        else:
            raise SchemeError("ill-formed list")

    def append(self, y):
        if not self.listp():
            raise SchemeError("attempt to append to improper list")
        result = last = Pair(self.first, y)
        p = self.second
        while p is not nil:
            last.second = Pair(p.first, y)
            last = last.second
            p = p.second
        return result

class nil(SchemeValue):
    """The empty list"""

    def listp(self):
        return scheme_true

    def nullp(self):
        return scheme_true

    def length(self):
        return SchemeInt(0)

    def __repr__(self):
        return "nil"

    def __str__(self):
        return "()"

    def __len__(self):
        return 0

    def __getitem__(self, k):
        if k < 0:
            raise IndexError("negative index into list")
        raise IndexError("list index out of bounds")

    def append(self, y):
        return y

    def map(self, fn):
        return self

nil = nil() # Assignment hides the nil class; there is only one instance

########################
# Primitive Operations #
########################

_PRIMITIVES = []

def primitive(*names):
    """An annotation to record a Python function as a primitive procedure.
    NAMES is the set of names to use in the Scheme global environment for
    the function."""
    def add(fn):
        _PRIMITIVES.append((names, fn))
        return fn
    return add

def get_primitive_bindings():
    """The list of all (names, function) bindings recorded by @primitive
    annotations."""
    return _PRIMITIVES

@primitive("boolean?")
def scheme_booleanp(x):
    """True iff X is #t or #f."""
    return x.booleanp()

@primitive("not")
def scheme_not(x):
    """True iff X is #f."""
    return x.notp()

@primitive("eq?")
def scheme_eqp(x, y):
    return x.eqp(y)

@primitive("eqv?")
def scheme_eqvp(x, y):
    return x.eqvp(y)

@primitive("equal?")
def scheme_equalp(x, y):
    return x.equalp(y)

@primitive("pair?")
def scheme_pairp(x):
    return x.pairp()

@primitive("null?")
def scheme_nullp(x):
    return x.nullp()

@primitive("list?")
def scheme_listp(x):
    return x.listp()

@primitive("length")
def scheme_length(x):
    return x.length()

@primitive("cons")
def scheme_cons(x, y):
    return x.cons(y)

@primitive("car")
def scheme_car(x):
    return x.car()

@primitive("cdr")
def scheme_cdr(x):
    return x.cdr()


@primitive("list")
def scheme_list(*vals):
    result = nil
    for i in range(len(vals)-1, -1, -1):
        result = scheme_cons(vals[i], result)
    return result

@primitive("append")
def scheme_append(*vals):
    if len(vals) == 0:
        return nil
    result = vals[-1]
    for i in range(len(vals)-2, -1, -1):
        result = vals[i].append(result)
    return result

@primitive("string?")
def scheme_stringp(x):
    return x.stringp()

@primitive("symbol?")
def scheme_symbolp(x):
    return x.symbolp()

@primitive("number?")
def scheme_numberp(x):
    return x.numberp()

@primitive("integer?")
def scheme_integerp(x):
    return x.integerp()

def _check_nums(*vals):
    """Check that all arguments in VALS are numbers."""
    for i, v in enumerate(vals):
        if not scheme_numberp(v):
            msg = "operand {0} ({1}) is not a number"
            raise SchemeError(msg.format(i, v))

def _arith(fn, init, vals):
    """Perform the fn operation on the number values of VALS, with INIT as
    the value when VALS is empty. Returns the result as a Scheme value."""
    _check_nums(*vals)
    s = init
    for val in vals:
        s = fn(s, val)
    if round(s) == s:
        return SchemeInt(round(s))
    else:
        return SchemeFloat(s)

@primitive("+")
def scheme_add(*vals):
    return _arith(operator.add, 0, vals)

@primitive("-")
def scheme_sub(val0, *vals):
    if len(vals) == 0:
        return val0.neg()
    return _arith(operator.sub, val0, vals)

@primitive("*")
def scheme_mul(*vals):
    return _arith(operator.mul, 1, vals)

@primitive("/")
def scheme_div(*vals):
    try:
        if len(vals) == 1:
            return _arith(operator.truediv, scnum(1), vals)
        elif len(vals) == 0:
            raise SchemeError("/ takes at least one argument")
        return _arith(operator.truediv, vals[0], vals[1:])
    except ZeroDivisionError as err:
        raise SchemeError(err)

@primitive("quotient")
def scheme_quo(val0, val1):
    return val0.quo(val1)

@primitive("modulo")
def scheme_modulo(val0, val1):
    return val0.modulo(val1)

@primitive("remainder")
def scheme_rem(val0, val1):
    return val0.rem(val1)

@primitive("floor")
def scheme_floor(val):
    return val.floor()

@primitive("ceil")
def scheme_ceil(val):
    return val.ceil()

@primitive("=")
def scheme_eq(x, y):
    return x.eq(y)

@primitive("<")
def scheme_lt(x, y):
    return x.ltp(y)

@primitive(">")
def scheme_gt(x, y):
    return x.gtp(y)

@primitive("<=")
def scheme_le(x, y):
    return x.lep(y)

@primitive(">=")
def scheme_ge(x, y):
    return x.gep(y)

@primitive("even?")
def scheme_evenp(x):
    return x.evenp()

@primitive("odd?")
def scheme_oddp(x):
    return x.oddp()

@primitive("zero?")
def scheme_zerop(x):
    return x.zerop()

##
## Other operations
##

# atom? is not standard.
@primitive("atom?")
def scheme_atomp(x):
    return x.atomp()

@primitive("display")
def scheme_display(val):
    print(str(val), end="")
    return okay

@primitive("print")
def scheme_print(val):
    print(val.print_repr())
    return okay

@primitive("newline")
def scheme_newline():
    print()
    sys.stdout.flush()
    return okay

@primitive("error")
def scheme_error(msg = None):
    msg = "" if msg is None else str(msg)
    raise SchemeError(msg)

@primitive("exit")
def scheme_exit():
    raise EOFError

##
## Turtle graphics (non-standard)
##

_turtle_screen_on = False

def turtle_screen_on():
    return _turtle_screen_on

def _tscheme_prep():
    global _turtle_screen_on
    if not _turtle_screen_on:
        _turtle_screen_on = True
        turtle.title("Scheme Turtles")
        turtle.mode('logo')

@primitive("forward", "fd")
def tscheme_forward(n):
    """Move the turtle forward a distance N units on the current heading."""
    _check_nums(n)
    _tscheme_prep()
    turtle.forward(n)
    return okay

@primitive("backward", "back", "bk")
def tscheme_backward(n):
    """Move the turtle backward a distance N units on the current heading,
    without changing direction."""
    _check_nums(n)
    _tscheme_prep()
    turtle.backward(n)
    return okay

@primitive("left", "lt")
def tscheme_left(n):
    """Rotate the turtle's heading N degrees counterclockwise."""
    _check_nums(n)
    _tscheme_prep()
    turtle.left(n)
    return okay

@primitive("right", "rt")
def tscheme_right(n):
    """Rotate the turtle's heading N degrees clockwise."""
    _check_nums(n)
    _tscheme_prep()
    turtle.right(n)
    return okay

@primitive("circle")
def tscheme_circle(r, extent = None):
    """Draw a circle with center R units to the left of the turtle (i.e.,
    right if N is negative.  If EXTENT is not None, then draw EXTENT degrees
    of the circle only.  Draws in the clockwise direction if R is negative,
    and otherwise counterclockwise, leaving the turtle facing along the
    arc at its end."""
    if extent is None:
        _check_nums(r)
    else:
        _check_nums(r, extent)
    _tscheme_prep()
    turtle.circle(r, extent and extent)
    return okay

@primitive("setposition", "setpos", "goto")
def tscheme_setposition(x, y):
    """Set turtle's position to (X,Y), heading unchanged."""
    _check_nums(x, y)
    _tscheme_prep()
    turtle.setposition(x, y)
    return okay

@primitive("setheading", "seth")
def tscheme_setheading(h):
    """Set the turtle's heading H degrees clockwise from north (up)."""
    _check_nums(h)
    _tscheme_prep()
    turtle.setheading(h)
    return okay

@primitive("penup", "pu")
def tscheme_penup():
    """Raise the pen, so that the turtle does not draw."""
    _tscheme_prep()
    turtle.penup()
    return okay

@primitive("pendown", "pd")
def tscheme_pendown():
    """Lower the pen, so that the turtle starts drawing."""
    _tscheme_prep()
    turtle.pendown()
    return okay

@primitive("showturtle", "st")
def tscheme_showturtle():
    """Make turtle visible."""
    _tscheme_prep()
    turtle.showturtle()
    return okay

@primitive("hideturtle", "ht")
def tscheme_hideturtle():
    """Make turtle visible."""
    _tscheme_prep()
    turtle.hideturtle()
    return okay

@primitive("clear")
def tscheme_clear():
    """Clear the drawing, leaving the turtle unchanged."""
    _tscheme_prep()
    turtle.clear()
    return okay

@primitive("color")
def tscheme_color(c):
    """Set the color to C, a string such as '"red"' or '"#ffc0c0"' (representing
    hexadecimal red, green, and blue values."""
    _tscheme_prep()
    check_type(c, scheme_stringp, 0, "color")
    turtle.color(eval(c))
    return okay

@primitive("begin_fill")
def tscheme_begin_fill():
    """Start a sequence of moves that outline a shape to be filled."""
    _tscheme_prep()
    turtle.begin_fill()
    return okay

@primitive("end_fill")
def tscheme_end_fill():
    """Fill in shape drawn since last begin_fill."""
    _tscheme_prep()
    turtle.end_fill()
    return okay

@primitive("exitonclick")
def tscheme_exitonclick():
    """Wait for a click on the turtle window, and then close it."""
    global _turtle_screen_on
    if _turtle_screen_on:
        print("Close or click on turtle window to complete exit")
        turtle.exitonclick()
        _turtle_screen_on = False
    return okay

@primitive("speed")
def tscheme_speed(s):
    """Set the turtle's animation speed as indicated by S (an integer in
    0-10, with 0 indicating no animation (lines draw instantly), and 1-10
    indicating faster and faster movement."""
    check_type(s, scheme_integerp, 0, "speed")
    _tscheme_prep()
    turtle.speed(s)
    return okay
